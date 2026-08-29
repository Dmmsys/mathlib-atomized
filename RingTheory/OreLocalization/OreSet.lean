/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.GroupTheory.OreLocalization.OreSet

/-!

# (Left) Ore sets and rings

This file contains results on left Ore sets for rings and monoids with zero.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

@[expose] public section

assert_not_exists RelIso

namespace OreLocalization

/-- Cancellability in monoids with zeros can act as a replacement for the `ore_right_cancel`
condition of an ore set. -/
@[instance_reducible]
/--
Definition of `oreSetOfIsCancelMulZero` / `oreSetOfIsCancelMulZero` 的定义

English:
definition oreSetOfIsCancelMulZero
  signature: {R : Type*} [MonoidWithZero R] [IsCancelMulZero R]
  body: { ore_right_cancel := fun _ _ s h => ⟨s, mul_eq_mul_left_iff.mpr (mul_eq_mul_right_iff.mp h)⟩
    oreNum
    oreDenom
    ore_eq }

@[deprecated (since := "2026-01-12")] alias oreSetOfCancelMonoidWithZero := oreSetOfIsCancelMulZero

中文:
定义 oreSetOfIsCancelMulZero
  签名: {R : 类型} [带零幺半群 R] [是乘零消去 R]
  定义体: { ore_right_cancel := fun _ _ s h => ⟨s, mul_eq_mul_left_iff.mpr (mul_eq_mul_right_iff.mp h)⟩
    oreNum
    oreDenom
    ore_eq }

@[deprecated (since := "2026-01-12")] alias oreSetOfCancelMonoidWithZero := oreSetOfIsCancelMulZero

Depends on / 依赖: mul_eq_mul_left_iff, mul_eq_mul_left_iff.mpr, mul_eq_mul_right_iff, mul_eq_mul_right_iff.mp, oreDenom, oreNum, ore_eq, ore_right_cancel
-/
def oreSetOfIsCancelMulZero {R : Type*} [MonoidWithZero R] [IsCancelMulZero R]
    {S : Submonoid R} (oreNum : R -> S -> R) (oreDenom : R -> S -> S)
    (ore_eq : forall (r : R) (s : S), oreDenom r s * r = oreNum r s * s) : OreSet S :=
  { ore_right_cancel := fun _ _ s h => ⟨s, mul_eq_mul_left_iff.mpr (mul_eq_mul_right_iff.mp h)⟩
    oreNum
    oreDenom
    ore_eq }

@[deprecated (since := "2026-01-12")] alias oreSetOfCancelMonoidWithZero := oreSetOfIsCancelMulZero

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a proof for the Ore condition itself. -/
@[instance_reducible]
/--
Definition of `oreSetOfNoZeroDivisors` / `oreSetOfNoZeroDivisors` 的定义

English:
definition oreSetOfNoZeroDivisors
  signature: {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submonoid R}
  body: letI : IsCancelMulZero R := NoZeroDivisors.toIsCancelMulZero
  oreSetOfIsCancelMulZero oreNum oreDenom ore_eq

中文:
定义 oreSetOfNoZeroDivisors
  签名: {R : 类型} [环 R] [无零因子 R] {S : 子幺半群 R}
  定义体: letI : IsCancelMulZero R := NoZeroDivisors.toIsCancelMulZero
  oreSetOfIsCancelMulZero oreNum oreDenom ore_eq

Depends on / 依赖: IsCancelMulZero, NoZeroDivisors, NoZeroDivisors.toIsCancelMulZero, oreDenom, oreNum, oreSetOfIsCancelMulZero, ore_eq, toIsCancelMulZero
-/
def oreSetOfNoZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submonoid R}
    (oreNum : R -> S -> R) (oreDenom : R -> S -> S)
    (ore_eq : forall (r : R) (s : S), oreDenom r s * r = oreNum r s * s) : OreSet S :=
  letI : IsCancelMulZero R := NoZeroDivisors.toIsCancelMulZero
  oreSetOfIsCancelMulZero oreNum oreDenom ore_eq

/--
lemma `nonempty_oreSet_iff` / 引理 `nonempty_oreSet_iff`

English:
lemma nonempty_oreSet_iff
  given: {R : Type*} [Monoid R] {S : Submonoid R}
  proof: by
  constructor
  · exact fun ⟨_⟩ => ⟨ore_right_cancel, fun r s => ⟨oreNum r s, oreDenom r s, ore_eq r s⟩⟩
  · intro ⟨H, H'⟩
    choose r' s' h using H'
    exact ⟨H, r', s', h⟩

中文:
引理 nonempty_oreSet_iff
  条件: {R : 类型} [幺半群 R] {S : 子幺半群 R}
  证明: by
  constructor
  · exact fun ⟨_⟩ => ⟨ore_right_cancel, fun r s => ⟨oreNum r s, oreDenom r s, ore_eq r s⟩⟩
  · intro ⟨H, H'⟩
    choose r' s' h using H'
    exact ⟨H, r', s', h⟩

Depends on / 依赖: oreDenom, oreNum, ore_eq, ore_right_cancel
-/
lemma nonempty_oreSet_iff {R : Type*} [Monoid R] {S : Submonoid R} :
    Nonempty (OreSet S) ↔ (forall (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s -> exists s' : S, s' * r₁ = s' * r₂) ∧
      (forall (r : R) (s : S), exists (r' : R) (s' : S), s' * r = r' * s) := by
  constructor
  · exact fun ⟨_⟩ => ⟨ore_right_cancel, fun r s => ⟨oreNum r s, oreDenom r s, ore_eq r s⟩⟩
  · intro ⟨H, H'⟩
    choose r' s' h using H'
    exact ⟨H, r', s', h⟩

/--
lemma `nonempty_oreSet_iff_of_noZeroDivisors` / 引理 `nonempty_oreSet_iff_of_noZeroDivisors`

English:
lemma nonempty_oreSet_iff_of_noZeroDivisors
  statement: {R : Type*} [Ring R] [NoZeroDivisors R]
  proof: by
  constructor
  · exact fun ⟨_⟩ => fun r s => ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
  · intro H
    choose r' s' h using H
    exact ⟨oreSetOfNoZeroDivisors r' s' h⟩

中文:
引理 nonempty_oreSet_iff_of_noZeroDivisors
  结论: {R : 类型} [环 R] [无零因子 R]
  证明: by
  constructor
  · exact fun ⟨_⟩ => fun r s => ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
  · intro H
    choose r' s' h using H
    exact ⟨oreSetOfNoZeroDivisors r' s' h⟩

Depends on / 依赖: oreDenom, oreNum, oreSetOfNoZeroDivisors, ore_eq
-/
lemma nonempty_oreSet_iff_of_noZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R]
    {S : Submonoid R} :
    Nonempty (OreSet S) ↔ forall (r : R) (s : S), exists (r' : R) (s' : S), s' * r = r' * s := by
  constructor
  · exact fun ⟨_⟩ => fun r s => ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
  · intro H
    choose r' s' h using H
    exact ⟨oreSetOfNoZeroDivisors r' s' h⟩

end OreLocalization
