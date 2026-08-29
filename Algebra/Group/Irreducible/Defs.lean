/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Basic

/-!
# Irreducible elements in a monoid

This file defines irreducible elements of a monoid (`Irreducible`), as non-units that can't be
written as the product of two non-units. This generalises irreducible elements of a ring.
We also define the additive variant (`AddIrreducible`).

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Prime`
(see `irreducible_iff_prime`), however this is not true in general.
-/

public section

assert_not_exists MonoidWithZero IsOrderedMonoid Multiset

variable {M : Type*}

/--
Definition of `AddIrreducible` / `AddIrreducible` 的定义

English:
structure AddIrreducible
  parameters: [AddMonoid M] (p : M)
  axioms and operations (2):
    - not_isAddUnit : ¬IsAddUnit p
    - isAddUnit_or_isAddUnit(⦃a b⦄) : p = a + b -> IsAddUnit a ∨ IsAddUnit b

中文:
结构 AddIrreducible
  参数: [AddMonoid M] (p : M)
  公理与运算 (2 个):
    - not_isAddUnit : ¬IsAddUnit p
    - isAddUnit_or_isAddUnit(⦃a b⦄) : p = a + b -> IsAddUnit a ∨ IsAddUnit b
-/
structure AddIrreducible [AddMonoid M] (p : M) : Prop where
  /-- An irreducible element is not an additive unit. -/
  not_isAddUnit : ¬IsAddUnit p
  /-- If an irreducible element can be written as a sum, then one term is an additive unit. -/
  isAddUnit_or_isAddUnit ⦃a b⦄ : p = a + b -> IsAddUnit a ∨ IsAddUnit b

section Monoid
variable [Monoid M] {p q a b : M}

/-- `Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements. -/
@[to_additive (attr := wikidata Q2989575)]
/--
Definition of `Irreducible` / `Irreducible` 的定义

English:
structure Irreducible
  parameters: (p : M)
  axioms and operations (2):
    - not_isUnit : ¬IsUnit p
    - isUnit_or_isUnit(⦃a b) : M⦄ : p = a * b -> IsUnit a ∨ IsUnit b

中文:
结构 Irreducible
  参数: (p : M)
  公理与运算 (2 个):
    - not_isUnit : ¬IsUnit p
    - isUnit_or_isUnit(⦃a b) : M⦄ : p = a * b -> IsUnit a ∨ IsUnit b
-/
structure Irreducible (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isUnit : ¬IsUnit p
  /-- If an irreducible element factors, then one factor is a unit. -/
  isUnit_or_isUnit ⦃a b : M⦄ : p = a * b -> IsUnit a ∨ IsUnit b

/--
lemma `irreducible_iff` / 引理 `irreducible_iff`

English:
lemma irreducible_iff
  proof: ⟨hp.not_isUnit, hp.isUnit_or_isUnit⟩
  mpr hp := ⟨hp.1, hp.2⟩

@[to_additive (attr := simp)]

中文:
引理 irreducible_iff
  证明: ⟨hp.not_isUnit, hp.isUnit_or_isUnit⟩
  mpr hp := ⟨hp.1, hp.2⟩

@[to_additive (attr := simp)]
-/
@[to_additive] lemma irreducible_iff :
    Irreducible p ↔ ¬IsUnit p ∧ forall ⦃a b⦄, p = a * b -> IsUnit a ∨ IsUnit b where
  mp hp := ⟨hp.not_isUnit, hp.isUnit_or_isUnit⟩
  mpr hp := ⟨hp.1, hp.2⟩

@[to_additive (attr := simp)]
/--
lemma `not_irreducible_one` / 引理 `not_irreducible_one`

English:
lemma not_irreducible_one
  statement: ¬Irreducible (1 : M)
  proof: by simp [irreducible_iff]

@[to_additive]

中文:
引理 not_irreducible_one
  结论: ¬Irreducible (1 : M)
  证明: by simp [irreducible_iff]

@[to_additive]

Depends on / 依赖: irreducible_iff
-/
lemma not_irreducible_one : ¬Irreducible (1 : M) := by simp [irreducible_iff]

@[to_additive]
/--
lemma `Irreducible.ne_one` / 引理 `Irreducible.ne_one`

English:
lemma Irreducible.ne_one
  given: (hp : Irreducible p)
  statement: p != 1
  proof: by rintro rfl; exact not_irreducible_one hp

@[to_additive]

中文:
引理 Irreducible.ne_one
  条件: (hp : Irreducible p)
  结论: p != 1
  证明: by rintro rfl; exact not_irreducible_one hp

@[to_additive]

Depends on / 依赖: not_irreducible_one
-/
lemma Irreducible.ne_one (hp : Irreducible p) : p != 1 := by rintro rfl; exact not_irreducible_one hp

@[to_additive]
/--
lemma `of_irreducible_mul` / 引理 `of_irreducible_mul`

English:
lemma of_irreducible_mul
  statement: Irreducible (a * b) -> IsUnit a ∨ IsUnit b | ⟨_, h⟩ => h rfl

中文:
引理 of_irreducible_mul
  结论: Irreducible (a * b) -> IsUnit a ∨ IsUnit b | ⟨_, h⟩ => h rfl
-/
lemma of_irreducible_mul : Irreducible (a * b) -> IsUnit a ∨ IsUnit b | ⟨_, h⟩ => h rfl

@[to_additive]
/--
lemma `irreducible_or_factor` / 引理 `irreducible_or_factor`

English:
lemma irreducible_or_factor
  given: (hp : ¬IsUnit p)
  proof: by
  simpa [irreducible_iff, hp, and_rotate] using em (forall a b, p = a * b -> IsUnit a ∨ IsUnit b)

@[to_additive]

中文:
引理 irreducible_or_factor
  条件: (hp : ¬IsUnit p)
  证明: by
  simpa [irreducible_iff, hp, and_rotate] using em (forall a b, p = a * b -> IsUnit a ∨ IsUnit b)

@[to_additive]

Depends on / 依赖: IsUnit, and_rotate, irreducible_iff
-/
lemma irreducible_or_factor (hp : ¬IsUnit p) :
    Irreducible p ∨ exists a b, ¬IsUnit a ∧ ¬IsUnit b ∧ p = a * b := by
  simpa [irreducible_iff, hp, and_rotate] using em (forall a b, p = a * b -> IsUnit a ∨ IsUnit b)

@[to_additive]
/--
lemma `Irreducible.eq_one_or_eq_one` / 引理 `Irreducible.eq_one_or_eq_one`

English:
lemma Irreducible.eq_one_or_eq_one
  given: [Subsingleton Mˣ] (hab : Irreducible (a * b))
  proof: by simpa using hab.isUnit_or_isUnit rfl

中文:
引理 Irreducible.eq_one_or_eq_one
  条件: [Subsingleton Mˣ] (hab : Irreducible (a * b))
  证明: by simpa using hab.isUnit_or_isUnit rfl

Depends on / 依赖: hab.isUnit_or_isUnit, isUnit_or_isUnit
-/
lemma Irreducible.eq_one_or_eq_one [Subsingleton Mˣ] (hab : Irreducible (a * b)) :
    a = 1 ∨ b = 1 := by simpa using hab.isUnit_or_isUnit rfl

end Monoid
