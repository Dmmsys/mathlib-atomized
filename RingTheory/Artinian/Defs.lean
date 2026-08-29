/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Artinian rings and modules

A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsArtinian R M` is the proposition that `M` is an Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.
* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

public section

/--
Definition of `IsArtinian` / `IsArtinian` 的定义

English:
abbreviation IsArtinian
  signature: (R M) [Semiring R] [AddCommMonoid M] [Module R M]
  body: WellFoundedLT (Submodule R M)

中文:
缩写 是Artin
  签名: (R M) [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: WellFoundedLT (Submodule R M)

Depends on / 依赖: Submodule, WellFoundedLT
-/
abbrev IsArtinian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  WellFoundedLT (Submodule R M)

/--
theorem `isArtinian_iff` / 定理 `isArtinian_iff`

English:
theorem isArtinian_iff
  given: (R M) [Semiring R] [AddCommMonoid M] [Module R M]
  statement: IsArtinian R M ↔
  proof: isWellFounded_iff _ _

中文:
定理 isArtinian_iff
  条件: (R M) [半环 R] [加法交换幺半群 M] [模 R M]
  结论: 是Artin R M ↔
  证明: isWellFounded_iff _ _

Depends on / 依赖: isWellFounded_iff
-/
theorem isArtinian_iff (R M) [Semiring R] [AddCommMonoid M] [Module R M] : IsArtinian R M ↔
    WellFounded (· < · : Submodule R M -> Submodule R M -> Prop) :=
  isWellFounded_iff _ _

/--
theorem `IsArtinian.induction` / 定理 `IsArtinian.induction`

English:
theorem IsArtinian.induction
  statement: {R M} [Semiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]
  proof: WellFoundedLT.induction I hgt

中文:
定理 是Artin.induction
  结论: {R M} [半环 R] [加法交换幺半群 M] [模 R M] [是Artin R M]
  证明: WellFoundedLT.induction I hgt

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction
-/
theorem IsArtinian.induction {R M} [Semiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]
    {P : Submodule R M -> Prop} (hgt : forall I, (forall J < I, P J) -> P I) (I : Submodule R M) : P I :=
  WellFoundedLT.induction I hgt

-- See `Mathlib/RingTheory/Artinian/Ring.lean`
assert_not_exists IsLocalization IsLocalRing

/-- A ring is Artinian if it is Artinian as a module over itself.

Strictly speaking, this should be called `IsLeftArtinianRing` but we omit the `Left` for
convenience in the commutative case. For a right Artinian ring, use `IsArtinian Rᵐᵒᵖ R`.

For equivalent definitions, see `Mathlib/RingTheory/Artinian/Ring.lean`.
-/
@[stacks 00J5]
/--
Definition of `IsArtinianRing` / `IsArtinianRing` 的定义

English:
abbreviation IsArtinianRing
  signature: (R) [Semiring R]
  body: IsArtinian R R

中文:
缩写 是Artin环
  签名: (R) [半环 R]
  定义体: IsArtinian R R

Depends on / 依赖: IsArtinian
-/
abbrev IsArtinianRing (R) [Semiring R] :=
  IsArtinian R R

/--
theorem `isArtinianRing_iff` / 定理 `isArtinianRing_iff`

English:
theorem isArtinianRing_iff
  given: {R} [Semiring R]
  statement: IsArtinianRing R ↔ IsArtinian R R
  proof: Iff.rfl

中文:
定理 isArtinianRing_iff
  条件: {R} [半环 R]
  结论: 是Artin环 R ↔ 是Artin R R
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isArtinianRing_iff {R} [Semiring R] : IsArtinianRing R ↔ IsArtinian R R := Iff.rfl
