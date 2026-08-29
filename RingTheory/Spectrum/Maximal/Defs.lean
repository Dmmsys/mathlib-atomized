/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Maximal spectrum of a commutative (semi)ring

The maximal spectrum of a commutative (semi)ring is the type of all maximal ideals.
It is naturally a subset of the prime spectrum endowed with the subspace topology.

## Main definitions

* `MaximalSpectrum R`: The maximal spectrum of a commutative (semi)ring `R`,
  i.e., the set of all maximal ideals of `R`.
-/

public section

/-- The maximal spectrum of a commutative (semi)ring `R` is the type of all
maximal ideals of `R`. -/
@[ext]
/--
Definition of `MaximalSpectrum` / `MaximalSpectrum` 的定义

English:
structure MaximalSpectrum
  parameters: (R : Type*) [CommSemiring R]
  axioms and operations (2):
    - asIdeal : Ideal R
    - isMaximal : asIdeal.IsMaximal

中文:
结构 MaximalSpectrum
  参数: (R : 类型) [CommSemiring R]
  公理与运算 (2 个):
    - asIdeal : Ideal R
    - isMaximal : asIdeal.IsMaximal
-/
structure MaximalSpectrum (R : Type*) [CommSemiring R] where
  asIdeal : Ideal R
  isMaximal : asIdeal.IsMaximal

attribute [instance] MaximalSpectrum.isMaximal

instance (R : Type*) [CommSemiring R] : Coe (MaximalSpectrum R) (Ideal R) where
  coe P := P.asIdeal
