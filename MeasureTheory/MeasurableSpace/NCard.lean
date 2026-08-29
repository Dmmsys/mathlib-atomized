/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of `Set.encard` and `Set.ncard`

In this file we prove that `Set.encard` and `Set.ncard` are measurable functions,
provided that the ambient space is countable.
-/

public section

open Set

variable {α : Type*} [Countable α]

@[fun_prop]
/--
theorem `measurable_encard` / 定理 `measurable_encard`

English:
theorem measurable_encard
  statement: Measurable (Set.encard : Set α -> Nat∞)
  proof: ENat.measurable_iff.2 fun _n => Countable.measurableSet Countable.ofPred_finite.mono fun _s hs =>
    finite_of_encard_eq_coe hs

@[fun_prop]

中文:
定理 measurable_encard
  结论: Measurable (Set.encard : Set α -> 自然数∞)
  证明: ENat.measurable_iff.2 fun _n => Countable.measurableSet Countable.ofPred_finite.mono fun _s hs =>
    finite_of_encard_eq_coe hs

@[fun_prop]

Depends on / 依赖: Countable, Countable.measurableSet, Countable.ofPred_finite.mono, ENat.measurable_iff, finite_of_encard_eq_coe, measurableSet, measurable_iff, ofPred_finite
-/
theorem measurable_encard : Measurable (Set.encard : Set α -> Nat∞) :=
ENat.measurable_iff.2 fun _n => Countable.measurableSet Countable.ofPred_finite.mono fun _s hs =>
    finite_of_encard_eq_coe hs

@[fun_prop]
/--
theorem `measurable_ncard` / 定理 `measurable_ncard`

English:
theorem measurable_ncard
  statement: Measurable (Set.ncard : Set α -> Nat)
  proof: Measurable.of_discrete.comp measurable_encard

中文:
定理 measurable_ncard
  结论: Measurable (Set.ncard : Set α -> 自然数)
  证明: Measurable.of_discrete.comp measurable_encard

Depends on / 依赖: Measurable, Measurable.of_discrete.comp, measurable_encard, of_discrete
-/
theorem measurable_ncard : Measurable (Set.ncard : Set α -> Nat) :=
  Measurable.of_discrete.comp measurable_encard
