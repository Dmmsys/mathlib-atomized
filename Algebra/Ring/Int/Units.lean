/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Group.Int.Units

/-!
# Basic lemmas for `ℤˣ`.

This file contains lemmas on the units of `ℤ`.

## Main results

* `Int.units_eq_one_or`: the invertible integers are 1 and -1.

See note [foundational algebra order theory].
-/

public section

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int


/--
lemma `units_eq_one_or` / 引理 `units_eq_one_or`

English:
lemma units_eq_one_or
  given: (u : Intˣ)
  statement: u = 1 ∨ u = -1
  proof: by
  simpa only [Units.ext_iff] using! isUnit_eq_one_or u.isUnit

中文:
引理 units_eq_one_or
  条件: (u : 整数ˣ)
  结论: u = 1 ∨ u = -1
  证明: by
  simpa only [Units.ext_iff] using! isUnit_eq_one_or u.isUnit

Depends on / 依赖: Units.ext_iff, ext_iff, isUnit, isUnit_eq_one_or, u.isUnit
-/
lemma units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using! isUnit_eq_one_or u.isUnit

/--
lemma `units_ne_iff_eq_neg` / 引理 `units_ne_iff_eq_neg`

English:
lemma units_ne_iff_eq_neg
  given: {u v : Intˣ}
  statement: u != v ↔ u = -v
  proof: by
  simpa only [Ne, Units.ext_iff] using! isUnit_ne_iff_eq_neg u.isUnit v.isUnit

中文:
引理 units_ne_iff_eq_neg
  条件: {u v : 整数ˣ}
  结论: u != v ↔ u = -v
  证明: by
  simpa only [Ne, Units.ext_iff] using! isUnit_ne_iff_eq_neg u.isUnit v.isUnit

Depends on / 依赖: Units.ext_iff, ext_iff, isUnit, isUnit_ne_iff_eq_neg, u.isUnit, v.isUnit
-/
lemma units_ne_iff_eq_neg {u v : Intˣ} : u != v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using! isUnit_ne_iff_eq_neg u.isUnit v.isUnit

end Int
