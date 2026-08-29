/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Euclidean absolute values

This file defines a predicate `AbsoluteValue.IsEuclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

* `AbsoluteValue.IsEuclidean abv` is a predicate on absolute values on `R` mapping to `S`
  that preserve the order on `R` arising from the Euclidean domain structure.
* `AbsoluteValue.abs_isEuclidean` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is Euclidean.
-/

public section

@[inherit_doc]
local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

section OrderedSemiring

variable {R S : Type*} [EuclideanDomain R] [Semiring S] [PartialOrder S]
variable (abv : AbsoluteValue R S)

/--
Definition of `IsEuclidean` / `IsEuclidean` 的定义

English:
structure IsEuclidean
  parameters: : Prop where
  axioms and operations (1):
    - map_lt_map_iff' : forall {x y}, abv x < abv y ↔ x ≺ y

中文:
结构 IsEuclidean
  参数: : 命题 where
  公理与运算 (1 个):
    - map_lt_map_iff' : 对任意 {x y}, abv x < abv y ↔ x ≺ y
-/
structure IsEuclidean : Prop where
  /-- The requirement of a Euclidean absolute value
  that `abv` is monotone with respect to `≺` -/
  map_lt_map_iff' : forall {x y}, abv x < abv y ↔ x ≺ y

namespace IsEuclidean

variable {abv}

-- Rearrange the parameters to `map_lt_map_iff'` so it elaborates better.
/--
theorem `map_lt_map_iff` / 定理 `map_lt_map_iff`

English:
theorem map_lt_map_iff
  given: {x y : R} (h : abv.IsEuclidean)
  statement: abv x < abv y ↔ x ≺ y
  proof: map_lt_map_iff' h

中文:
定理 map_lt_map_iff
  条件: {x y : R} (h : abv.IsEuclidean)
  结论: abv x < abv y ↔ x ≺ y
  证明: map_lt_map_iff' h

Depends on / 依赖: map_lt_map_iff
-/
theorem map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y :=
  map_lt_map_iff' h

attribute [simp] map_lt_map_iff

/--
theorem `sub_mod_lt` / 定理 `sub_mod_lt`

English:
theorem sub_mod_lt
  given: (h : abv.IsEuclidean) (a : R) {b : R} (hb : b != 0)
  statement: abv (a % b) < abv b
  proof: h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)

中文:
定理 sub_mod_lt
  条件: (h : abv.IsEuclidean) (a : R) {b : R} (hb : b != 0)
  结论: abv (a % b) < abv b
  证明: h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mod_lt, h.map_lt_map_iff.mpr, map_lt_map_iff, mod_lt
-/
theorem sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b != 0) : abv (a % b) < abv b :=
  h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)

end IsEuclidean

end OrderedSemiring

section Int

open Int

-- TODO: generalize to `LinearOrderedEuclideanDomain`s if we ever get a definition of those
/--
theorem `abs_isEuclidean` / 定理 `abs_isEuclidean`

English:
theorem abs_isEuclidean
  statement: IsEuclidean (AbsoluteValue.abs : AbsoluteValue Int Int)
  proof: { map_lt_map_iff' := fun {x y} =>
       show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_natAbs, abs_eq_natAbs, ofNat_lt] }

中文:
定理 abs_isEuclidean
  结论: IsEuclidean (AbsoluteValue.abs : AbsoluteValue 整数 整数)
  证明: { map_lt_map_iff' := fun {x y} =>
       show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_natAbs, abs_eq_natAbs, ofNat_lt] }
-/
protected theorem abs_isEuclidean : IsEuclidean (AbsoluteValue.abs : AbsoluteValue Int Int) :=
  { map_lt_map_iff' := fun {x y} =>
       show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_natAbs, abs_eq_natAbs, ofNat_lt] }

end Int

end AbsoluteValue
