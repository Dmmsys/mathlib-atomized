/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Facts about `algebraMap` when the coefficient ring is a field.
-/

public section

namespace algebraMap

universe u v w u₁ v₁

section SemifieldSemidivisionRing

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (r : R)
  statement: ↑r⁻¹ = ((↑r)⁻¹ : A)
  proof: map_inv₀ (algebraMap R A) r

@[norm_cast]

中文:
定理 coe_inv
  条件: (r : R)
  结论: ↑r⁻¹ = ((↑r)⁻¹ : A)
  证明: map_inv₀ (algebraMap R A) r

@[norm_cast]

Depends on / 依赖: algebraMap
-/
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r

@[norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (r s : R)
  statement: ↑(r / s) = (↑r / ↑s : A)
  proof: map_div₀ (algebraMap R A) r s

@[norm_cast]

中文:
定理 coe_div
  条件: (r s : R)
  结论: ↑(r / s) = (↑r / ↑s : A)
  证明: map_div₀ (algebraMap R A) r s

@[norm_cast]

Depends on / 依赖: algebraMap
-/
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s

@[norm_cast]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (r : R) (z : Int)
  statement: ↑(r ^ z) = (r : A) ^ z
  proof: map_zpow₀ (algebraMap R A) r z

中文:
定理 coe_zpow
  条件: (r : R) (z : 整数)
  结论: ↑(r ^ z) = (r : A) ^ z
  证明: map_zpow₀ (algebraMap R A) r z

Depends on / 依赖: algebraMap
-/
theorem coe_zpow (r : R) (z : Int) : ↑(r ^ z) = (r : A) ^ z :=
  map_zpow₀ (algebraMap R A) r z

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]

@[norm_cast]
/--
theorem `coe_ratCast` / 定理 `coe_ratCast`

English:
theorem coe_ratCast
  given: (q : Rat)
  statement: ↑(q : R) = (q : A)
  proof: map_ratCast (algebraMap R A) q

中文:
定理 coe_ratCast
  条件: (q : 有理数)
  结论: ↑(q : R) = (q : A)
  证明: map_ratCast (algebraMap R A) q

Depends on / 依赖: algebraMap, map_ratCast
-/
theorem coe_ratCast (q : Rat) : ↑(q : R) = (q : A) := map_ratCast (algebraMap R A) q

end FieldDivisionRing

end algebraMap
