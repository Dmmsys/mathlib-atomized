/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Rat.Cast.Defs

/-!
# \*-ring structure on `ℚ` and `ℚ≥0`.
-/

public section

/--
Instance `Rat.instStarRing` / 实例 `Rat.instStarRing`

English:
instance Rat.instStarRing
  signature: : StarRing Rat
  body: starRingOfComm

中文:
实例 Rat.instStarRing
  签名: : StarRing Rat
  定义体: starRingOfComm

Depends on / 依赖: starRingOfComm
-/
instance Rat.instStarRing : StarRing Rat := starRingOfComm
/--
Instance `NNRat.instStarRing` / 实例 `NNRat.instStarRing`

English:
instance NNRat.instStarRing
  signature: : StarRing Rat>=0
  body: starRingOfComm

中文:
实例 NNRat.instStarRing
  签名: : StarRing Rat>=0
  定义体: starRingOfComm

Depends on / 依赖: starRingOfComm
-/
instance NNRat.instStarRing : StarRing Rat>=0 := starRingOfComm
/--
Instance `Rat.instTrivialStar` / 实例 `Rat.instTrivialStar`

English:
instance Rat.instTrivialStar
  signature: : TrivialStar Rat
  body: ⟨fun _ => rfl⟩

中文:
实例 Rat.instTrivialStar
  签名: : TrivialStar Rat
  定义体: ⟨fun _ => rfl⟩
-/
instance Rat.instTrivialStar : TrivialStar Rat := ⟨fun _ => rfl⟩
/--
Instance `NNRat.instTrivialStar` / 实例 `NNRat.instTrivialStar`

English:
instance NNRat.instTrivialStar
  signature: : TrivialStar Rat>=0
  body: ⟨fun _ => rfl⟩

中文:
实例 NNRat.instTrivialStar
  签名: : TrivialStar Rat>=0
  定义体: ⟨fun _ => rfl⟩
-/
instance NNRat.instTrivialStar : TrivialStar Rat>=0 := ⟨fun _ => rfl⟩

variable {R : Type*}

open MulOpposite

@[simp, norm_cast]
/--
lemma `star_nnratCast` / 引理 `star_nnratCast`

English:
lemma star_nnratCast
  given: [DivisionSemiring R] [StarRing R] (q : Rat>=0)
  statement: star (q : R) = q
  proof: (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]

中文:
引理 star_nnratCast
  条件: [DivisionSemiring R] [StarRing R] (q : Rat>=0)
  结论: star (q : R) = q
  证明: (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]

Depends on / 依赖: congr_arg, map_nnratCast, starRingEquiv, unop_nnratCast
-/
lemma star_nnratCast [DivisionSemiring R] [StarRing R] (q : Rat>=0) : star (q : R) = q :=
  (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]
/--
theorem `star_ratCast` / 定理 `star_ratCast`

English:
theorem star_ratCast
  given: [DivisionRing R] [StarRing R] (r : Rat)
  statement: star (r : R) = r
  proof: (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)

中文:
定理 star_ratCast
  条件: [DivisionRing R] [StarRing R] (r : Rat)
  结论: star (r : R) = r
  证明: (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)

Depends on / 依赖: congr_arg, map_ratCast, starRingEquiv, unop_ratCast
-/
theorem star_ratCast [DivisionRing R] [StarRing R] (r : Rat) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)
