/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.ULift
public import Mathlib.Algebra.Ring.ULift

/-!
# Field instances for `ULift`

This file defines instances for fields, semifields, and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

@[expose] public section

universe u
variable {α : Type u}

namespace ULift

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: [NNRatCast α]
  body: up q

中文:
实例 instNNRatCast
  签名: [NNRatCast α]
  定义体: up q
-/
instance instNNRatCast [NNRatCast α] : NNRatCast (ULift α) where nnratCast q := up q
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: [RatCast α]
  body: up q

中文:
实例 instRatCast
  签名: [RatCast α]
  定义体: up q
-/
instance instRatCast [RatCast α] : RatCast (ULift α) where ratCast q := up q

/--
lemma `up_nnratCast` / 引理 `up_nnratCast`

English:
lemma up_nnratCast
  given: [NNRatCast α] (q : Rat>=0)
  statement: up (q : α) = q
  proof: rfl

中文:
引理 up_nnratCast
  条件: [NNRatCast α] (q : Rat>=0)
  结论: up (q : α) = q
  证明: rfl
-/
@[simp, norm_cast] lemma up_nnratCast [NNRatCast α] (q : Rat>=0) : up (q : α) = q := rfl
/--
lemma `down_nnratCast` / 引理 `down_nnratCast`

English:
lemma down_nnratCast
  given: [NNRatCast α] (q : Rat>=0)
  statement: down (q : ULift α) = q
  proof: rfl

中文:
引理 down_nnratCast
  条件: [NNRatCast α] (q : Rat>=0)
  结论: down (q : ULift α) = q
  证明: rfl
-/
@[simp, norm_cast] lemma down_nnratCast [NNRatCast α] (q : Rat>=0) : down (q : ULift α) = q := rfl
/--
lemma `up_ratCast` / 引理 `up_ratCast`

English:
lemma up_ratCast
  given: [RatCast α] (q : Rat)
  statement: up (q : α) = q
  proof: rfl

中文:
引理 up_ratCast
  条件: [RatCast α] (q : Rat)
  结论: up (q : α) = q
  证明: rfl
-/
@[simp, norm_cast] lemma up_ratCast [RatCast α] (q : Rat) : up (q : α) = q := rfl
/--
lemma `down_ratCast` / 引理 `down_ratCast`

English:
lemma down_ratCast
  given: [RatCast α] (q : Rat)
  statement: down (q : ULift α) = q
  proof: rfl

中文:
引理 down_ratCast
  条件: [RatCast α] (q : Rat)
  结论: down (q : ULift α) = q
  证明: rfl
-/
@[simp, norm_cast] lemma down_ratCast [RatCast α] (q : Rat) : down (q : ULift α) = q := rfl

/--
Instance `divisionSemiring` / 实例 `divisionSemiring`

English:
instance divisionSemiring
  signature: [DivisionSemiring α]
  body: up (DivisionSemiring.nnqsmul q x.down)
nnqsmul_def _ _ := congrArg up DivisionSemiring.nnqsmul_def _ _
nnratCast_def _ := congrArg up DivisionSemiring.nnratCast_def _

中文:
实例 divisionSemiring
  签名: [DivisionSemiring α]
  定义体: up (DivisionSemiring.nnqsmul q x.down)
nnqsmul_def _ _ := congrArg up DivisionSemiring.nnqsmul_def _ _
nnratCast_def _ := congrArg up DivisionSemiring.nnratCast_def _

Depends on / 依赖: DivisionSemiring, DivisionSemiring.nnqsmul, nnqsmul, x.down
-/
instance divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) where
  nnqsmul q x := up (DivisionSemiring.nnqsmul q x.down)
nnqsmul_def _ _ := congrArg up DivisionSemiring.nnqsmul_def _ _
nnratCast_def _ := congrArg up DivisionSemiring.nnratCast_def _

/--
Instance `semifield` / 实例 `semifield`

English:
instance semifield
  signature: [Semifield α]
  body: { ULift.divisionSemiring, ULift.commGroupWithZero with }

中文:
实例 semifield
  签名: [Semifield α]
  定义体: { ULift.divisionSemiring, ULift.commGroupWithZero with }

Depends on / 依赖: ULift.commGroupWithZero, ULift.divisionSemiring, commGroupWithZero, divisionSemiring
-/
instance semifield [Semifield α] : Semifield (ULift α) :=
  { ULift.divisionSemiring, ULift.commGroupWithZero with }

/--
Instance `divisionRing` / 实例 `divisionRing`

English:
instance divisionRing
  signature: [DivisionRing α]
  body: ring
  __ := groupWithZero
  nnqsmul q x := up (DivisionSemiring.nnqsmul q x.down)
nnqsmul_def _ _ := congrArg up DivisionSemiring.nnqsmul_def _ _
nnratCast_def _ := congrArg up DivisionSemiring.nnratCast_def _
  qsmul q x := up (DivisionRing.qsmul q x.down)
qsmul_def _ _ := congrArg up DivisionRing

中文:
实例 divisionRing
  签名: [DivisionRing α]
  定义体: ring
  __ := groupWithZero
  nnqsmul q x := up (DivisionSemiring.nnqsmul q x.down)
nnqsmul_def _ _ := congrArg up DivisionSemiring.nnqsmul_def _ _
nnratCast_def _ := congrArg up DivisionSemiring.nnratCast_def _
  qsmul q x := up (DivisionRing.qsmul q x.down)
qsmul_def _ _ := congrArg up DivisionRing
-/
instance divisionRing [DivisionRing α] : DivisionRing (ULift α) where
  toRing := ring
  __ := groupWithZero
  nnqsmul q x := up (DivisionSemiring.nnqsmul q x.down)
nnqsmul_def _ _ := congrArg up DivisionSemiring.nnqsmul_def _ _
nnratCast_def _ := congrArg up DivisionSemiring.nnratCast_def _
  qsmul q x := up (DivisionRing.qsmul q x.down)
qsmul_def _ _ := congrArg up DivisionRing.qsmul_def _ _
ratCast_def _ := congrArg up DivisionRing.ratCast_def _

/--
Instance `field` / 实例 `field`

English:
instance field
  signature: [Field α]
  body: {}

中文:
实例 field
  签名: [Field α]
  定义体: {}
-/
instance field [Field α] : Field (ULift α) := {}

end ULift
