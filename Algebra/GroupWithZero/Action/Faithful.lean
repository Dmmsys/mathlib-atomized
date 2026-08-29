/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module -- shake: keep-all

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Faithful actions involving groups with zero
-/
deprecated_module (since := "2026-02-03")

public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {α : Type*}

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
@[nolint unusedArguments, deprecated "subsumed by `instFaithfulSMul`" (since := "2026-02-03")]
/--
lemma `IsRightCancelMulZero.faithfulSMul` / 引理 `IsRightCancelMulZero.faithfulSMul`

English:
lemma IsRightCancelMulZero.faithfulSMul
  given: [MonoidWithZero α] [IsRightCancelMulZero α]
  proof: inferInstance

中文:
引理 是右消去MulZero.faithfulSMul
  条件: [带零幺半群 α] [是右消去MulZero α]
  证明: inferInstance
-/
lemma IsRightCancelMulZero.faithfulSMul [MonoidWithZero α] [IsRightCancelMulZero α] :
    FaithfulSMul α α := inferInstance
