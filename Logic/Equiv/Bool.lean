/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Emily Riehl, Wrenna Robson
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Equivalences involving `Bool`

This file shows that `not : Bool → Bool` is an equivalence and derives some consequences
-/

@[expose] public section

/-- The boolean negation function `not : Bool → Bool` is an involution and thus an equivalence. -/
@[simps!]
/--
Definition of `Equiv.boolNot` / `Equiv.boolNot` 的定义

English:
definition Equiv.boolNot
  signature: : Equiv.Perm Bool
  body: Bool.involutive_not.toPerm

中文:
定义 Equiv.boolNot
  签名: : Equiv.Perm 布尔
  定义体: Bool.involutive_not.toPerm

Depends on / 依赖: Bool.involutive_not.toPerm, involutive_not, toPerm
-/
def Equiv.boolNot : Equiv.Perm Bool := Bool.involutive_not.toPerm

namespace Bool

open Function

/--
theorem `not_bijective` / 定理 `not_bijective`

English:
theorem not_bijective
  statement: Bijective not
  proof: Equiv.boolNot.bijective

中文:
定理 not_bijective
  结论: Bijective not
  证明: Equiv.boolNot.bijective

Depends on / 依赖: Equiv.boolNot.bijective, bijective, boolNot
-/
theorem not_bijective : Bijective not := Equiv.boolNot.bijective
/--
theorem `not_injective` / 定理 `not_injective`

English:
theorem not_injective
  statement: Injective not
  proof: Equiv.boolNot.injective

中文:
定理 not_injective
  结论: Injective not
  证明: Equiv.boolNot.injective

Depends on / 依赖: Equiv.boolNot.injective, boolNot, injective
-/
theorem not_injective : Injective not := Equiv.boolNot.injective
/--
theorem `not_surjective` / 定理 `not_surjective`

English:
theorem not_surjective
  statement: Surjective not
  proof: Equiv.boolNot.surjective

中文:
定理 not_surjective
  结论: Surjective not
  证明: Equiv.boolNot.surjective

Depends on / 依赖: Equiv.boolNot.surjective, boolNot, surjective
-/
theorem not_surjective : Surjective not := Equiv.boolNot.surjective

/--
theorem `not_leftInverse` / 定理 `not_leftInverse`

English:
theorem not_leftInverse
  statement: LeftInverse not not
  proof: not_not

中文:
定理 not_leftInverse
  结论: LeftInverse not not
  证明: not_not

Depends on / 依赖: not_not
-/
theorem not_leftInverse : LeftInverse not not := not_not
/--
theorem `not_rightInverse` / 定理 `not_rightInverse`

English:
theorem not_rightInverse
  statement: RightInverse not not
  proof: not_not

中文:
定理 not_rightInverse
  结论: RightInverse not not
  证明: not_not

Depends on / 依赖: not_not
-/
theorem not_rightInverse : RightInverse not not := not_not

/--
theorem `not_hasLeftInverse` / 定理 `not_hasLeftInverse`

English:
theorem not_hasLeftInverse
  statement: HasLeftInverse not
  proof: ⟨not, not_leftInverse⟩

中文:
定理 not_hasLeftInverse
  结论: HasLeftInverse not
  证明: ⟨not, not_leftInverse⟩

Depends on / 依赖: not_leftInverse
-/
theorem not_hasLeftInverse : HasLeftInverse not := ⟨not, not_leftInverse⟩
/--
theorem `not_hasRightInverse` / 定理 `not_hasRightInverse`

English:
theorem not_hasRightInverse
  statement: HasRightInverse not
  proof: ⟨not, not_rightInverse⟩

中文:
定理 not_hasRightInverse
  结论: HasRightInverse not
  证明: ⟨not, not_rightInverse⟩

Depends on / 依赖: not_rightInverse
-/
theorem not_hasRightInverse : HasRightInverse not := ⟨not, not_rightInverse⟩

end Bool
