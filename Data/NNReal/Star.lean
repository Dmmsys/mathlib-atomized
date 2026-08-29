/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.Real.Star

/-!
# The non-negative real numbers are a \*-ring, with the trivial \*-structure
-/

public section

assert_not_exists Finset

open scoped NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing Real>=0
  body: starRingOfComm

中文:
实例 :
  签名: 对合环 实数>=0
  定义体: starRingOfComm

Depends on / 依赖: starRingOfComm
-/
instance : StarRing Real>=0 := starRingOfComm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TrivialStar Real>=0
  body: rfl

中文:
实例 :
  签名: TrivialStar 实数>=0
  定义体: rfl
-/
instance : TrivialStar Real>=0 where
  star_trivial _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule Real>=0 Real
  body: by simp only [star_trivial, forall_const]

中文:
实例 :
  签名: 对合模 实数>=0 实数
  定义体: by simp only [star_trivial, forall_const]

Depends on / 依赖: forall_const, star_trivial
-/
instance : StarModule Real>=0 Real where
  star_smul := by simp only [star_trivial, forall_const]

instance {E : Type*} [AddCommMonoid E] [Star E] [Module Real E] [StarModule Real E] :
    StarModule Real>=0 E where
  star_smul _ := star_smul (_ : Real)
