/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Real.Basic

/-!
# The real numbers are a \*-ring, with the trivial \*-structure
-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing Real
  body: starRingOfComm

中文:
实例 :
  签名: StarRing 实数
  定义体: starRingOfComm

Depends on / 依赖: starRingOfComm
-/
instance : StarRing Real :=
  starRingOfComm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TrivialStar Real
  body: ⟨fun _ => rfl⟩

中文:
实例 :
  签名: TrivialStar 实数
  定义体: ⟨fun _ => rfl⟩
-/
instance : TrivialStar Real :=
  ⟨fun _ => rfl⟩
