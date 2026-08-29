/-
Copyright (c) 2025 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# Divisibility in finite types
-/

public section

variable {M : Type*} [Semigroup M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: M] [DecidableEq M] (a b
  body: decidable_of_iff (exists c, b = a * c) dvd_def

中文:
实例 [Fintype
  签名: M] [DecidableEq M] (a b
  定义体: decidable_of_iff (exists c, b = a * c) dvd_def

Depends on / 依赖: decidable_of_iff, dvd_def
-/
instance [Fintype M] [DecidableEq M] (a b : M) : Decidable (a ∣ b) :=
  decidable_of_iff (exists c, b = a * c) dvd_def
