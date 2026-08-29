/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Floris Van Doorn
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Rat.Encodable
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

public section

assert_not_exists Module Field

open Cardinal

/--
theorem `Cardinal.mkRat` / 定理 `Cardinal.mkRat`

English:
theorem Cardinal.mkRat
  statement: #Rat = ℵ₀
  proof: mk_eq_aleph0 Rat

中文:
定理 Cardinal.mkRat
  结论: #Rat = ℵ₀
  证明: mk_eq_aleph0 Rat

Depends on / 依赖: mk_eq_aleph0
-/
theorem Cardinal.mkRat : #Rat = ℵ₀ := mk_eq_aleph0 Rat
