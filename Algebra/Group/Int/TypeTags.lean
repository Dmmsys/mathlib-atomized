/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℤ`.
-/

public section


open Nat

namespace Int

section Multiplicative

open Multiplicative

/--
lemma `toAdd_pow` / 引理 `toAdd_pow`

English:
lemma toAdd_pow
  given: (a : Multiplicative Int) (b : Nat)
  statement: (a ^ b).toAdd = a.toAdd * b
  proof: mul_comm _ _

中文:
引理 toAdd_pow
  条件: (a : Multiplicative 整数) (b : 自然数)
  结论: (a ^ b).toAdd = a.toAdd * b
  证明: mul_comm _ _

Depends on / 依赖: mul_comm
-/
lemma toAdd_pow (a : Multiplicative Int) (b : Nat) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

/--
lemma `toAdd_zpow` / 引理 `toAdd_zpow`

English:
lemma toAdd_zpow
  given: (a : Multiplicative Int) (b : Int)
  statement: (a ^ b).toAdd = a.toAdd * b
  proof: mul_comm _ _

中文:
引理 toAdd_zpow
  条件: (a : Multiplicative 整数) (b : 整数)
  结论: (a ^ b).toAdd = a.toAdd * b
  证明: mul_comm _ _

Depends on / 依赖: _image, mul_comm
-/
lemma toAdd_zpow (a : Multiplicative Int) (b : Int) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

/--
lemma `ofAdd_mul` / 引理 `ofAdd_mul`

English:
lemma ofAdd_mul
  given: (a b : Int)
  statement: ofAdd (a * b) = ofAdd a ^ b
  proof: (toAdd_zpow ..).symm

中文:
引理 ofAdd_mul
  条件: (a b : 整数)
  结论: ofAdd (a * b) = ofAdd a ^ b
  证明: (toAdd_zpow ..).symm
-/
@[simp] lemma ofAdd_mul (a b : Int) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_zpow ..).symm

end Multiplicative

end Int
