/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℕ`
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Multiplicative

namespace Nat

/--
lemma `toAdd_pow` / 引理 `toAdd_pow`

English:
lemma toAdd_pow
  given: (a : Multiplicative Nat) (b : Nat)
  statement: (a ^ b).toAdd = a.toAdd * b
  proof: mul_comm _ _

中文:
引理 toAdd_pow
  条件: (a : Multiplicative 自然数) (b : 自然数)
  结论: (a ^ b).toAdd = a.toAdd * b
  证明: mul_comm _ _

Depends on / 依赖: mul_comm
-/
lemma toAdd_pow (a : Multiplicative Nat) (b : Nat) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

/--
lemma `ofAdd_mul` / 引理 `ofAdd_mul`

English:
lemma ofAdd_mul
  given: (a b : Nat)
  statement: ofAdd (a * b) = ofAdd a ^ b
  proof: (toAdd_pow _ _).symm

中文:
引理 ofAdd_mul
  条件: (a b : 自然数)
  结论: ofAdd (a * b) = ofAdd a ^ b
  证明: (toAdd_pow _ _).symm
-/
@[simp] lemma ofAdd_mul (a b : Nat) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm

end Nat
