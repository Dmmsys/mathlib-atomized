/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coset.Card

/-!
# The abelianization of a finite group is finite
-/

public section

variable {G : Type*} [Group G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: G] [DecidablePred (· in commutator G)] : Fintype (Abelianization G)
  body: QuotientGroup.fintype (commutator G)

中文:
实例 [Fintype
  签名: G] [DecidablePred (· in commutator G)] : Fintype (Abelianization G)
  定义体: QuotientGroup.fintype (commutator G)
-/
instance [Fintype G] [DecidablePred (· in commutator G)] : Fintype (Abelianization G) :=
  QuotientGroup.fintype (commutator G)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] : Finite (Abelianization G)
  body: Quotient.finite _

中文:
实例 [Finite
  签名: G] : Finite (Abelianization G)
  定义体: Quotient.finite _

Depends on / 依赖: Quotient, Quotient.finite, finite
-/
instance [Finite G] : Finite (Abelianization G) :=
  Quotient.finite _
