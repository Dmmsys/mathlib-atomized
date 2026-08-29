/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Conjugacy of elements of finite groups
-/

public section

assert_not_exists Field

-- TODO: the following `assert_not_exists` should work, but does not
-- assert_not_exists MonoidWithZero

variable {α : Type*} [Monoid α]

attribute [local instance] IsConj.setoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: α] [DecidableRel (IsConj : α -> α -> Prop)] : Fintype (ConjClasses α)
  body: Quotient.fintype (IsConj.setoid α)

中文:
实例 [有限类型
  签名: α] [DecidableRel (IsConj : α -> α -> 命题)] : 有限类型 (ConjClasses α)
  定义体: Quotient.fintype (IsConj.setoid α)

Depends on / 依赖: IsConj, IsConj.setoid, Quotient, Quotient.fintype, fintype, setoid
-/
instance [Fintype α] [DecidableRel (IsConj : α -> α -> Prop)] : Fintype (ConjClasses α) :=
  Quotient.fintype (IsConj.setoid α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (ConjClasses α)
  body: Quotient.finite _

中文:
实例 [有限
  签名: α] : 有限 (ConjClasses α)
  定义体: Quotient.finite _

Depends on / 依赖: Quotient, Quotient.finite, finite
-/
instance [Finite α] : Finite (ConjClasses α) :=
  Quotient.finite _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [Fintype α] : DecidableRel (IsConj
  body: fun a b =>
  inferInstanceAs (Decidable (exists c : αˣ, c.1 * a = b * c.1))

中文:
实例 [DecidableEq
  签名: α] [有限类型 α] : DecidableRel (IsConj
  定义体: fun a b =>
  inferInstanceAs (Decidable (exists c : αˣ, c.1 * a = b * c.1))
-/
instance [DecidableEq α] [Fintype α] : DecidableRel (IsConj : α -> α -> Prop) := fun a b =>
  inferInstanceAs (Decidable (exists c : αˣ, c.1 * a = b * c.1))

/--
Instance `conjugatesOf.fintype` / 实例 `conjugatesOf.fintype`

English:
instance conjugatesOf.fintype
  signature: [Fintype α] [DecidableRel (IsConj : α -> α -> Prop)] {a : α}
  body: @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _

中文:
实例 conjugatesOf.fintype
  签名: [有限类型 α] [DecidableRel (IsConj : α -> α -> 命题)] {a : α}
  定义体: @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _

Depends on / 依赖: DecidableRel, IsConj, Subtype, Subtype.fintype, fintype
-/
instance conjugatesOf.fintype [Fintype α] [DecidableRel (IsConj : α -> α -> Prop)] {a : α} :
    Fintype (conjugatesOf a) :=
  @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _

namespace ConjClasses

variable [Fintype α] [DecidableRel (IsConj : α -> α -> Prop)]

instance {x : ConjClasses α} : Fintype (carrier x) :=
  Quotient.recOnSubsingleton x fun _ => conjugatesOf.fintype

end ConjClasses
