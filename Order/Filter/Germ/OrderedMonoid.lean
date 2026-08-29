/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Ordered monoid instances on the space of germs of a function at a filter

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* `IsOrderedCancelMonoid` and `IsOrderedCancelAddMonoid`.

## Tags

filter, germ
-/

public section

namespace Filter.Germ

variable {α : Type*} {β : Type*} {l : Filter α}

@[to_additive]
/--
Instance `instIsOrderedMonoid` / 实例 `instIsOrderedMonoid`

English:
instance instIsOrderedMonoid
  signature: [CommMonoid β] [Preorder β] [IsOrderedMonoid β]
  body: inductionOn₂ f g fun _ _ H h => inductionOn h fun _ => H.mono
    fun _ H => by dsimp; gcongr

@[to_additive]

中文:
实例 instIsOrderedMonoid
  签名: [交换幺半群 β] [预序 β] [是Ordered幺半群 β]
  定义体: inductionOn₂ f g fun _ _ H h => inductionOn h fun _ => H.mono
    fun _ H => by dsimp; gcongr

@[to_additive]

Depends on / 依赖: H.mono, inductionOn
-/
instance instIsOrderedMonoid [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (Germ l β) where
  mul_le_mul_left f g := inductionOn₂ f g fun _ _ H h => inductionOn h fun _ => H.mono
    fun _ H => by dsimp; gcongr

@[to_additive]
/--
Instance `instIsOrderedCancelMonoid` / 实例 `instIsOrderedCancelMonoid`

English:
instance instIsOrderedCancelMonoid
  signature: [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β]
  body: inductionOn₃ f g h fun _ _ _ H => H.mono
    fun _ => le_of_mul_le_mul_left'

@[to_additive]

中文:
实例 instIsOrderedCancelMonoid
  签名: [交换幺半群 β] [预序 β] [是OrderedCancel幺半群 β]
  定义体: inductionOn₃ f g h fun _ _ _ H => H.mono
    fun _ => le_of_mul_le_mul_left'

@[to_additive]

Depends on / 依赖: H.mono
-/
instance instIsOrderedCancelMonoid [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (Germ l β) where
  le_of_mul_le_mul_left f g h := inductionOn₃ f g h fun _ _ _ H => H.mono
    fun _ => le_of_mul_le_mul_left'

@[to_additive]
/--
Instance `instCanonicallyOrderedMul` / 实例 `instCanonicallyOrderedMul`

English:
instance instCanonicallyOrderedMul
  signature: [Mul β] [LE β] [CanonicallyOrderedMul β]
  body: inductionOn₂ x y fun _ _ => Eventually.of_forall fun _ => le_mul_self
  le_self_mul x y := inductionOn₂ x y fun _ _ => Eventually.of_forall fun _ => le_self_mul

中文:
实例 instCanonicallyOrderedMul
  签名: [乘法 β] [LE β] [典范有序乘法 β]
  定义体: inductionOn₂ x y fun _ _ => Eventually.of_forall fun _ => le_mul_self
  le_self_mul x y := inductionOn₂ x y fun _ _ => Eventually.of_forall fun _ => le_self_mul

Depends on / 依赖: Eventually, Eventually.of_forall, le_mul_self, of_forall
-/
instance instCanonicallyOrderedMul [Mul β] [LE β] [CanonicallyOrderedMul β] :
    CanonicallyOrderedMul (Germ l β) where
  le_mul_self x y := inductionOn₂ x y fun _ _ => Eventually.of_forall fun _ => le_mul_self
  le_self_mul x y := inductionOn₂ x y fun _ _ => Eventually.of_forall fun _ => le_self_mul

end Filter.Germ
