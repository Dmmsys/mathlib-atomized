/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.PartialSups

/-!
# Results about `partialSups` of functions taking values in a `Group`
-/

public section

variable {α ι : Type*}

variable [SemilatticeSup α] [Group α] [Preorder ι] [LocallyFiniteOrderBot ι]

@[to_additive]
/--
lemma `partialSups_const_mul` / 引理 `partialSups_const_mul`

English:
lemma partialSups_const_mul
  given: [MulLeftMono α] (f : ι -> α) (c : α) (i : ι)
  proof: map_partialSups (OrderIso.mulLeft _) ..

@[to_additive]

中文:
引理 partialSups_const_mul
  条件: [MulLeftMono α] (f : ι -> α) (c : α) (i : ι)
  证明: map_partialSups (OrderIso.mulLeft _) ..

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, map_partialSups, mulLeft
-/
lemma partialSups_const_mul [MulLeftMono α] (f : ι -> α) (c : α) (i : ι) :
    partialSups (c * f ·) i = c * partialSups f i := map_partialSups (OrderIso.mulLeft _) ..

@[to_additive]
/--
lemma `partialSups_mul_const` / 引理 `partialSups_mul_const`

English:
lemma partialSups_mul_const
  given: [MulRightMono α] (f : ι -> α) (c : α) (i : ι)
  proof: map_partialSups (OrderIso.mulRight _) ..

中文:
引理 partialSups_mul_const
  条件: [MulRightMono α] (f : ι -> α) (c : α) (i : ι)
  证明: map_partialSups (OrderIso.mulRight _) ..

Depends on / 依赖: IsOrderedRing, IsOrderedRing.toIsOrderedModule, OrderIso, OrderIso.mulRight, map_partialSups, mulRight, toIsOrderedModule
-/
lemma partialSups_mul_const [MulRightMono α] (f : ι -> α) (c : α) (i : ι) :
    partialSups (f · * c) i = partialSups f i * c := map_partialSups (OrderIso.mulRight _) ..
