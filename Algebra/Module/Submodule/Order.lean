/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Monoid.Basic

/-!
# Ordered instances on submodules
-/

public section

namespace Submodule
variable {R M : Type*}

section OrderedMonoid
variable [Semiring R]

/--
Instance `toIsOrderedAddMonoid` / 实例 `toIsOrderedAddMonoid`

English:
instance toIsOrderedAddMonoid
  signature: [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  body: Function.Injective.isOrderedAddMonoid Subtype.val (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedAddMonoid
  签名: [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  定义体: Function.Injective.isOrderedAddMonoid Subtype.val (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedAddMonoid, Injective, Subtype, Subtype.val, isOrderedAddMonoid
-/
instance toIsOrderedAddMonoid [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module R M] (S : Submodule R M) :
    IsOrderedAddMonoid S :=
  Function.Injective.isOrderedAddMonoid Subtype.val (fun _ _ => rfl) .rfl

/--
Instance `toIsOrderedCancelAddMonoid` / 实例 `toIsOrderedCancelAddMonoid`

English:
instance toIsOrderedCancelAddMonoid
  signature: [AddCommMonoid M] [PartialOrder M]
  body: Function.Injective.isOrderedCancelAddMonoid Subtype.val (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedCancelAddMonoid
  签名: [AddCommMonoid M] [PartialOrder M]
  定义体: Function.Injective.isOrderedCancelAddMonoid Subtype.val (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedCancelAddMonoid, Injective, Subtype, Subtype.val, isOrderedCancelAddMonoid
-/
instance toIsOrderedCancelAddMonoid [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] [Module R M] (S : Submodule R M) :
    IsOrderedCancelAddMonoid S :=
  Function.Injective.isOrderedCancelAddMonoid Subtype.val (fun _ _ => rfl) .rfl

end OrderedMonoid

end Submodule
