/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

@[expose] public noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [Semiring R] [AddCommMonoid α] [Module R α]

namespace Shrink

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (Shrink.{v} α)
  body: (equivShrink α).symm.module R

中文:
实例 :
  签名: Module R (Shrink.{v} α)
  定义体: (equivShrink α).symm.module R

Depends on / 依赖: equivShrink, module, symm.module
-/
instance : Module R (Shrink.{v} α) := (equivShrink α).symm.module R

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves module structure. -/
@[simps!]
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: : Shrink.{v} α ≃ₗ[R] α
  body: (equivShrink α).symm.linearEquiv _

中文:
定义 linearEquiv
  签名: : Shrink.{v} α ≃ₗ[R] α
  定义体: (equivShrink α).symm.linearEquiv _

Depends on / 依赖: equivShrink, linearEquiv, symm.linearEquiv
-/
def linearEquiv : Shrink.{v} α ≃ₗ[R] α := (equivShrink α).symm.linearEquiv _

end Shrink
