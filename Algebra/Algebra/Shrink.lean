/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Ring.Shrink

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [CommSemiring R]

namespace Shrink

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] [Algebra R α] : Algebra R (Shrink.{v} α)
  body: (equivShrink α).symm.algebra _

中文:
实例 [Semiring
  签名: α] [Algebra R α] : Algebra R (Shrink.{v} α)
  定义体: (equivShrink α).symm.algebra _

Depends on / 依赖: algebra, equivShrink, symm.algebra
-/
instance [Semiring α] [Algebra R α] : Algebra R (Shrink.{v} α) := (equivShrink α).symm.algebra _

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves algebra structure. -/
@[simps!]
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: [Semiring α] [Algebra R α]
  body: (equivShrink α).symm.algEquiv _

中文:
定义 algEquiv
  签名: [Semiring α] [Algebra R α]
  定义体: (equivShrink α).symm.algEquiv _

Depends on / 依赖: algEquiv, equivShrink, symm.algEquiv
-/
def algEquiv [Semiring α] [Algebra R α] : Shrink.{v} α ≃ₐ[R] α :=
  (equivShrink α).symm.algEquiv _

end Shrink
