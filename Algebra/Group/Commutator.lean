/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Bracket

/-!
# The bracket on a group given by commutator.

## Notation

After `open scoped commutatorElement`, `⁅g₁, g₂⁆` is syntax for `g₁ * g₂ * g₁⁻¹ * g₂⁻¹`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

/-- The commutator of two elements `g₁` and `g₂`. This is a scoped instance in the
`commutatorElement` namespace to avoid clashing with other brackets. -/
@[to_additive (attr := reducible) /-- The additive commutator of two elements `g₁` and `g₂`. This
is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets -/]
/--
Definition of `commutatorElement` / `commutatorElement` 的定义

English:
definition commutatorElement
  signature: {G : Type*} [Group G]
  body: ⟨fun g₁ g₂ => g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

中文:
定义 commutatorElement
  签名: {G : 类型} [Group G]
  定义体: ⟨fun g₁ g₂ => g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩
-/
def commutatorElement {G : Type*} [Group G] : Bracket G G :=
  ⟨fun g₁ g₂ => g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

namespace commutatorElement

attribute [scoped instance] commutatorElement

end commutatorElement

namespace addCommutatorElement

attribute [scoped instance] addCommutatorElement

end addCommutatorElement

open scoped commutatorElement

@[to_additive]
/--
theorem `commutatorElement_def` / 定理 `commutatorElement_def`

English:
theorem commutatorElement_def
  given: {G : Type*} [Group G] (g₁ g₂ : G)
  proof: rfl

中文:
定理 commutatorElement_def
  条件: {G : 类型} [Group G] (g₁ g₂ : G)
  证明: rfl
-/
theorem commutatorElement_def {G : Type*} [Group G] (g₁ g₂ : G) :
    ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ :=
  rfl
