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
/-
**commutatorElement** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commutatorElement {G : Type*} [Group G] : Bracket G G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commutatorElement {G : Type*} [Group G] : Bracket G G :=
  ⟨fun g₁ g₂ ↦ g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

namespace commutatorElement

attribute [scoped instance] commutatorElement

end commutatorElement

namespace addCommutatorElement

attribute [scoped instance] addCommutatorElement

end addCommutatorElement

open scoped commutatorElement

@[to_additive]
/-
**commutatorElement_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commutatorElement_def {G : Type*} [Group G] (g₁ g₂ : G) : ⁅g₁, g₂⁆ = g₁ * 
g₂ * g₁⁻¹ * g₂⁻¹
参数：g₁ g₂ : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commutatorElement_def {G : Type*} [Group G] (g₁ g₂ : G) :
    ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ :=
  rfl
