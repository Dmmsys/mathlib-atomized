/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather
-/
module

public import Mathlib.Init
public import Batteries.Tactic.Lint.Misc

/-!
# Bundled types

`Bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `Category` instances for these in
`Mathlib/CategoryTheory/ConcreteCategory/UnbundledHom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `Mathlib/CategoryTheory/ConcreteCategory/BundledHom.lean`
(for categories with bundled homs, e.g. monoids).

Note: this structure will be deprecated in the future in favor of defining the category manually
and then providing the `ConcreteCategory` instance on top of this. See
`Mathlib/CategoryTheory/ConcreteCategory/Basic.lean` for more details.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {c d : Type u -> Type v}

/--
Definition of `Bundled` / `Bundled` 的定义

English:
structure Bundled
  parameters: (c : Type u -> Type v)
  axioms and operations (2):
    - α : Type u
    - str : c α  [default: by infer_instance]

中文:
结构 Bundled
  参数: (c : 类型u -> 类型v)
  公理与运算 (2 个):
    - α : 类型u
    - str : c α  [默认: by infer_instance]

Depends on / 依赖: PreservesColimits, PreservesColimits.preservesFiniteColimits, infer_instance, preservesFiniteColimits
-/
structure Bundled (c : Type u -> Type v) : Type max (u + 1) v where
  /-- The underlying type of the bundled type -/
  α : Type u
  /-- The corresponding instance of the bundled type class -/
  str : c α := by infer_instance

namespace Bundled

attribute [coe] α

-- This is needed so that we can ask for an instance of `c α` below even though Lean doesn't know
-- that `c α` is a typeclass.
set_option checkBinderAnnotations false in

-- Usually explicit instances will provide their own version of this, e.g. `MonCat.of` and
-- `TopCat.of`.
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: {c : Type u -> Type v} (α : Type u) [str : c α]
  body: ⟨α, str⟩

中文:
定义 of
  签名: {c : 类型u -> 类型v} (α : 类型u) [str : c α]
  定义体: ⟨α, str⟩
-/
def of {c : Type u -> Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩

/--
Instance `coeSort` / 实例 `coeSort`

English:
instance coeSort
  signature: : CoeSort (Bundled c) (Type u)
  body: ⟨Bundled.α⟩

中文:
实例 coeSort
  签名: : CoeSort (Bundled c) (类型u)
  定义体: ⟨Bundled.α⟩

Depends on / 依赖: Bundled
-/
instance coeSort : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (α) (str)
  statement: (@Bundled.mk c α str : Type u) = α
  proof: rfl

中文:
定理 coe_mk
  条件: (α) (str)
  结论: (@Bundled.mk c α str : 类型u) = α
  证明: rfl
-/
theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: (f : forall {α}, c α -> d α) (b : Bundled c)
  body: ⟨b, f b.str⟩

中文:
缩写 map
  签名: (f : 对任意 {α}, c α -> d α) (b : Bundled c)
  定义体: ⟨b, f b.str⟩

Depends on / 依赖: Finite, b.str
-/
abbrev map (f : forall {α}, c α -> d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩

end Bundled

end CategoryTheory
