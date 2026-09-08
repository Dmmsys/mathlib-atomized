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

variable {c d : Type u → Type v}

/-- `Bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
/-
**CategoryTheory.Bundled** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Bundled (c : Type u -> Type v) : Type max (u + 1) v where /-- The underlyi
ng type of the bundled type -/ α : Type u /-- The corresponding instance of the 
bundled type class -/ str : c α
参数：c : Type u -> Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter.
-/
structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
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
/-- A generic function for lifting a type equipped with an instance to a bundled object. -/
/-
**CategoryTheory.Bundled.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bundled`。
形式化陈述：of {c : Type u -> Type v} (α : Type u) [str : c α] : Bundled c
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generic function for lifting a type equipped with an instance to a bundled obj
ect.
-/
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩
/-
**CategoryTheory.Bundled.coeSort** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bundl
ed`。
形式化陈述：coeSort : CoeSort (Bundled c) (Type u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeSort : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩
/-
**CategoryTheory.Bundled.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bundle
d`。
形式化陈述：coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α
参数：α；str。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl

/-- Map over the bundled structure -/
/-
**CategoryTheory.Bundled.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Bundled
`。
形式化陈述：map (f : forall {α}, c α -> d α) (b : Bundled c) : Bundled d
参数：f : forall {α}, c α -> d α；b : Bundled c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map over the bundled structure
-/
abbrev map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩

end Bundled

end CategoryTheory

