/-
Copyright (c) 2025 Vilim Lendvaj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vilim Lendvaj
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Control.Basic

/-!
# Convert from `Applicative` to `CategoryTheory.Functor.LaxMonoidal`

This allows us to use Lean's `Type`-based applicative functors in category theory.

-/

@[expose] public section

namespace CategoryTheory

section

variable (F : Type* → Type*) [Applicative F] [LawfulApplicative F]

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] map_seq seq_map_assoc types_tensorObj_def types_tensorUnit_def
  LawfulApplicative.pure_seq LawfulApplicative.seq_assoc in
/-- A lawful `Applicative` gives a category theory `LaxMonoidal` functor
between categories of types. -/
@[simps]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lawful `Applicative` gives a category theory `LaxMonoidal` functor
between categories of types.
-/
instance : (ofTypeFunctor F).LaxMonoidal where
  ε := ↾fun _ ↦ (pure PUnit.unit : F _)
  μ _ _ := ↾fun p ↦ (Prod.mk <$> p.1 <*> p.2 : F _)

end

end CategoryTheory

