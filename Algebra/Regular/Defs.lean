/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Notation.Defs

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements, along with their `to_additive`
analogues add-left-regular, add-right-regular and add-regular elements.

For monoids where _every_ element is regular, see `IsCancelMul` and nearby typeclasses.
-/

@[expose] public section

variable {R : Type*} [Mul R]

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective. -/
@[to_additive (attr := instance_reducible)
  /-- An add-left-regular element is an element `c` such that addition
    on the left by `c` is injective. -/]
/--
Definition of `IsLeftRegular` / `IsLeftRegular` 的定义

English:
definition IsLeftRegular
  signature: (c : R)
  body: (c * ·).Injective

中文:
定义 IsLeftRegular
  签名: (c : R)
  定义体: (c * ·).Injective

Depends on / 依赖: Injective
-/
def IsLeftRegular (c : R) :=
  (c * ·).Injective

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive (attr := instance_reducible)
  /-- An add-right-regular element is an element `c` such that addition
    on the right by `c` is injective. -/]
/--
Definition of `IsRightRegular` / `IsRightRegular` 的定义

English:
definition IsRightRegular
  signature: (c : R)
  body: (· * c).Injective

中文:
定义 IsRightRegular
  签名: (c : R)
  定义体: (· * c).Injective

Depends on / 依赖: Injective
-/
def IsRightRegular (c : R) :=
  (· * c).Injective

/--
Definition of `IsAddRegular` / `IsAddRegular` 的定义

English:
structure IsAddRegular
  parameters: {R : Type*} [Add R] (c : R)
  axioms and operations (2):
    - left : IsAddLeftRegular c
    - right : IsAddRightRegular c

中文:
结构 IsAddRegular
  参数: {R : 类型} [Add R] (c : R)
  公理与运算 (2 个):
    - left : IsAddLeftRegular c
    - right : IsAddRightRegular c
-/
structure IsAddRegular {R : Type*} [Add R] (c : R) : Prop where
  /-- An add-regular element `c` is left-regular -/
  left : IsAddLeftRegular c
  /-- An add-regular element `c` is right-regular -/
  right : IsAddRightRegular c

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
structure IsRegular
  parameters: (c : R)
  axioms and operations (2):
    - left : IsLeftRegular c
    - right : IsRightRegular c

中文:
结构 IsRegular
  参数: (c : R)
  公理与运算 (2 个):
    - left : IsLeftRegular c
    - right : IsRightRegular c
-/
structure IsRegular (c : R) : Prop where
  /-- A regular element `c` is left-regular -/
  left : IsLeftRegular c
  /-- A regular element `c` is right-regular -/
  right : IsRightRegular c

attribute [simp] IsRegular.left IsRegular.right

attribute [to_additive] IsRegular

@[to_additive]
/--
theorem `isRegular_iff` / 定理 `isRegular_iff`

English:
theorem isRegular_iff
  given: {c : R}
  statement: IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c
  proof: ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

中文:
定理 isRegular_iff
  条件: {c : R}
  结论: IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c
  证明: ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
-/
theorem isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
