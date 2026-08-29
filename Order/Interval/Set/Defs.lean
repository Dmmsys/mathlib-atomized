/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Push.Attr

/-!
# Intervals

In any preorder `α`, we define intervals
(which on each side can be either infinite, open, or closed)
using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.

We also define a typeclass `Set.OrdConnected`
saying that a set includes `Set.Icc a b` whenever it contains both `a` and `b`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [Preorder α] {a b x : α}

/-- `Iio b` is the left-infinite right-open interval $(-∞, b)$. -/
@[to_dual /-- `Ioi a` is the left-open right-infinite interval $(a, ∞)$. -/]
/--
Definition of `Iio` / `Iio` 的定义

English:
definition Iio
  signature: (b : α)
  body: { x | x < b }

中文:
定义 Iio
  签名: (b : α)
  定义体: { x | x < b }
-/
def Iio (b : α) := { x | x < b }

/--
theorem `mem_Iio` / 定理 `mem_Iio`

English:
theorem mem_Iio
  statement: x in Iio b ↔ x < b
  proof: .rfl

中文:
定理 mem_Iio
  结论: x in Iio b ↔ x < b
  证明: .rfl
-/
@[to_dual (attr := simp, grind =, push)] theorem mem_Iio : x in Iio b ↔ x < b := .rfl
/--
theorem `Iio_def` / 定理 `Iio_def`

English:
theorem Iio_def
  given: (a : α)
  statement: { x | x < a } = Iio a
  proof: rfl

中文:
定理 Iio_def
  条件: (a : α)
  结论: { x | x < a } = Iio a
  证明: rfl
-/
@[to_dual] theorem Iio_def (a : α) : { x | x < a } = Iio a := rfl

/-- `Iic b` is the left-infinite right-closed interval $(-∞, b]$. -/
@[to_dual /-- `Ici a` is the left-closed right-infinite interval $[a, ∞)$. -/]
/--
Definition of `Iic` / `Iic` 的定义

English:
definition Iic
  signature: (b : α)
  body: { x | x <= b }

中文:
定义 Iic
  签名: (b : α)
  定义体: { x | x <= b }
-/
def Iic (b : α) := { x | x <= b }

/--
theorem `mem_Iic` / 定理 `mem_Iic`

English:
theorem mem_Iic
  statement: x in Iic b ↔ x <= b
  proof: .rfl

中文:
定理 mem_Iic
  结论: x in Iic b ↔ x <= b
  证明: .rfl
-/
@[to_dual (attr := simp, grind =, push)] theorem mem_Iic : x in Iic b ↔ x <= b := .rfl
/--
theorem `Iic_def` / 定理 `Iic_def`

English:
theorem Iic_def
  given: (b : α)
  statement: { x | x <= b } = Iic b
  proof: rfl

中文:
定理 Iic_def
  条件: (b : α)
  结论: { x | x <= b } = Iic b
  证明: rfl
-/
@[to_dual] theorem Iic_def (b : α) : { x | x <= b } = Iic b := rfl

/-- `Ioo a b` is the left-open right-open interval $(a, b)$. -/
@[to_dual self (reorder := a b)]
/--
Definition of `Ioo` / `Ioo` 的定义

English:
definition Ioo
  signature: (a b : α)
  body: { x | a < x ∧ x < b }

to_dual_insert_cast Ioo := by simp only [and_comm]

中文:
定义 Ioo
  签名: (a b : α)
  定义体: { x | a < x ∧ x < b }

to_dual_insert_cast Ioo := by simp only [and_comm]
-/
def Ioo (a b : α) := { x | a < x ∧ x < b }

to_dual_insert_cast Ioo := by simp only [and_comm]

/--
theorem `mem_Ioo` / 定理 `mem_Ioo`

English:
theorem mem_Ioo
  statement: x in Ioo a b ↔ a < x ∧ x < b
  proof: .rfl

中文:
定理 mem_Ioo
  结论: x in Ioo a b ↔ a < x ∧ x < b
  证明: .rfl
-/
@[simp, grind =, push, to_dual none] theorem mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b := .rfl
/--
theorem `Ioo_def` / 定理 `Ioo_def`

English:
theorem Ioo_def
  given: (a b : α)
  statement: { x | a < x ∧ x < b } = Ioo a b
  proof: rfl

中文:
定理 Ioo_def
  条件: (a b : α)
  结论: { x | a < x ∧ x < b } = Ioo a b
  证明: rfl
-/
@[to_dual none] theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = Ioo a b := rfl

/--
Definition of `Ico` / `Ico` 的定义

English:
definition Ico
  signature: (a b : α)
  body: { x | a <= x ∧ x < b }

中文:
定义 Ico
  签名: (a b : α)
  定义体: { x | a <= x ∧ x < b }
-/
def Ico (a b : α) := { x | a <= x ∧ x < b }

/-- `Ioc a b` is the left-open right-closed interval $(a, b]$. -/
@[to_dual existing (reorder := a b)]
/--
Definition of `Ioc` / `Ioc` 的定义

English:
definition Ioc
  signature: (a b : α)
  body: { x | a < x ∧ x <= b }

to_dual_insert_cast Ico := by simp only [and_comm]
to_dual_insert_cast Ioc := by simp only [and_comm]

中文:
定义 Ioc
  签名: (a b : α)
  定义体: { x | a < x ∧ x <= b }

to_dual_insert_cast Ico := by simp only [and_comm]
to_dual_insert_cast Ioc := by simp only [and_comm]
-/
def Ioc (a b : α) := { x | a < x ∧ x <= b }

to_dual_insert_cast Ico := by simp only [and_comm]
to_dual_insert_cast Ioc := by simp only [and_comm]

/--
theorem `mem_Ico` / 定理 `mem_Ico`

English:
theorem mem_Ico
  statement: x in Ico a b ↔ a <= x ∧ x < b
  proof: .rfl

中文:
定理 mem_Ico
  结论: x in Ico a b ↔ a <= x ∧ x < b
  证明: .rfl
-/
@[simp, grind =, push, to_dual none] theorem mem_Ico : x in Ico a b ↔ a <= x ∧ x < b := .rfl
/--
theorem `Ico_def` / 定理 `Ico_def`

English:
theorem Ico_def
  given: (a b : α)
  statement: { x | a <= x ∧ x < b } = Ico a b
  proof: rfl

中文:
定理 Ico_def
  条件: (a b : α)
  结论: { x | a <= x ∧ x < b } = Ico a b
  证明: rfl
-/
@[to_dual none] theorem Ico_def (a b : α) : { x | a <= x ∧ x < b } = Ico a b := rfl

/--
theorem `mem_Ioc` / 定理 `mem_Ioc`

English:
theorem mem_Ioc
  statement: x in Ioc a b ↔ a < x ∧ x <= b
  proof: .rfl

中文:
定理 mem_Ioc
  结论: x in Ioc a b ↔ a < x ∧ x <= b
  证明: .rfl
-/
@[simp, grind =, push, to_dual none] theorem mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b := .rfl
/--
theorem `Ioc_def` / 定理 `Ioc_def`

English:
theorem Ioc_def
  given: (a b : α)
  statement: { x | a < x ∧ x <= b } = Ioc a b
  proof: rfl

中文:
定理 Ioc_def
  条件: (a b : α)
  结论: { x | a < x ∧ x <= b } = Ioc a b
  证明: rfl
-/
@[to_dual none] theorem Ioc_def (a b : α) : { x | a < x ∧ x <= b } = Ioc a b := rfl

/-- `Icc a b` is the left-closed right-closed interval $[a, b]$. -/
@[to_dual self (reorder := a b)]
/--
Definition of `Icc` / `Icc` 的定义

English:
definition Icc
  signature: (a b : α)
  body: { x | a <= x ∧ x <= b }

to_dual_insert_cast Icc := by simp only [and_comm]

中文:
定义 Icc
  签名: (a b : α)
  定义体: { x | a <= x ∧ x <= b }

to_dual_insert_cast Icc := by simp only [and_comm]
-/
def Icc (a b : α) := { x | a <= x ∧ x <= b }

to_dual_insert_cast Icc := by simp only [and_comm]

/--
theorem `mem_Icc` / 定理 `mem_Icc`

English:
theorem mem_Icc
  statement: x in Icc a b ↔ a <= x ∧ x <= b
  proof: .rfl

中文:
定理 mem_Icc
  结论: x in Icc a b ↔ a <= x ∧ x <= b
  证明: .rfl
-/
@[simp, grind =, push, to_dual none] theorem mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b := .rfl
/--
theorem `Icc_def` / 定理 `Icc_def`

English:
theorem Icc_def
  given: (a b : α)
  statement: { x | a <= x ∧ x <= b } = Icc a b
  proof: rfl

中文:
定理 Icc_def
  条件: (a b : α)
  结论: { x | a <= x ∧ x <= b } = Icc a b
  证明: rfl
-/
@[to_dual none] theorem Icc_def (a b : α) : { x | a <= x ∧ x <= b } = Icc a b := rfl

/--
Definition of `OrdConnected` / `OrdConnected` 的定义

English:
class OrdConnected
  parameters: (s : Set α)
  axioms and operations (1):
    - out'(⦃x) : α⦄ (hx : x in s) ⦃y : α⦄ (hy : y in s) : Icc x y subseteq s

中文:
类 OrdConnected
  参数: (s : Set α)
  公理与运算 (1 个):
    - out'(⦃x) : α⦄ (hx : x in s) ⦃y : α⦄ (hy : y in s) : Icc x y subseteq s

Depends on / 依赖: OrdConnected, OrdConnected.mk
-/
class OrdConnected (s : Set α) : Prop where
  /-- `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x : α⦄ (hx : x in s) ⦃y : α⦄ (hy : y in s) : Icc x y subseteq s

attribute [to_dual self (reorder := out' (x y, hx hy))] OrdConnected.mk
attribute [to_dual self (reorder := x y, hx hy)] OrdConnected.out'

end Set
