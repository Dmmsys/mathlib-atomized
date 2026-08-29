/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Tactic.Variable

/-!
# Theory of quantales

Quantales are the non-commutative generalization of locales/frames and as such are linked
to point-free topology and order theory. Applications are found throughout logic,
quantum mechanics, and computer science (see e.g. [Vickers1989] and [Mulvey1986]).

The most general definition of quantale occurring in literature, is that a quantale is a semigroup
distributing over a complete sup-semilattice. In our definition below, we use the fact that
every complete sup-semilattice is in fact a complete lattice, and make constructs defined for
those immediately available. Another view could be to define a quantale as a complete idempotent
semiring, i.e. a complete semiring in which + and sup coincide. However, we will often encounter
additive quantales, i.e. quantales in which the semigroup operator is thought of as addition, in
which case the link with semirings will lead to confusion notationally.

In this file, we follow the basic definition set out on the wikipedia page on quantales,
using a mixin typeclass to make the special cases of unital, commutative, idempotent,
integral, and involutive quantales easier to add on later.

## Main definitions

* `IsQuantale` and `IsAddQuantale` : Typeclass mixin for a (additive) semigroup distributing
  over a complete lattice, i.e satisfying `x * (sSup s) = ⨆ y ∈ s, x * y` and
  `(sSup s) * y = ⨆ x ∈ s, x * y`;

* `Quantale` and `AddQuantale` : Structures serving as a typeclass alias, so one can write
  `variable? [Quantale α]` instead of `variable [Semigroup α] [CompleteLattice α] [IsQuantale α]`,
  and similarly for the additive variant.

* `leftMulResiduation`, `rightMulResiduation`, `leftAddResiduation`, `rightAddResiduation` :
  Defining the left- and right- residuations of the semigroup (see notation below).

* Finally, we provide basic distributivity laws for sSup into iSup and sup, monotonicity of
  the semigroup operator, and basic equivalences for left- and right-residuation.

## Notation

* `x ⇨ₗ y` : `sSup {z | z * x ≤ y}`, the `leftMulResiduation` of `y` over `x`;

* `x ⇨ᵣ y` : `sSup {z | x * z ≤ y}`, the `rightMulResiduation` of `y` over `x`;

## References

<https://en.wikipedia.org/wiki/Quantale>
<https://encyclopediaofmath.org/wiki/Quantale>
<https://ncatlab.org/nlab/show/quantale>

-/

@[expose] public section

open Function

/--
Definition of `IsAddQuantale` / `IsAddQuantale` 的定义

English:
class IsAddQuantale
  parameters: (α : Type*) [AddSemigroup α] [CompleteLattice α]
  axioms and operations (2):
    - add_sSup_distrib((x : α) (s : Set α)) : x + sSup s = ⨆ y in s, x + y
    - sSup_add_distrib((s : Set α) (y : α)) : sSup s + y = ⨆ x in s, x + y

中文:
类 IsAddQuantale
  参数: (α : 类型) [AddSemigroup α] [CompleteLattice α]
  公理与运算 (2 个):
    - add_sSup_distrib((x : α) (s : Set α)) : x + sSup s = ⨆ y in s, x + y
    - sSup_add_distrib((s : Set α) (y : α)) : sSup s + y = ⨆ x in s, x + y
-/
class IsAddQuantale (α : Type*) [AddSemigroup α] [CompleteLattice α] where
  /-- Addition is distributive over join in a quantale -/
  protected add_sSup_distrib (x : α) (s : Set α) : x + sSup s = ⨆ y in s, x + y
  /-- Addition is distributive over join in a quantale -/
  protected sSup_add_distrib (s : Set α) (y : α) : sSup s + y = ⨆ x in s, x + y

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[variable_alias]
/--
Definition of `AddQuantale` / `AddQuantale` 的定义

English:
structure AddQuantale
  parameters: (α : Type*)
  (no additional axioms)

中文:
结构 AddQuantale
  参数: (α : 类型)
  (无附加公理)
-/
structure AddQuantale (α : Type*)
  [AddSemigroup α] [CompleteLattice α] [IsAddQuantale α]

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[to_additive]
/--
Definition of `IsQuantale` / `IsQuantale` 的定义

English:
class IsQuantale
  parameters: (α : Type*) [Semigroup α] [CompleteLattice α]
  axioms and operations (2):
    - mul_sSup_distrib((x : α) (s : Set α)) : x * sSup s = ⨆ y in s, x * y
    - sSup_mul_distrib((s : Set α) (y : α)) : sSup s * y = ⨆ x in s, x * y

中文:
类 IsQuantale
  参数: (α : 类型) [Semigroup α] [CompleteLattice α]
  公理与运算 (2 个):
    - mul_sSup_distrib((x : α) (s : Set α)) : x * sSup s = ⨆ y in s, x * y
    - sSup_mul_distrib((s : Set α) (y : α)) : sSup s * y = ⨆ x in s, x * y
-/
class IsQuantale (α : Type*) [Semigroup α] [CompleteLattice α] where
  /-- Multiplication is distributive over join in a quantale -/
  protected mul_sSup_distrib (x : α) (s : Set α) : x * sSup s = ⨆ y in s, x * y
  /-- Multiplication is distributive over join in a quantale -/
  protected sSup_mul_distrib (s : Set α) (y : α) : sSup s * y = ⨆ x in s, x * y

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[variable_alias, to_additive]
/--
Definition of `Quantale` / `Quantale` 的定义

English:
structure Quantale
  parameters: (α : Type*)
  (no additional axioms)

中文:
结构 Quantale
  参数: (α : 类型)
  (无附加公理)
-/
structure Quantale (α : Type*)
  [Semigroup α] [CompleteLattice α] [IsQuantale α]

section

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι -> α}
variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

@[to_additive]
/--
theorem `mul_sSup_distrib` / 定理 `mul_sSup_distrib`

English:
theorem mul_sSup_distrib
  statement: x * sSup s = ⨆ y in s, x * y
  proof: IsQuantale.mul_sSup_distrib _ _

@[to_additive]

中文:
定理 mul_sSup_distrib
  结论: x * sSup s = ⨆ y in s, x * y
  证明: IsQuantale.mul_sSup_distrib _ _

@[to_additive]

Depends on / 依赖: IsQuantale, IsQuantale.mul_sSup_distrib, mul_sSup_distrib
-/
theorem mul_sSup_distrib : x * sSup s = ⨆ y in s, x * y := IsQuantale.mul_sSup_distrib _ _

@[to_additive]
/--
theorem `sSup_mul_distrib` / 定理 `sSup_mul_distrib`

English:
theorem sSup_mul_distrib
  statement: sSup s * x = ⨆ y in s, y * x
  proof: IsQuantale.sSup_mul_distrib _ _

中文:
定理 sSup_mul_distrib
  结论: sSup s * x = ⨆ y in s, y * x
  证明: IsQuantale.sSup_mul_distrib _ _

Depends on / 依赖: IsQuantale, IsQuantale.sSup_mul_distrib, sSup_mul_distrib
-/
theorem sSup_mul_distrib : sSup s * x = ⨆ y in s, y * x := IsQuantale.sSup_mul_distrib _ _

end

namespace AddQuantale

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι -> α}
variable [AddSemigroup α] [CompleteLattice α] [IsAddQuantale α]

/--
Definition of `leftAddResiduation` / `leftAddResiduation` 的定义

English:
definition leftAddResiduation
  signature: (x y : α)
  body: sSup {z | z + x <= y}

中文:
定义 leftAddResiduation
  签名: (x y : α)
  定义体: sSup {z | z + x <= y}
-/
def leftAddResiduation (x y : α) := sSup {z | z + x <= y}

/--
Definition of `rightAddResiduation` / `rightAddResiduation` 的定义

English:
definition rightAddResiduation
  signature: (x y : α)
  body: sSup {z | x + z <= y}

@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftAddResiduation

@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightAddResiduation

中文:
定义 rightAddResiduation
  签名: (x y : α)
  定义体: sSup {z | x + z <= y}

@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftAddResiduation

@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightAddResiduation
-/
def rightAddResiduation (x y : α) := sSup {z | x + z <= y}

@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftAddResiduation

@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightAddResiduation

end AddQuantale

namespace Quantale

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι -> α}
variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

/-- Left- and right-residuation operators on a quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ₗ z ↔ x * y ≤ z` or alternatively `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive existing]
/--
Definition of `leftMulResiduation` / `leftMulResiduation` 的定义

English:
definition leftMulResiduation
  signature: (x y : α)
  body: sSup {z | z * x <= y}

中文:
定义 leftMulResiduation
  签名: (x y : α)
  定义体: sSup {z | z * x <= y}
-/
def leftMulResiduation (x y : α) := sSup {z | z * x <= y}

/-- Left- and right- residuation operators on a quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ᵣ z ↔ y * x ≤ z` or alternatively `x ⇨ₗ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive existing]
/--
Definition of `rightMulResiduation` / `rightMulResiduation` 的定义

English:
definition rightMulResiduation
  signature: (x y : α)
  body: sSup {z | x * z <= y}

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ₗ " => leftMulResiduation

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ᵣ " => rightMulResiduation

@[to_additive]

中文:
定义 rightMulResiduation
  签名: (x y : α)
  定义体: sSup {z | x * z <= y}

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ₗ " => leftMulResiduation

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ᵣ " => rightMulResiduation

@[to_additive]
-/
def rightMulResiduation (x y : α) := sSup {z | x * z <= y}

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ₗ " => leftMulResiduation

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ᵣ " => rightMulResiduation

@[to_additive]
/--
theorem `mul_iSup_distrib` / 定理 `mul_iSup_distrib`

English:
theorem mul_iSup_distrib
  statement: x * ⨆ i, f i = ⨆ i, x * f i
  proof: by
  rw [iSup]; rw [mul_sSup_distrib]; rw [iSup_range]

@[to_additive]

中文:
定理 mul_iSup_distrib
  结论: x * ⨆ i, f i = ⨆ i, x * f i
  证明: by
  rw [iSup]; rw [mul_sSup_distrib]; rw [iSup_range]

@[to_additive]

Depends on / 依赖: iSup_range, mul_sSup_distrib
-/
theorem mul_iSup_distrib : x * ⨆ i, f i = ⨆ i, x * f i := by
  rw [iSup]; rw [mul_sSup_distrib]; rw [iSup_range]

@[to_additive]
/--
theorem `iSup_mul_distrib` / 定理 `iSup_mul_distrib`

English:
theorem iSup_mul_distrib
  statement: (⨆ i, f i) * x = ⨆ i, f i * x
  proof: by
  rw [iSup]; rw [sSup_mul_distrib]; rw [iSup_range]

@[to_additive]

中文:
定理 iSup_mul_distrib
  结论: (⨆ i, f i) * x = ⨆ i, f i * x
  证明: by
  rw [iSup]; rw [sSup_mul_distrib]; rw [iSup_range]

@[to_additive]

Depends on / 依赖: iSup_range, sSup_mul_distrib
-/
theorem iSup_mul_distrib : (⨆ i, f i) * x = ⨆ i, f i * x := by
  rw [iSup]; rw [sSup_mul_distrib]; rw [iSup_range]

@[to_additive]
/--
theorem `mul_sup_distrib` / 定理 `mul_sup_distrib`

English:
theorem mul_sup_distrib
  statement: x * (y ⊔ z) = (x * y) ⊔ (x * z)
  proof: by
  rw [← iSup_pair]; rw [← sSup_pair]; rw [mul_sSup_distrib]

@[to_additive]

中文:
定理 mul_sup_distrib
  结论: x * (y ⊔ z) = (x * y) ⊔ (x * z)
  证明: by
  rw [← iSup_pair]; rw [← sSup_pair]; rw [mul_sSup_distrib]

@[to_additive]

Depends on / 依赖: iSup_pair, mul_sSup_distrib, sSup_pair
-/
theorem mul_sup_distrib : x * (y ⊔ z) = (x * y) ⊔ (x * z) := by
  rw [← iSup_pair]; rw [← sSup_pair]; rw [mul_sSup_distrib]

@[to_additive]
/--
theorem `sup_mul_distrib` / 定理 `sup_mul_distrib`

English:
theorem sup_mul_distrib
  statement: (x ⊔ y) * z = (x * z) ⊔ (y * z)
  proof: by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _)]; rw [← sSup_pair]; rw [sSup_mul_distrib]

@[to_additive]

中文:
定理 sup_mul_distrib
  结论: (x ⊔ y) * z = (x * z) ⊔ (y * z)
  证明: by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _)]; rw [← sSup_pair]; rw [sSup_mul_distrib]

@[to_additive]

Depends on / 依赖: iSup_pair, sSup_mul_distrib, sSup_pair
-/
theorem sup_mul_distrib : (x ⊔ y) * z = (x * z) ⊔ (y * z) := by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _)]; rw [← sSup_pair]; rw [sSup_mul_distrib]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulLeftMono α
  body: by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← mul_sup_distrib, sup_of_le_left]

@[to_additive]

中文:
实例 :
  签名: MulLeftMono α
  定义体: by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← mul_sup_distrib, sup_of_le_left]

@[to_additive]

Depends on / 依赖: left_eq_sup, mul_sup_distrib, sup_of_le_left
-/
instance : MulLeftMono α where
  elim := by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← mul_sup_distrib, sup_of_le_left]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRightMono α
  body: by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← sup_mul_distrib, sup_of_le_left]

@[to_additive]

中文:
实例 :
  签名: MulRightMono α
  定义体: by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← sup_mul_distrib, sup_of_le_left]

@[to_additive]

Depends on / 依赖: left_eq_sup, sup_mul_distrib, sup_of_le_left
-/
instance : MulRightMono α where
  elim := by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← sup_mul_distrib, sup_of_le_left]

@[to_additive]
/--
theorem `leftMulResiduation_le_iff_mul_le` / 定理 `leftMulResiduation_le_iff_mul_le`

English:
theorem leftMulResiduation_le_iff_mul_le
  statement: x <= y ⇨ₗ z ↔ x * y <= z where
  proof: by
    grw [h1]
    simp_all only [leftMulResiduation, sSup_mul_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

@[to_additive]

中文:
定理 leftMulResiduation_le_iff_mul_le
  结论: x <= y ⇨ₗ z ↔ x * y <= z where
  证明: by
    grw [h1]
    simp_all only [leftMulResiduation, sSup_mul_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

@[to_additive]

Depends on / 依赖: Set.mem_ofPred_eq, iSup_le_iff, implies_true, le_sSup, leftMulResiduation, mem_ofPred_eq, sSup_mul_distrib
-/
theorem leftMulResiduation_le_iff_mul_le : x <= y ⇨ₗ z ↔ x * y <= z where
  mp h1 := by
    grw [h1]
    simp_all only [leftMulResiduation, sSup_mul_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

@[to_additive]
/--
theorem `rightMulResiduation_le_iff_mul_le` / 定理 `rightMulResiduation_le_iff_mul_le`

English:
theorem rightMulResiduation_le_iff_mul_le
  statement: x <= y ⇨ᵣ z ↔ y * x <= z where
  proof: by
    grw [h1]
    simp_all only [rightMulResiduation, mul_sSup_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

中文:
定理 rightMulResiduation_le_iff_mul_le
  结论: x <= y ⇨ᵣ z ↔ y * x <= z where
  证明: by
    grw [h1]
    simp_all only [rightMulResiduation, mul_sSup_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

Depends on / 依赖: Set.mem_ofPred_eq, iSup_le_iff, implies_true, le_sSup, mem_ofPred_eq, mul_sSup_distrib, rightMulResiduation
-/
theorem rightMulResiduation_le_iff_mul_le : x <= y ⇨ᵣ z ↔ y * x <= z where
  mp h1 := by
    grw [h1]
    simp_all only [rightMulResiduation, mul_sSup_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

section Zero

variable {α : Type*} [Semigroup α] [CompleteLattice α] [IsQuantale α]
variable {x : α}

@[to_additive (attr := simp)]
/--
theorem `bot_mul` / 定理 `bot_mul`

English:
theorem bot_mul
  statement: ⊥ * x = ⊥
  proof: by
  rw [← sSup_empty]; rw [sSup_mul_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

@[to_additive (attr := simp)]

中文:
定理 bot_mul
  结论: ⊥ * x = ⊥
  证明: by
  rw [← sSup_empty]; rw [sSup_mul_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_empty_iff_false, iSup_bot, iSup_neg, mem_empty_iff_false, not_false_eq_true, sSup_empty, sSup_mul_distrib
-/
theorem bot_mul : ⊥ * x = ⊥ := by
  rw [← sSup_empty]; rw [sSup_mul_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

@[to_additive (attr := simp)]
/--
theorem `mul_bot` / 定理 `mul_bot`

English:
theorem mul_bot
  statement: x * ⊥ = ⊥
  proof: by
  rw [← sSup_empty]; rw [mul_sSup_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

中文:
定理 mul_bot
  结论: x * ⊥ = ⊥
  证明: by
  rw [← sSup_empty]; rw [mul_sSup_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

Depends on / 依赖: Set.mem_empty_iff_false, iSup_bot, iSup_neg, mem_empty_iff_false, mul_sSup_distrib, not_false_eq_true, sSup_empty
-/
theorem mul_bot : x * ⊥ = ⊥ := by
  rw [← sSup_empty]; rw [mul_sSup_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

end Zero

end Quantale
