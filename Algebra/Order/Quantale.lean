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

/-- An additive quantale is an additive semigroup distributing over a complete lattice. -/
/-
**IsAddQuantale** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [AddSemigroup α] → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive quantale is an additive semigroup distributing over a complete latti
ce.
-/
class IsAddQuantale (α : Type*) [AddSemigroup α] [CompleteLattice α] where
  /-- Addition is distributive over join in a quantale -/
  protected add_sSup_distrib (x : α) (s : Set α) : x + sSup s = ⨆ y ∈ s, x + y
  /-- Addition is distributive over join in a quantale -/
  protected sSup_add_distrib (s : Set α) (y : α) : sSup s + y = ⨆ x ∈ s, x + y

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[variable_alias]
/-
**AddQuantale** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [inst : AddSemigroup α] → [inst_1 : CompleteLattice α] → 
[IsAddQuantale α] → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quantale is a semigroup distributing over a complete lattice.
-/
structure AddQuantale (α : Type*)
  [AddSemigroup α] [CompleteLattice α] [IsAddQuantale α]

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[to_additive]
/-
**IsQuantale** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Semigroup α] → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quantale is a semigroup distributing over a complete lattice.
-/
class IsQuantale (α : Type*) [Semigroup α] [CompleteLattice α] where
  /-- Multiplication is distributive over join in a quantale -/
  protected mul_sSup_distrib (x : α) (s : Set α) : x * sSup s = ⨆ y ∈ s, x * y
  /-- Multiplication is distributive over join in a quantale -/
  protected sSup_mul_distrib (s : Set α) (y : α) : sSup s * y = ⨆ x ∈ s, x * y

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[variable_alias, to_additive]
/-
**Quantale** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [inst : Semigroup α] → [inst_1 : CompleteLattice α] → [Is
Quantale α] → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quantale is a semigroup distributing over a complete lattice.
-/
structure Quantale (α : Type*)
  [Semigroup α] [CompleteLattice α] [IsQuantale α]

section

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

@[to_additive]
/-
**mul_sSup_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_sSup_distrib : x * sSup s = ⨆ y in s, x * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuantale.mul_sSup_distrib`：∀ {α : Type u_1} {inst : Semigroup α} {inst
_1 : CompleteLattice α} [self : IsQuantale α] (x : α) (s : Set α),   x * sSup s 
= ⨆ y ∈ s, x * y
-/
theorem mul_sSup_distrib : x * sSup s = ⨆ y ∈ s, x * y := IsQuantale.mul_sSup_distrib _ _

@[to_additive]
/-
**sSup_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_mul_distrib : sSup s * x = ⨆ y in s, y * x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuantale.sSup_mul_distrib`：∀ {α : Type u_1} {inst : Semigroup α} {inst
_1 : CompleteLattice α} [self : IsQuantale α] (s : Set α) (y : α),   sSup s * y 
= ⨆ x ∈ s, x * y
-/
theorem sSup_mul_distrib : sSup s * x = ⨆ y ∈ s, y * x := IsQuantale.sSup_mul_distrib _ _

end

namespace AddQuantale

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [AddSemigroup α] [CompleteLattice α] [IsAddQuantale α]

/-- Left- and right- residuation operators on an additive quantale are similar
to the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ₗ z ↔ x + y ≤ z` or alternatively `x ⇨ₗ y = sSup { z | z + x ≤ y }`. -/
/-
**AddQuantale.leftAddResiduation** 是 Mathlib 中的一个定义，位于命名空间 `AddQuantale`。
形式化陈述：leftAddResiduation (x y : α)
参数：x y : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left- and right- residuation operators on an additive quantale are similar
to the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ₗ z ↔ x + y ≤ z` or alternatively `x ⇨ₗ y = sSup { z | z + x ≤ y }`
.
-/
def leftAddResiduation (x y : α) := sSup {z | z + x ≤ y}

/-- Left- and right- residuation operators on an additive quantale are similar
to the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ᵣ z ↔ y + x ≤ z` or alternatively `x ⇨ₗ y = sSup { z | x + z ≤ y }`." -/
def rightAddResiduation (x y : α) := sSup {z | x + z ≤ y}

@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftAddResiduation

@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightAddResiduation

end AddQuantale

namespace Quantale

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

/-- Left- and right-residuation operators on a quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ₗ z ↔ x * y ≤ z` or alternatively `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive existing]
def leftMulResiduation (x y : α) := sSup {z | z * x ≤ y}

/-- Left- and right- residuation operators on a quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ᵣ z ↔ y * x ≤ z` or alternatively `x ⇨ₗ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive existing]
def rightMulResiduation (x y : α) := sSup {z | x * z ≤ y}

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ₗ " => leftMulResiduation

@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ᵣ " => rightMulResiduation

@[to_additive]
theorem mul_iSup_distrib : x * ⨆ i, f i = ⨆ i, x * f i := by
  rw [iSup, mul_sSup_distrib, iSup_range]

@[to_additive]
theorem iSup_mul_distrib : (⨆ i, f i) * x = ⨆ i, f i * x := by
  rw [iSup, sSup_mul_distrib, iSup_range]

@[to_additive]
theorem mul_sup_distrib : x * (y ⊔ z) = (x * y) ⊔ (x * z) := by
  rw [← iSup_pair, ← sSup_pair, mul_sSup_distrib]

@[to_additive]
theorem sup_mul_distrib : (x ⊔ y) * z = (x * z) ⊔ (y * z) := by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _), ← sSup_pair, sSup_mul_distrib]

@[to_additive]
instance : MulLeftMono α where
  elim := by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← mul_sup_distrib, sup_of_le_left]

@[to_additive]
instance : MulRightMono α where
  elim := by
    intro _ _ _; simp only; intro
    rwa [← left_eq_sup, ← sup_mul_distrib, sup_of_le_left]

@[to_additive]
theorem leftMulResiduation_le_iff_mul_le : x ≤ y ⇨ₗ z ↔ x * y ≤ z where
  mp h1 := by
    grw [h1]
    simp_all only [leftMulResiduation, sSup_mul_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

@[to_additive]
theorem rightMulResiduation_le_iff_mul_le : x ≤ y ⇨ᵣ z ↔ y * x ≤ z where
  mp h1 := by
    grw [h1]
    simp_all only [rightMulResiduation, mul_sSup_distrib, Set.mem_ofPred_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

section Zero

variable {α : Type*} [Semigroup α] [CompleteLattice α] [IsQuantale α]
variable {x : α}

@[to_additive (attr := simp)]
theorem bot_mul : ⊥ * x = ⊥ := by
  rw [← sSup_empty, sSup_mul_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

@[to_additive (attr := simp)]
theorem mul_bot : x * ⊥ = ⊥ := by
  rw [← sSup_empty, mul_sSup_distrib]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, sSup_empty]

end Zero

end Quantale

