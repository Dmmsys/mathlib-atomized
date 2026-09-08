/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `Ordered[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `CovariantClass` and
`ContravariantClass`:

* `CovariantClass` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `ContravariantClass` models the implication `a * b < a * c → b < c`.

Since `Co(ntra)variantClass` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`IsOrdered[...]` typeclass of your liking.  After that, you convert the typeclass,
say `[IsOrderedCancelMonoid M]`, into whichever typeclasses, e.g.
`[CovariantClass M M (Function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several `Co(ntra)variantClass` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[CovariantClass M M (*) (≤)] [ContravariantClass M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `CovariantClass` uses the `(≤)`-relation, while
`ContravariantClass` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[Semigroup α] [PartialOrder α] [ContravariantClass α α (*) (≤)] → LeftCancelSemigroup α
```
holds -- note the `Co*ntra*` assumption on the `(≤)`-relation.

## Formalization notes

We stick to the convention of using `Function.swap (*)` (or `Function.swap (+)`), for the
typeclass assumptions, since `Function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use.

## TODO

This is unergonomic. Inline in `MulLeftMono` and friends.
-/

@[expose] public section


-- TODO: convert `ExistsMulOfLE`, `ExistsAddOfLE`?
-- TODO: relationship with `Con/AddCon`
-- TODO: include equivalence of `LeftCancelSemigroup` with
-- `Semigroup PartialOrder ContravariantClass α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)
variable (M N)

/-- `Covariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `CovariantClass` doc-string for its meaning. -/
/-
**Covariant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Covariant : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Covariant` is useful to formulate succinctly statements about the interactions 
between an
action of a Type on another one and a relation on the acted-upon Type.

See the `CovariantClass` doc-string for its meaning.
-/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `Contravariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `ContravariantClass` doc-string for its meaning. -/
/-
**Contravariant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Contravariant : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Contravariant` is useful to formulate succinctly statements about the interacti
ons between an
action of a Type on another one and a relation on the acted-upon Type.

See the `ContravariantClass` doc-string for its meaning.
-/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`CovariantClass` says that "the action `μ` preserves the relation `r`."

More precisely, the `CovariantClass` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `CovariantClass.elim m h : r (μ m n₁) (μ m n₂)`.
-/
/-
**CovariantClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → (N : Type u_2) → (M → N → N) → (N → N → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, infor
mally, the
`CovariantClass` says that "the action `μ` preserves the relation `r`."

More precisely, the `CovariantClass` is a class taking two Types `M N`, together
 with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is t
he assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
 pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `CovariantClass.elim m h : r (μ m n₁) (μ m n₂
)`.
-/
class CovariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
  `(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)` -/
  protected elim : Covariant M N μ r

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`ContravariantClass` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `ContravariantClass` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `ContravariantClass.elim m h : r n₁ n₂`.
-/
/-
**ContravariantClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → (N : Type u_2) → (M → N → N) → (N → N → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, infor
mally, the
`ContravariantClass` says that "if the result of the action `μ` on a pair satisf
ies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `ContravariantClass` is a class taking two Types `M N`, toge
ther with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `e
lim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r
` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then,
 the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `ContravariantClass.elim m h : r 
n₁ n₂`.
-/
class ContravariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
  pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
  `r` also holds for the pair `(n₁, n₂)`. -/
  protected elim : Contravariant M N μ r

/-- Typeclass for monotonicity of multiplication on the left,
namely `b₁ ≤ b₂ → a * b₁ ≤ a * b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedMonoid`. -/
/-
**MulLeftMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulLeftMono [Mul M] [LE M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of multiplication on the left,
namely `b₁ ≤ b₂ → a * b₁ ≤ a * b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedMonoid`.
-/
abbrev MulLeftMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (· * ·) (· ≤ ·)

/-- Typeclass for monotonicity of multiplication on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedMonoid`. -/
/-
**MulRightMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulRightMono [Mul M] [LE M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of multiplication on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedMonoid`.
-/
abbrev MulRightMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· ≤ ·)

/-- Typeclass for monotonicity of addition on the left,
namely `b₁ ≤ b₂ → a + b₁ ≤ a + b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedAddMonoid`. -/
/-
**AddLeftMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddLeftMono [Add M] [LE M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of addition on the left,
namely `b₁ ≤ b₂ → a + b₁ ≤ a + b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedAddMonoid`.
-/
abbrev AddLeftMono [Add M] [LE M] : Prop :=
  CovariantClass M M (· + ·) (· ≤ ·)

/-- Typeclass for monotonicity of addition on the right,
namely `a₁ ≤ a₂ → a₁ + b ≤ a₂ + b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedAddMonoid`. -/
/-
**AddRightMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddRightMono [Add M] [LE M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of addition on the right,
namely `a₁ ≤ a₂ → a₁ + b ≤ a₂ + b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedAddMonoid`.
-/
abbrev AddRightMono [Add M] [LE M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive existing] MulLeftMono MulRightMono

/-- Typeclass for monotonicity of multiplication on the left,
namely `b₁ < b₂ → a * b₁ < a * b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedMonoid`. -/
/-
**MulLeftStrictMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulLeftStrictMono [Mul M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of multiplication on the left,
namely `b₁ < b₂ → a * b₁ < a * b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedMonoid`.
-/
abbrev MulLeftStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (· * ·) (· < ·)

/-- Typeclass for monotonicity of multiplication on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedMonoid`. -/
/-
**MulRightStrictMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulRightStrictMono [Mul M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of multiplication on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedMonoid`.
-/
abbrev MulRightStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· < ·)

/-- Typeclass for monotonicity of addition on the left,
namely `b₁ < b₂ → a + b₁ < a + b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedAddMonoid`. -/
/-
**AddLeftStrictMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddLeftStrictMono [Add M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of addition on the left,
namely `b₁ < b₂ → a + b₁ < a + b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedAddMonoid`.
-/
abbrev AddLeftStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (· + ·) (· < ·)

/-- Typeclass for monotonicity of addition on the right,
namely `a₁ < a₂ → a₁ + b < a₂ + b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedAddMonoid`. -/
/-
**AddRightStrictMono** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddRightStrictMono [Add M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of addition on the right,
namely `a₁ < a₂ → a₁ + b < a₂ + b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedAddMonoid`.
-/
abbrev AddRightStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftStrictMono MulRightStrictMono

/-- Typeclass for strict reverse monotonicity of multiplication on the left,
namely `a * b₁ < a * b₂ → b₁ < b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedMonoid`. -/
/-
**MulLeftReflectLT** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulLeftReflectLT [Mul M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of multiplication on the left,
namely `a * b₁ < a * b₂ → b₁ < b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedMonoid`.
-/
abbrev MulLeftReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (· * ·) (· < ·)

/-- Typeclass for strict reverse monotonicity of multiplication on the right,
namely `a₁ * b < a₂ * b → a₁ < a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedMonoid`. -/
/-
**MulRightReflectLT** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulRightReflectLT [Mul M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of multiplication on the right,
namely `a₁ * b < a₂ * b → a₁ < a₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedMonoid`.
-/
abbrev MulRightReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (swap (· * ·)) (· < ·)

/-- Typeclass for strict reverse monotonicity of addition on the left,
namely `a + b₁ < a + b₂ → b₁ < b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedAddMonoid`. -/
/-
**AddLeftReflectLT** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddLeftReflectLT [Add M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of addition on the left,
namely `a + b₁ < a + b₂ → b₁ < b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedAddMonoid`.
-/
abbrev AddLeftReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (· + ·) (· < ·)

/-- Typeclass for strict reverse monotonicity of addition on the right,
namely `a₁ * b < a₂ * b → a₁ < a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedAddMonoid`. -/
/-
**AddRightReflectLT** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddRightReflectLT [Add M] [LT M] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of addition on the right,
namely `a₁ * b < a₂ * b → a₁ < a₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedAddMonoid`.
-/
abbrev AddRightReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftReflectLT MulRightReflectLT

/-- Typeclass for reverse monotonicity of multiplication on the left,
namely `a * b₁ ≤ a * b₂ → b₁ ≤ b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedCancelMonoid`. -/
/-
**MulLeftReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Mul M] → [LE M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of multiplication on the left,
namely `a * b₁ ≤ a * b₂ → b₁ ≤ b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedCancelMonoid`.
-/
class MulLeftReflectLE [Mul M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_mul_le_mul_left'` instead. -/
  protected le_of_mul_le_mul_left' {a b₁ b₂ : M} : a * b₁ ≤ a * b₂ → b₁ ≤ b₂

/-- Typeclass for reverse monotonicity of multiplication on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedCancelMonoid`. -/
/-
**MulRightReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Mul M] → [LE M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of multiplication on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedCancelMonoid`.
-/
class MulRightReflectLE [Mul M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_mul_le_mul_right'` instead. -/
  protected le_of_mul_le_mul_right' {b a₁ a₂ : M} : a₁ * b ≤ a₂ * b → a₁ ≤ a₂

/-- Typeclass for reverse monotonicity of addition on the left,
namely `a + b₁ ≤ a + b₂ → b₁ ≤ b₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedCancelAddMonoid`. -/
/-
**AddLeftReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Add M] → [LE M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of addition on the left,
namely `a + b₁ ≤ a + b₂ → b₁ ≤ b₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedCancelAddMonoid`.
-/
class AddLeftReflectLE [Add M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_add_le_add_left` instead. -/
  protected le_of_add_le_add_left {a b₁ b₂ : M} : a + b₁ ≤ a + b₂ → b₁ ≤ b₂

/-- Typeclass for reverse monotonicity of addition on the right,
namely `a₁ + b ≤ a₂ + b → a₁ ≤ a₂`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedCancelAddMonoid`. -/
/-
**AddRightReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Add M] → [LE M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of addition on the right,
namely `a₁ + b ≤ a₂ + b → a₁ ≤ a₂`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedCancelAddMonoid`.
-/
class AddRightReflectLE [Add M] [LE M] : Prop where
  /-- Do not use this. Use `le_of_add_le_add_right` instead. -/
  protected le_of_add_le_add_right {b a₁ a₂ : M} : a₁ + b ≤ a₂ + b → a₁ ≤ a₂

attribute [to_additive existing] MulLeftReflectLE MulRightReflectLE

variable {M N μ r} in
/-
**rel_iff_cov'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contravariant M N μ r) 
{m : M} {a b : N} : r (μ m a) (μ m b) ↔ r a b
参数：hcov : Covariant M N μ r；hcontra : Contravariant M N μ r。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contravariant M N μ r) {m : M}
    {a b : N} : r (μ m a) (μ m b) ↔ r a b :=
  ⟨hcontra m, hcov m⟩
/-
**rel_iff_cov** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) 
{a b : N} : r (μ m a) (μ m b) ↔ r a b
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov'`：rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contrav
ariant M N μ r) {m : M} {a b : N} : r (μ m a) (μ m b) ↔ r a b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  rel_iff_cov' CovariantClass.elim ContravariantClass.elim

section flip

variable {M N μ r}

/-
**Covariant.flip** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r)
参数：h : Covariant M N μ r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) :=
  fun a _ _ ↦ h a
/-
**Contravariant.flip** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip
 r)
参数：h : Contravariant M N μ r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a _ _ ↦ h a

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

/-
**act_rel_act_of_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b)
参数：m : M；ab : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab

@[to_additive]
/-
**Group.covariant_iff_contravariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.covariant_iff_contravariant [Group N] : Covariant N N (· * ·) r ↔ Co
ntravariant N N (· * ·) r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem Group.covariant_iff_contravariant [Group N] :
    Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine ⟨fun h a b c bc ↦ ?_, fun h a b c bc ↦ ?_⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] :
    ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩

@[to_additive]
/-
**Group.mulLeftReflectLE_of_mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.mulLeftReflectLE_of_mulLeftMono [Group N] [LE N] [MulLeftMono N] : M
ulLeftReflectLE N where le_of_mul_le_mul_left'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.covariant_iff_contravariant`：Group.covariant_iff_contravariant [Gr
oup N] : Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance Group.mulLeftReflectLE_of_mulLeftMono [Group N] [LE N] [MulLeftMono N] :
    MulLeftReflectLE N where
  le_of_mul_le_mul_left' := Group.covariant_iff_contravariant.mp CovariantClass.elim _

@[to_additive]
/-
**Group.mulLeftReflectLT_of_mulLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.mulLeftReflectLT_of_mulLeftStrictMono [Group N] [LT N] [MulLeftStric
tMono N] : MulLeftReflectLT N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
-/
theorem Group.mulLeftReflectLT_of_mulLeftStrictMono [Group N] [LT N]
    [MulLeftStrictMono N] : MulLeftReflectLT N :=
  inferInstance

@[to_additive]
/-
**Group.covariant_swap_iff_contravariant_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.covariant_swap_iff_contravariant_swap [Group N] : Covariant N N (swa
p (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine ⟨fun h a b c bc ↦ ?_, fun h a b c bc ↦ ?_⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc


@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩

@[to_additive]
/-
**Group.mulRightReflectLE_of_mulRightMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.mulRightReflectLE_of_mulRightMono [Group N] [LE N] [MulRightMono N] 
: MulRightReflectLE N where le_of_mul_le_mul_right'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.covariant_swap_iff_contravariant_swap`：Group.covariant_swap_iff_co
ntravariant_swap [Group N] : Covariant N N (swap (· * ·)) r ↔ Contravariant N N 
(swap (· * ·)) r
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance Group.mulRightReflectLE_of_mulRightMono [Group N] [LE N] [MulRightMono N] :
    MulRightReflectLE N where
  le_of_mul_le_mul_right' := Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim _

@[to_additive]
/-
**Group.mulRightReflectLT_of_mulRightStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.mulRightReflectLT_of_mulRightStrictMono [Group N] [LT N] [MulRightSt
rictMono N] : MulRightReflectLT N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
-/
theorem Group.mulRightReflectLT_of_mulRightStrictMono [Group N] [LT N] [MulRightStrictMono N] :
    MulRightReflectLT N :=
  inferInstance


section Trans

variable [IsTrans N r] (m : M) {a b c : N}

--  Lemmas with 3 elements.
/-
**act_rel_of_rel_of_act_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c
参数：ab : r a b；rl : r (μ m b) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `act_rel_act_of_rel`：act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : 
r (μ m a) (μ m b)
-/
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  _root_.trans (act_rel_act_of_rel m ab) rl
/-
**rel_act_of_rel_of_rel_act** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b)
参数：ab : r a b；rr : r c (μ m a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `act_rel_act_of_rel`：act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : 
r (μ m a) (μ m b)
-/
theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  _root_.trans rr (act_rel_act_of_rel _ ab)

end Trans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [i : CovariantClass N N mu r]
  [i' : CovariantClass N N (swap mu) r] {a b c d : N}

/-
**act_rel_act_of_rel_of_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d)
参数：ab : r a b；cd : r c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `act_rel_act_of_rel`：act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : 
r (μ m a) (μ m b)
-/
theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

/-
**rel_of_act_rel_act** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b
参数：m : M；ab : r (μ m a) (μ m b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab

section Trans

variable [IsTrans N r] (m : M) {a b c : N}

--  Lemmas with 3 elements.
/-
**act_rel_of_act_rel_of_rel_act_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m 
c)) : r (μ m a) c
参数：ab : r (μ m a) b；rl : r (μ m b) (μ m c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `rel_of_act_rel_act`：rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a)
 (μ m b)) : r a b
-/
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c :=
  _root_.trans ab (rel_of_act_rel_act m rl)
/-
**rel_act_of_act_rel_act_of_rel_act** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m 
c)) : r a (μ m c)
参数：ab : r (μ m a) (μ m b)；rr : r b (μ m c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `rel_of_act_rel_act`：rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a)
 (μ m b)) : r a b
-/
theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) :=
  _root_.trans (rel_of_act_rel_act m ab) rr

end Trans

end Contravariant

section Monotone

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]
variable {f : N → α}

/-- The partial application of a constant to a covariant operator is monotone. -/
/-
**Covariant.monotone_of_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Covariant.monotone_of_const [CovariantClass M N μ (· <= ·)] (m : M) : Mono
tone (μ m)
参数：· <= ·；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r

--- 原说明 ---
The partial application of a constant to a covariant operator is monotone.
-/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) :=
  fun _ _ ↦ CovariantClass.elim m

/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (m + n))`. -/
/-
**Monotone.covariant_of_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.covariant_of_const [CovariantClass M N μ (· <= ·)] (hf : Monotone
 f) (m : M) : Monotone (f <| μ m ·)
参数：· <= ·；hf : Monotone f；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Covariant.monotone_of_const`：Covariant.monotone_of_const [CovariantClass
 M N μ (· <= ·)] (m : M) : Monotone (μ m)

--- 原说明 ---
A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (m +
 n))`.
-/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone (f <| μ m ·) :=
  hf.comp (Covariant.monotone_of_const m)

/-- Same as `Monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (n + m))`. -/
/-
**Monotone.covariant_of_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.covariant_of_const' {μ : N -> N -> N} [CovariantClass N N (swap μ
) (· <= ·)] (hf : Monotone f) (m : N) : Monotone (f <| μ · m)
参数：swap μ；· <= ·；hf : Monotone f；m : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.covariant_of_const`：Monotone.covariant_of_const [CovariantClass
 M N μ (· <= ·)] (hf : Monotone f) (m : M) : Monotone (f <| μ m ·)

--- 原说明 ---
Same as `Monotone.covariant_of_const`, but with the constant on the other side o
f
the operator.  E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (n + m))`.
-/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Monotone f) (m : N) : Monotone (f <| μ · m) :=
  Monotone.covariant_of_const (μ := swap μ) hf m

/-- Dual of `Monotone.covariant_of_const` -/
/-
**Antitone.covariant_of_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.covariant_of_const [CovariantClass M N μ (· <= ·)] (hf : Antitone
 f) (m : M) : Antitone (f <| μ m ·)
参数：· <= ·；hf : Antitone f；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `Covariant.monotone_of_const`：Covariant.monotone_of_const [CovariantClass
 M N μ (· <= ·)] (m : M) : Monotone (μ m)

--- 原说明 ---
Dual of `Monotone.covariant_of_const`
-/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone (f <| μ m ·) :=
  hf.comp_monotone <| Covariant.monotone_of_const m

/-- Dual of `Monotone.covariant_of_const'` -/
/-
**Antitone.covariant_of_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.covariant_of_const' {μ : N -> N -> N} [CovariantClass N N (swap μ
) (· <= ·)] (hf : Antitone f) (m : N) : Antitone (f <| μ · m)
参数：swap μ；· <= ·；hf : Antitone f；m : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.covariant_of_const`：Antitone.covariant_of_const [CovariantClass
 M N μ (· <= ·)] (hf : Antitone f) (m : M) : Antitone (f <| μ m ·)

--- 原说明 ---
Dual of `Monotone.covariant_of_const'`
-/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Antitone f) (m : N) : Antitone (f <| μ · m) :=
  Antitone.covariant_of_const (μ := swap μ) hf m

end Monotone

/-
**covariant_le_of_covariant_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covariant_le_of_covariant_lt [PartialOrder N] : Covariant M N μ (· < ·) ->
 Covariant M N μ (· <= ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le
/-
**covariantClass_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covariantClass_le_of_lt [PartialOrder N] [CovariantClass M N μ (· < ·)] : 
CovariantClass M N μ (· <= ·)
参数：· < ·。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `covariant_le_of_covariant_lt`：covariant_le_of_covariant_lt [PartialOrder
 N] : Covariant M N μ (· < ·) -> Covariant M N μ (· <= ·)
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem covariantClass_le_of_lt [PartialOrder N] [CovariantClass M N μ (· < ·)] :
    CovariantClass M N μ (· ≤ ·) := ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

@[to_additive]
/-
**mulLeftMono_of_mulLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftMono_of_mulLeftStrictMono (M) [Mul M] [PartialOrder M] [MulLeftStri
ctMono M] : MulLeftMono M
参数：M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `covariantClass_le_of_lt`：covariantClass_le_of_lt [PartialOrder N] [Covar
iantClass M N μ (· < ·)] : CovariantClass M N μ (· <= ·)
-/
theorem mulLeftMono_of_mulLeftStrictMono (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M] :
    MulLeftMono M := covariantClass_le_of_lt _ _ _

@[to_additive]
/-
**mulRightMono_of_mulRightStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightMono_of_mulRightStrictMono (M) [Mul M] [PartialOrder M] [MulRightS
trictMono M] : MulRightMono M
参数：M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `covariantClass_le_of_lt`：covariantClass_le_of_lt [PartialOrder N] [Covar
iantClass M N μ (· < ·)] : CovariantClass M N μ (· <= ·)
-/
theorem mulRightMono_of_mulRightStrictMono (M) [Mul M] [PartialOrder M] [MulRightStrictMono M] :
    MulRightMono M := covariantClass_le_of_lt _ _ _
/-
**contravariant_le_iff_contravariant_lt_and_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contravariant_le_iff_contravariant_lt_and_eq [PartialOrder N] : Contravari
ant M N μ (· <= ·) ↔ Contravariant M N μ (· < ·) ∧ Contravariant M N μ (· = ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contravariant_le_iff_contravariant_lt_and_eq [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) ∧ Contravariant M N μ (· = ·) := by
  refine ⟨fun h ↦ ⟨fun a b c bc ↦ ?_, fun a b c bc ↦ ?_⟩, fun h ↦ fun a b c bc ↦ ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc ↦ (h.1 a bc).le) (fun bc ↦ (h.2 a bc).le)
/-
**contravariant_lt_of_contravariant_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contravariant_lt_of_contravariant_le [PartialOrder N] : Contravariant M N 
μ (· <= ·) -> Contravariant M N μ (· < ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contravariant_le_iff_contravariant_lt_and_eq`：contravariant_le_iff_contr
avariant_lt_and_eq [PartialOrder N] : Contravariant M N μ (· <= ·) ↔ Contravaria
nt M N μ (· < ·) ∧ Contravariant M…
-/
theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) :=
  And.left ∘ (contravariant_le_iff_contravariant_lt_and_eq M N μ).mp
/-
**covariant_le_iff_contravariant_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covariant_le_iff_contravariant_lt [LinearOrder N] : Covariant M N μ (· <= 
·) ↔ Contravariant M N μ (· < ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem covariant_le_iff_contravariant_lt [LinearOrder N] :
    Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_ge (h _ k),
   fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_gt (h _ k)⟩
/-
**covariant_lt_iff_contravariant_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covariant_lt_iff_contravariant_le [LinearOrder N] : Covariant M N μ (· < ·
) ↔ Contravariant M N μ (· <= ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_gt (h _ k),
   fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_ge (h _ k)⟩

variable (mu : N → N → N)
/-
**covariant_flip_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covariant_flip_iff [h : Std.Commutative mu] : Covariant N N (flip mu) r ↔ 
Covariant N N mu r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem covariant_flip_iff [h : Std.Commutative mu] :
    Covariant N N (flip mu) r ↔ Covariant N N mu r := by unfold flip; simp_rw [h.comm]
/-
**contravariant_flip_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contravariant_flip_iff [h : Std.Commutative mu] : Contravariant N N (flip 
mu) r ↔ Contravariant N N mu r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contravariant_flip_iff [h : Std.Commutative mu] :
    Contravariant N N (flip mu) r ↔ Contravariant N N mu r := by unfold flip; simp_rw [h.comm]
/-
**contravariant_lt_of_covariant_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：contravariant_lt_of_covariant_le [LinearOrder N] [CovariantClass N N mu (·
 <= ·)] : ContravariantClass N N mu (· < ·) where elim
参数：· <= ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `covariant_le_iff_contravariant_lt`：covariant_le_iff_contravariant_lt [Li
nearOrder N] : Covariant M N μ (· <= ·) ↔ Contravariant M N μ (· < ·)
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance contravariant_lt_of_covariant_le [LinearOrder N]
    [CovariantClass N N mu (· ≤ ·)] : ContravariantClass N N mu (· < ·) where
  elim := (covariant_le_iff_contravariant_lt N N mu).mp CovariantClass.elim

@[to_additive]
/-
**mulLeftReflectLT_of_mulLeftMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftReflectLT_of_mulLeftMono [Mul N] [LinearOrder N] [MulLeftMono N] : 
MulLeftReflectLT N
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeftReflectLT_of_mulLeftMono [Mul N] [LinearOrder N] [MulLeftMono N] :
    MulLeftReflectLT N :=
  inferInstance

@[to_additive]
/-
**mulRightReflectLT_of_mulRightMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightReflectLT_of_mulRightMono [Mul N] [LinearOrder N] [MulRightMono N]
 : MulRightReflectLT N
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRightReflectLT_of_mulRightMono [Mul N] [LinearOrder N] [MulRightMono N] :
    MulRightReflectLT N :=
  inferInstance
/-
**covariant_lt_of_contravariant_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：covariant_lt_of_contravariant_le [LinearOrder N] [ContravariantClass N N m
u (· <= ·)] : CovariantClass N N mu (· < ·) where elim
参数：· <= ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `covariant_lt_iff_contravariant_le`：covariant_lt_iff_contravariant_le [Li
nearOrder N] : Covariant M N μ (· < ·) ↔ Contravariant M N μ (· <= ·)
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
instance covariant_lt_of_contravariant_le [LinearOrder N]
    [ContravariantClass N N mu (· ≤ ·)] : CovariantClass N N mu (· < ·) where
  elim := (covariant_lt_iff_contravariant_le N N mu).mpr ContravariantClass.elim

@[to_additive]
/-
**mulLeftStrictMono_of_mulLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulLeftStrictMono_of_mulLeftReflectLE [Mul N] [LinearOrder N] [MulLeftRefl
ectLE N] : MulLeftStrictMono N where elim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `covariant_lt_iff_contravariant_le`：covariant_lt_iff_contravariant_le [Li
nearOrder N] : Covariant M N μ (· < ·) ↔ Contravariant M N μ (· <= ·)
· 使用定理 `MulLeftReflectLE.le_of_mul_le_mul_left'`：∀ {M : Type u_1} {inst : Mul M}
 {inst_1 : LE M} [self : MulLeftReflectLE M] {a b₁ b₂ : M}, a * b₁ ≤ a * b₂ → b₁
 ≤ b₂
-/
instance mulLeftStrictMono_of_mulLeftReflectLE [Mul N] [LinearOrder N] [MulLeftReflectLE N] :
    MulLeftStrictMono N where
  elim :=
    covariant_lt_iff_contravariant_le .. |>.mpr fun _ ↦ MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive]
/-
**mulRightStrictMono_of_mulRightReflectLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulRightStrictMono_of_mulRightReflectLE [Mul N] [LinearOrder N] [MulRightR
eflectLE N] : MulRightStrictMono N where elim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `covariant_lt_iff_contravariant_le`：covariant_lt_iff_contravariant_le [Li
nearOrder N] : Covariant M N μ (· < ·) ↔ Contravariant M N μ (· <= ·)
· 使用定理 `MulRightReflectLE.le_of_mul_le_mul_right'`：∀ {M : Type u_1} {inst : Mul 
M} {inst_1 : LE M} [self : MulRightReflectLE M] {b a₁ a₂ : M}, a₁ * b ≤ a₂ * b →
 a₁ ≤ a₂
-/
instance mulRightStrictMono_of_mulRightReflectLE [Mul N] [LinearOrder N] [MulRightReflectLE N] :
    MulRightStrictMono N where
  elim :=
    covariant_lt_iff_contravariant_le .. |>.mpr fun _ ↦ MulRightReflectLE.le_of_mul_le_mul_right'

@[to_additive]
/-
**covariant_swap_mul_of_covariant_mul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：covariant_swap_mul_of_covariant_mul [CommSemigroup N] [CovariantClass N N 
(· * ·) r] : CovariantClass N N (swap (· * ·)) r where elim
参数：· * ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `covariant_flip_iff`：covariant_flip_iff [h : Std.Commutative mu] : Covari
ant N N (flip mu) r ↔ Covariant N N mu r
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance covariant_swap_mul_of_covariant_mul [CommSemigroup N]
    [CovariantClass N N (· * ·) r] : CovariantClass N N (swap (· * ·)) r where
  elim := (covariant_flip_iff N r (· * ·)).mpr CovariantClass.elim

@[to_additive]
/-
**mulRightMono_of_mulLeftMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightMono_of_mulLeftMono [CommSemigroup N] [LE N] [MulLeftMono N] : Mul
RightMono N
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRightMono_of_mulLeftMono [CommSemigroup N] [LE N] [MulLeftMono N] :
    MulRightMono N :=
  inferInstance

@[to_additive]
/-
**mulRightStrictMono_of_mulLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightStrictMono_of_mulLeftStrictMono [CommSemigroup N] [LT N] [MulLeftS
trictMono N] : MulRightStrictMono N
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRightStrictMono_of_mulLeftStrictMono [CommSemigroup N] [LT N] [MulLeftStrictMono N] :
    MulRightStrictMono N :=
  inferInstance

@[to_additive]
/-
**contravariant_swap_mul_of_contravariant_mul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：contravariant_swap_mul_of_contravariant_mul [CommSemigroup N] [Contravaria
ntClass N N (· * ·) r] : ContravariantClass N N (swap (· * ·)) r where elim
参数：· * ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contravariant_flip_iff`：contravariant_flip_iff [h : Std.Commutative mu] 
: Contravariant N N (flip mu) r ↔ Contravariant N N mu r
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
instance contravariant_swap_mul_of_contravariant_mul [CommSemigroup N]
    [ContravariantClass N N (· * ·) r] : ContravariantClass N N (swap (· * ·)) r where
  elim := (contravariant_flip_iff N r (· * ·)).mpr ContravariantClass.elim

@[to_additive]
/-
**mulRightReflectLE_of_mulLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulRightReflectLE_of_mulLeftReflectLE [CommSemigroup N] [LE N] [MulLeftRef
lectLE N] : MulRightReflectLE N where .mpr le_of_mul_le_mul_right'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contravariant_flip_iff`：contravariant_flip_iff [h : Std.Commutative mu] 
: Contravariant N N (flip mu) r ↔ Contravariant N N mu r
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `MulLeftReflectLE.le_of_mul_le_mul_left'`：∀ {M : Type u_1} {inst : Mul M}
 {inst_1 : LE M} [self : MulLeftReflectLE M] {a b₁ b₂ : M}, a * b₁ ≤ a * b₂ → b₁
 ≤ b₂
-/
instance mulRightReflectLE_of_mulLeftReflectLE [CommSemigroup N] [LE N] [MulLeftReflectLE N] :
    MulRightReflectLE N where
  le_of_mul_le_mul_right' := contravariant_flip_iff .. |>.mpr
    (fun _ ↦ MulLeftReflectLE.le_of_mul_le_mul_left' : Contravariant N N (· * ·) _) _

@[to_additive]
/-
**mulRightReflectLT_of_mulLeftReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRightReflectLT_of_mulLeftReflectLT [CommSemigroup N] [LT N] [MulLeftRef
lectLT N] : MulRightReflectLT N
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRightReflectLT_of_mulLeftReflectLT [CommSemigroup N] [LT N] [MulLeftReflectLT N] :
    MulRightReflectLT N :=
  inferInstance
/-
**covariant_lt_of_covariant_le_of_contravariant_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covariant_lt_of_covariant_le_of_contravariant_eq [ContravariantClass M N μ
 (· = ·)] [PartialOrder N] [CovariantClass M N μ (· <= ·)] : CovariantClass M N 
μ (· < ·) where elim a _ _ bc
参数：· = ·；· <= ·。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem covariant_lt_of_covariant_le_of_contravariant_eq [ContravariantClass M N μ (· = ·)]
    [PartialOrder N] [CovariantClass M N μ (· ≤ ·)] : CovariantClass M N μ (· < ·) where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne (bc.ne ∘ ContravariantClass.elim _)
/-
**contravariant_le_of_contravariant_eq_and_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contravariant_le_of_contravariant_eq_and_lt [PartialOrder N] [Contravarian
tClass M N μ (· = ·)] [ContravariantClass M N μ (· < ·)] : ContravariantClass M 
N μ (· <= ·) where elim
参数：· = ·；· < ·。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contravariant_le_iff_contravariant_lt_and_eq`：contravariant_le_iff_contr
avariant_lt_and_eq [PartialOrder N] : Contravariant M N μ (· <= ·) ↔ Contravaria
nt M N μ (· < ·) ∧ Contravariant M…
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem contravariant_le_of_contravariant_eq_and_lt [PartialOrder N]
    [ContravariantClass M N μ (· = ·)] [ContravariantClass M N μ (· < ·)] :
    ContravariantClass M N μ (· ≤ ·) where
  elim := (contravariant_le_iff_contravariant_lt_and_eq M N μ).mpr
    ⟨ContravariantClass.elim, ContravariantClass.elim⟩

/- TODO:
  redefine `IsLeftCancel N mu` as abbrev of `ContravariantClass N N mu (· = ·)`,
  redefine `IsRightCancel N mu` as abbrev of `ContravariantClass N N (flip mu) (· = ·)`,
  redefine `IsLeftCancelMul` as abbrev of `IsLeftCancel`,
  then the following four instances (actually eight) can be removed in favor of the above two. -/

@[to_additive]
/-
**IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono [Mul N] [IsLeftCancelMul 
N] [PartialOrder N] [MulLeftMono N] : MulLeftStrictMono N where elim a _ _ bc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_ne_mul_right`：mul_ne_mul_right (a : G) {b c : G} : a * b != a * c ↔ 
b != c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
TODO:
  redefine `IsLeftCancel N mu` as abbrev of `ContravariantClass N N mu (· = ·)`,
  redefine `IsRightCancel N mu` as abbrev of `ContravariantClass N N (flip mu) (
· = ·)`,
  redefine `IsLeftCancelMul` as abbrev of `IsLeftCancel`,
  then the following four instances (actually eight) can be removed in favor of 
the above two.
-/
instance IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftMono N] :
    MulLeftStrictMono N where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_right a).mpr bc.ne)

@[to_additive]
/-
**IsRightCancelMul.mulRightStrictMono_of_mulRightMono** 是 Mathlib 中的一个实例，位于命名空间 
``。
形式化陈述：IsRightCancelMul.mulRightStrictMono_of_mulRightMono [Mul N] [IsRightCancel
Mul N] [PartialOrder N] [MulRightMono N] : MulRightStrictMono N where elim a _ _
 bc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_ne_mul_left`：mul_ne_mul_left (a : G) {b c : G} : b * a != c * a ↔ b 
!= c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
instance IsRightCancelMul.mulRightStrictMono_of_mulRightMono
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightMono N] :
    MulRightStrictMono N where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne ((mul_ne_mul_left a).mpr bc.ne)

@[to_additive]
/-
**IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间
 ``。
形式化陈述：IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT [Mul N] [IsLeftCancel
Mul N] [PartialOrder N] [MulLeftReflectLT N] : MulLeftReflectLE N where .mpr le_
of_mul_le_mul_left'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contravariant_le_iff_contravariant_lt_and_eq`：contravariant_le_iff_contr
avariant_lt_and_eq [PartialOrder N] : Contravariant M N μ (· <= ·) ↔ Contravaria
nt M N μ (· < ·) ∧ Contravariant M…
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
-/
instance IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftReflectLT N] :
    MulLeftReflectLE N where
  le_of_mul_le_mul_left' := contravariant_le_iff_contravariant_lt_and_eq N N _ |>.mpr
    ⟨‹MulLeftReflectLT N›.elim, fun _ ↦ mul_left_cancel⟩ _

@[to_additive]
/-
**IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT** 是 Mathlib 中的一个实例，位于命
名空间 ``。
形式化陈述：IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT [Mul N] [IsRightCa
ncelMul N] [PartialOrder N] [MulRightReflectLT N] : MulRightReflectLE N where .m
pr le_of_mul_le_mul_right'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contravariant_le_iff_contravariant_lt_and_eq`：contravariant_le_iff_contr
avariant_lt_and_eq [PartialOrder N] : Contravariant M N μ (· <= ·) ↔ Contravaria
nt M N μ (· < ·) ∧ Contravariant M…
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
-/
instance IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightReflectLT N] :
    MulRightReflectLE N where
  le_of_mul_le_mul_right' := contravariant_le_iff_contravariant_lt_and_eq N N _ |>.mpr
    ⟨‹MulRightReflectLT N›.elim, fun _ ↦ mul_right_cancel⟩ _

end Variants

