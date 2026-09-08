/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Action.Synonym
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Monotonicity of scalar multiplication by positive elements

This file defines typeclasses to reason about monotonicity of the operations
* `b ↦ a • b`, "left scalar multiplication"
* `a ↦ a • b`, "right scalar multiplication"

We use eight typeclasses to encode the various properties we care about for those two operations.
These typeclasses are meant to be mostly internal to this file, to set up each lemma in the
appropriate generality.

Less granular typeclasses like `IsOrderedAddMonoid` and `IsOrderedModule` should be enough for most
purposes, and the system is set up so that they imply the correct granular typeclasses here.
If those are enough for you, you may stop reading here! Else, beware that what
follows is a bit technical.


In all that follows, `α` and `β` are orders which have a `0` and such that `α` acts on `β` by scalar
multiplication. Note however that we do not use lawfulness of this action in most of the file. Hence
`•` should be considered here as a mostly arbitrary function `α → β → β`.

We use the following four typeclasses to reason about left scalar multiplication (`b ↦ a • b`):
* `PosSMulMono`: If `a ≥ 0`, then `b₁ ≤ b₂` implies `a • b₁ ≤ a • b₂`.
* `PosSMulStrictMono`: If `a > 0`, then `b₁ < b₂` implies `a • b₁ < a • b₂`.
* `PosSMulReflectLT`: If `a ≥ 0`, then `a • b₁ < a • b₂` implies `b₁ < b₂`.
* `PosSMulReflectLE`: If `a > 0`, then `a • b₁ ≤ a • b₂` implies `b₁ ≤ b₂`.

We use the following four typeclasses to reason about right scalar multiplication (`a ↦ a • b`):
* `SMulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂` implies `a₁ • b ≤ a₂ • b`.
* `SMulPosStrictMono`: If `b > 0`, then `a₁ < a₂` implies `a₁ • b < a₂ • b`.
* `SMulPosReflectLT`: If `b ≥ 0`, then `a₁ • b < a₂ • b` implies `a₁ < a₂`.
* `SMulPosReflectLE`: If `b > 0`, then `a₁ • b ≤ a₂ • b` implies `a₁ ≤ a₂`.

Furthermore, in a *module*, i.e. a group acted on by a ring, `PosSMulMono` and `SMulPosMono` are
equivalent (they are both the same as `∀ r ≥ 0, ∀ m ≥ 0, 0 ≤ r • m`),
and similarly for `PosSMulStrictMono` and `SMulPosStrictMono`.
To avoid dangerous instances going both, we have the extra two typeclasses:
* `IsOrderedModule`: Conjunction of `PosSMulMono` and `SMulPosMono`
* `IsStrictOrderedModule`: Conjunction of `PosSMulStrictMono` and `SMulPosStrictMono`.

## Constructors

The four typeclasses about nonnegativity can usually be checked only on positive inputs due to their
condition becoming trivial when `a = 0` or `b = 0`. We therefore make the following constructors
available: `PosSMulMono.of_pos`, `PosSMulReflectLT.of_pos`, `SMulPosMono.of_pos`,
`SMulPosReflectLT.of_pos`

## Implications

As `α` and `β` get more and more structure, those typeclasses end up being equivalent. The commonly
used implications are:
* When `α`, `β` are partial orders:
  * `PosSMulStrictMono → PosSMulMono`
  * `SMulPosStrictMono → SMulPosMono`
  * `PosSMulReflectLE → PosSMulReflectLT`
  * `SMulPosReflectLE → SMulPosReflectLT`
* When `β` is a linear order:
  * `PosSMulStrictMono → PosSMulReflectLE`
  * `PosSMulReflectLT → PosSMulMono` (not registered as instance)
  * `SMulPosReflectLT → SMulPosMono` (not registered as instance)
  * `PosSMulReflectLE → PosSMulStrictMono` (not registered as instance)
  * `SMulPosReflectLE → SMulPosStrictMono` (not registered as instance)
* When `α` is a linear order:
  * `SMulPosStrictMono → SMulPosReflectLE`
* When `α` is an ordered ring, `β` an ordered group and also an `α`-module:
  * `PosSMulMono → SMulPosMono`
  * `PosSMulStrictMono → SMulPosStrictMono`
* When `α` is a linear ordered semifield, `β` is an `α`-module:
  * `PosSMulStrictMono → PosSMulReflectLT`
  * `PosSMulMono → PosSMulReflectLE`
* When `α` is a semiring, `β` is an `α`-module with `Module.IsTorsionFree`:
  * `PosSMulMono → PosSMulStrictMono` (not registered as instance)
* When `α` is a ring, `β` is an `α`-module with `Module.IsTorsionFree`:
  * `SMulPosMono → SMulPosStrictMono` (not registered as instance)

Further, the bundled non-granular typeclasses imply the granular ones like so:
* `IsOrderedModule → PosSMulMono`
* `IsOrderedModule → SMulPosMono`
* `IsStrictOrderedModule → PosSMulStrictMono`
* `IsStrictOrderedModule → SMulPosStrictMono`

Unless otherwise stated, all these implications are registered as instances,
which means that in practice you should not worry about these implications.
However, if you encounter a case where you think a statement is true but
not covered by the current implications, please bring it up on Zulip!

## Implementation notes

This file uses custom typeclasses instead of abbreviations of `CovariantClass`/`ContravariantClass`
because:
* They get displayed as classes in the docs. In particular, one can see their list of instances,
  instead of their instances being invariably dumped to the `CovariantClass`/`ContravariantClass`
  list.
* They don't pollute other typeclass searches. Having many abbreviations of the same typeclass for
  different purposes always felt like a performance issue (more instances with the same key, for no
  added benefit), and indeed making the classes here abbreviation previous creates timeouts due to
  the higher number of `CovariantClass`/`ContravariantClass` instances.
* `SMulPosReflectLT`/`SMulPosReflectLE` do not fit in the framework since they relate `≤` on two
  different types. So we would have to generalise `CovariantClass`/`ContravariantClass` to three
  types and two relations.
* Very minor, but the constructors let you work with `a : α`, `h : 0 ≤ a` instead of
  `a : {a : α // 0 ≤ a}`. This actually makes some instances surprisingly cleaner to prove.
* The `CovariantClass`/`ContravariantClass` framework is only useful to automate very simple logic
  anyway. It is easily copied over.

In the future, it would be good to make the corresponding typeclasses in
`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` custom typeclasses too.
-/

@[expose] public section

assert_not_exists Field Finset

open OrderDual

variable (α β : Type*)

section Defs
variable [SMul α β] [Preorder α] [Preorder β]

section Left
variable [Zero α]

/-- Typeclass for monotonicity of scalar multiplication by nonnegative elements on the left,
namely `b₁ ≤ b₂ → a • b₁ ≤ a • b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**PosSMulMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of scalar multiplication by nonnegative elements on t
he left,
namely `b₁ ≤ b₂ → a • b₁ ≤ a • b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class PosSMulMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_left` instead. -/
  protected smul_le_smul_of_nonneg_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : b₁ ≤ b₂) :
    a • b₁ ≤ a • b₂

/-- Typeclass for strict monotonicity of scalar multiplication by positive elements on the left,
namely `b₁ < b₂ → a • b₁ < a • b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**PosSMulStrictMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict monotonicity of scalar multiplication by positive elements 
on the left,
namely `b₁ < b₂ → a • b₁ < a • b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class PosSMulStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_left` instead. -/
  protected smul_lt_smul_of_pos_left ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : b₁ < b₂) :
    a • b₁ < a • b₂

/-- Typeclass for strict reverse monotonicity of scalar multiplication by nonnegative elements on
the left, namely `a • b₁ < a • b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**PosSMulReflectLT** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of scalar multiplication by nonnegativ
e elements on
the left, namely `a • b₁ < a • b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class PosSMulReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_left` instead. -/
  protected lt_of_smul_lt_smul_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) :
    b₁ < b₂

/-- Typeclass for reverse monotonicity of scalar multiplication by positive elements on the left,
namely `a • b₁ ≤ a • b₂ → b₁ ≤ b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**PosSMulReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of scalar multiplication by positive elements
 on the left,
namely `a • b₁ ≤ a • b₂ → b₁ ≤ b₂` if `0 < a`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class PosSMulReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_le_smul_left` instead. -/
  protected le_of_smul_le_smul_left ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ ≤ a • b₂) :
    b₁ ≤ b₂

end Left

section Right
variable [Zero β]

/-- Typeclass for monotonicity of scalar multiplication by nonnegative elements on the left,
namely `a₁ ≤ a₂ → a₁ • b ≤ a₂ • b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**SMulPosMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of scalar multiplication by nonnegative elements on t
he left,
namely `a₁ ≤ a₂ → a₁ • b ≤ a₂ • b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class SMulPosMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_right` instead. -/
  protected smul_le_smul_of_nonneg_right ⦃b : β⦄ (hb : 0 ≤ b) ⦃a₁ a₂ : α⦄ (ha : a₁ ≤ a₂) :
    a₁ • b ≤ a₂ • b

/-- Typeclass for strict monotonicity of scalar multiplication by positive elements on the left,
namely `a₁ < a₂ → a₁ • b < a₂ • b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**SMulPosStrictMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict monotonicity of scalar multiplication by positive elements 
on the left,
namely `a₁ < a₂ → a₁ • b < a₂ • b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class SMulPosStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_right` instead. -/
  protected smul_lt_smul_of_pos_right ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (ha : a₁ < a₂) :
    a₁ • b < a₂ • b

/-- Typeclass for strict reverse monotonicity of scalar multiplication by nonnegative elements on
the left, namely `a₁ • b < a₂ • b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**SMulPosReflectLT** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of scalar multiplication by nonnegativ
e elements on
the left, namely `a₁ • b < a₂ • b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class SMulPosReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_right` instead. -/
  protected lt_of_smul_lt_smul_right ⦃b : β⦄ (hb : 0 ≤ b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b < a₂ • b) :
    a₁ < a₂

/-- Typeclass for reverse monotonicity of scalar multiplication by positive elements on the left,
namely `a₁ • b ≤ a₂ • b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
/-
**SMulPosReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of scalar multiplication by positive elements
 on the left,
namely `a₁ • b ≤ a₂ • b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedModule`.
-/
class SMulPosReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_le_smul_right` instead. -/
  protected le_of_smul_le_smul_right ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b ≤ a₂ • b) :
    a₁ ≤ a₂

end Right

section LeftRight
variable [Zero α] [Zero β]

/-- An ordered module is a module with a partial order such that scalar multiplication by a
nonnegative scalar and of a nonnegative vector are both monotone. -/
/-
**IsOrderedModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero α] → [Zero β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered module is a module with a partial order such that scalar multiplicati
on by a
nonnegative scalar and of a nonnegative vector are both monotone.
-/
class IsOrderedModule extends PosSMulMono α β, SMulPosMono α β

/-- An ordered module is a module with a partial order such that scalar multiplication by a
positive scalar and of a positive vector are both strictly monotone. -/
/-
**IsStrictOrderedModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [SMul α β] → [Preorder α] → [Preorder β]
 → [Zero α] → [Zero β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered module is a module with a partial order such that scalar multiplicati
on by a
positive scalar and of a positive vector are both strictly monotone.
-/
class IsStrictOrderedModule extends PosSMulStrictMono α β, SMulPosStrictMono α β

end LeftRight
end Defs

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

section Mul
variable [Zero α] [Mul α] [Preorder α]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulMono.toPosSMulMono [PosMulMono α] : PosSMulMono α α where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb := mul_le_mul_of_nonneg_left hb ha

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulStrictMono.toPosSMulStrictMono [PosMulStrictMono α] :
    PosSMulStrictMono α α where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb := mul_lt_mul_of_pos_left hb ha

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulReflectLT.toPosSMulReflectLT [PosMulReflectLT α] :
    PosSMulReflectLT α α where
  lt_of_smul_lt_smul_left _a ha _b₁ _b₂ h := lt_of_mul_lt_mul_left h ha

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulReflectLE.toPosSMulReflectLE [PosMulReflectLE α] :
    PosSMulReflectLE α α where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h := le_of_mul_le_mul_left h ha

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosMono.toSMulPosMono [MulPosMono α] : SMulPosMono α α where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := mul_le_mul_of_nonneg_right ha hb

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosStrictMono.toSMulPosStrictMono [MulPosStrictMono α] :
    SMulPosStrictMono α α where
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := mul_lt_mul_of_pos_right ha hb

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosReflectLT.toSMulPosReflectLT [MulPosReflectLT α] :
    SMulPosReflectLT α α where
  lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h := lt_of_mul_lt_mul_right h hb

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosReflectLE.toSMulPosReflectLE [MulPosReflectLE α] :
    SMulPosReflectLE α α where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h := le_of_mul_le_mul_right h hb

end Mul

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [PartialOrder M] [AddCommMonoid M] [IsOrderedAddMonoid M] :
    PosSMulMono ℕ M where
  smul_le_smul_of_nonneg_left _n _ _a _b hab := nsmul_le_nsmul_right hab _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [PartialOrder M] [AddCommMonoid M] [IsOrderedAddMonoid M] :
    SMulPosMono ℕ M where
  smul_le_smul_of_nonneg_right _a ha _m _n hmn := nsmul_le_nsmul_left ha hmn
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [PartialOrder M] [AddCancelCommMonoid M] [IsOrderedAddMonoid M] :
    PosSMulStrictMono ℕ M where
  smul_lt_smul_of_pos_left _n hn _m₁ _m₂ := nsmul_lt_nsmul_right hn.ne'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [PartialOrder M] [AddCommMonoid M] [IsOrderedCancelAddMonoid M] :
    SMulPosStrictMono ℕ M where
  smul_lt_smul_of_pos_right _a ha _m _n hmn := nsmul_lt_nsmul_left ha hmn
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] :
    PosSMulStrictMono ℤ G where
  smul_lt_smul_of_pos_left _n hn _m₁ _m₂ := zsmul_lt_zsmul_right hn
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] :
    SMulPosStrictMono ℤ G where
  smul_lt_smul_of_pos_right _a ha _m _n hmn := zsmul_lt_zsmul_left ha hmn

section SMul
variable [SMul α β]

section Preorder
variable [Preorder α] [Preorder β]

section Left
variable [Zero α]

/-
**monotone_smul_left_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 <= a) : Monotone ((
a • ·) : β -> β)
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulMono.smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2}
 {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}
   [self : PosSMulMono α β] ⦃…
-/
lemma monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) : Monotone ((a • ·) : β → β) :=
  PosSMulMono.smul_le_smul_of_nonneg_left ha
/-
**strictMono_smul_left_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) : StrictM
ono ((a • ·) : β -> β)
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulStrictMono.smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u
_2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero
 α}   [self : PosSMulStrictMono …
-/
lemma strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) :
    StrictMono ((a • ·) : β → β) := PosSMulStrictMono.smul_lt_smul_of_pos_left ha
/-
**smul_le_smul_of_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂ : β} [inst : SMul α β] [ins
t_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : Zero α] [PosSMulMono α β], b
₁ ≤ b₂ → 0 ≤ a → a • b₁ ≤ a • b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
@[gcongr] lemma smul_le_smul_of_nonneg_left [PosSMulMono α β] (hb : b₁ ≤ b₂) (ha : 0 ≤ a) :
    a • b₁ ≤ a • b₂ := monotone_smul_left_of_nonneg ha hb
/-
**smul_lt_smul_of_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂ : β} [inst : SMul α β] [ins
t_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : Zero α] [PosSMulStrictMono α
 β], b₁ < b₂ → 0 < a → a • b₁ < a • b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMono_smul_left_of_pos`：strictMono_smul_left_of_pos [PosSMulStrictM
ono α β] (ha : 0 < a) : StrictMono ((a • ·) : β -> β)
-/
@[gcongr] lemma smul_lt_smul_of_pos_left [PosSMulStrictMono α β] (hb : b₁ < b₂) (ha : 0 < a) :
    a • b₁ < a • b₂ := strictMono_smul_left_of_pos ha hb

/-- Scalar multiplication on the left by a nonnegative element preserves monotonicity. -/
/-
**Monotone.const_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.const_smul [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ -> β
} (hf : Monotone f) (ha : 0 <= a) : Monotone fun x => a • f x
参数：hf : Monotone f；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)

--- 原说明 ---
Scalar multiplication on the left by a nonnegative element preserves monotonicit
y.
-/
lemma Monotone.const_smul [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ → β}
    (hf : Monotone f) (ha : 0 ≤ a) : Monotone fun x ↦ a • f x :=
  (monotone_smul_left_of_nonneg ha).comp hf

/-- Scalar multiplication on the left by a nonnegative element preserves antitonicity. -/
/-
**Antitone.const_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.const_smul [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ -> β
} (hf : Antitone f) (ha : 0 <= a) : Antitone fun x => a • f x
参数：hf : Antitone f；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)

--- 原说明 ---
Scalar multiplication on the left by a nonnegative element preserves antitonicit
y.
-/
lemma Antitone.const_smul [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ → β}
    (hf : Antitone f) (ha : 0 ≤ a) : Antitone fun x ↦ a • f x :=
  (monotone_smul_left_of_nonneg ha).comp_antitone hf

/-- Scalar multiplication on the left by a positive element preserves strict monotonicity. -/
/-
**StrictMono.const_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.const_smul [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f 
: γ -> β} (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x => a • f x
参数：hf : StrictMono f；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `strictMono_smul_left_of_pos`：strictMono_smul_left_of_pos [PosSMulStrictM
ono α β] (ha : 0 < a) : StrictMono ((a • ·) : β -> β)

--- 原说明 ---
Scalar multiplication on the left by a positive element preserves strict monoton
icity.
-/
lemma StrictMono.const_smul [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f : γ → β}
    (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x ↦ a • f x :=
  (strictMono_smul_left_of_pos ha).comp hf

/-- Scalar multiplication on the left by a positive element preserves strict antitonicity. -/
/-
**StrictAnti.const_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.const_smul [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f 
: γ -> β} (hf : StrictAnti f) (ha : 0 < a) : StrictAnti fun x => a • f x
参数：hf : StrictAnti f；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictAnti`：StrictMono.comp_strictAnti (hg : StrictMono 
g) (hf : StrictAnti f) : StrictAnti (g ∘ f)
· 使用引理 `strictMono_smul_left_of_pos`：strictMono_smul_left_of_pos [PosSMulStrictM
ono α β] (ha : 0 < a) : StrictMono ((a • ·) : β -> β)

--- 原说明 ---
Scalar multiplication on the left by a positive element preserves strict antiton
icity.
-/
lemma StrictAnti.const_smul [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f : γ → β}
    (hf : StrictAnti f) (ha : 0 < a) : StrictAnti fun x ↦ a • f x :=
  (strictMono_smul_left_of_pos ha).comp_strictAnti hf
/-
**lt_of_smul_lt_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha :
 0 <= a) : b₁ < b₂
参数：h : a • b₁ < a • b₂；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulReflectLT.lt_of_smul_lt_smul_left`：∀ {α : Type u_1} {β : Type u_2
} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α
}   [self : PosSMulReflectLT α…
-/
lemma lt_of_smul_lt_smul_left [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : 0 ≤ a) : b₁ < b₂ :=
  PosSMulReflectLT.lt_of_smul_lt_smul_left ha h
/-
**le_of_smul_le_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_smul_le_smul_left [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha 
: 0 < a) : b₁ <= b₂
参数：h : a • b₁ <= a • b₂；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulReflectLE.le_of_smul_le_smul_left`：∀ {α : Type u_1} {β : Type u_2
} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α
}   [self : PosSMulReflectLE α…
-/
lemma le_of_smul_le_smul_left [PosSMulReflectLE α β] (h : a • b₁ ≤ a • b₂) (ha : 0 < a) : b₁ ≤ b₂ :=
  PosSMulReflectLE.le_of_smul_le_smul_left ha h

alias lt_of_smul_lt_smul_of_nonneg_left := lt_of_smul_lt_smul_left
alias le_of_smul_le_smul_of_pos_left := le_of_smul_le_smul_left

@[simp]
/-
**smul_le_smul_iff_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_smul_iff_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha 
: 0 < a) : a • b₁ <= a • b₂ ↔ b₁ <= b₂
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma smul_le_smul_iff_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a • b₁ ≤ a • b₂ ↔ b₁ ≤ b₂ :=
  ⟨fun h ↦ le_of_smul_le_smul_left h ha, fun h ↦ smul_le_smul_of_nonneg_left h ha.le⟩

@[simp]
/-
**smul_lt_smul_iff_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β
] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma smul_lt_smul_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b₁ < a • b₂ ↔ b₁ < b₂ :=
  ⟨fun h ↦ lt_of_smul_lt_smul_left h ha.le, fun hb ↦ smul_lt_smul_of_pos_left hb ha⟩

end Left

section Right
variable [Zero β]

/-
**monotone_smul_right_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_smul_right_of_nonneg [SMulPosMono α β] (hb : 0 <= b) : Monotone (
(· • b) : α -> β)
参数：hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulPosMono.smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2
} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero β
}   [self : SMulPosMono α β] ⦃…
-/
lemma monotone_smul_right_of_nonneg [SMulPosMono α β] (hb : 0 ≤ b) : Monotone ((· • b) : α → β) :=
  SMulPosMono.smul_le_smul_of_nonneg_right hb
/-
**strictMono_smul_right_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_smul_right_of_pos [SMulPosStrictMono α β] (hb : 0 < b) : Strict
Mono ((· • b) : α -> β)
参数：hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulPosStrictMono.smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type 
u_2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zer
o β}   [self : SMulPosStrictMono …
-/
lemma strictMono_smul_right_of_pos [SMulPosStrictMono α β] (hb : 0 < b) :
    StrictMono ((· • b) : α → β) := SMulPosStrictMono.smul_lt_smul_of_pos_right hb

/-- Scalar multiplication on the right by a nonnegative element preserves monotonicity. -/
/-
**Monotone.smul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.smul_const [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ -> α
} (hf : Monotone f) (hb : 0 <= b) : Monotone fun x => f x • b
参数：hf : Monotone f；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用引理 `monotone_smul_right_of_nonneg`：monotone_smul_right_of_nonneg [SMulPosMon
o α β] (hb : 0 <= b) : Monotone ((· • b) : α -> β)

--- 原说明 ---
Scalar multiplication on the right by a nonnegative element preserves monotonici
ty.
-/
lemma Monotone.smul_const [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ → α}
    (hf : Monotone f) (hb : 0 ≤ b) : Monotone fun x ↦ f x • b :=
  (monotone_smul_right_of_nonneg hb).comp hf

/-- Scalar multiplication on the right by a nonnegative element preserves antitonicity. -/
/-
**Antitone.smul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.smul_const [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ -> α
} (hf : Antitone f) (hb : 0 <= b) : Antitone fun x => f x • b
参数：hf : Antitone f；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `monotone_smul_right_of_nonneg`：monotone_smul_right_of_nonneg [SMulPosMon
o α β] (hb : 0 <= b) : Monotone ((· • b) : α -> β)

--- 原说明 ---
Scalar multiplication on the right by a nonnegative element preserves antitonici
ty.
-/
lemma Antitone.smul_const [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ → α}
    (hf : Antitone f) (hb : 0 ≤ b) : Antitone fun x ↦ f x • b :=
  (monotone_smul_right_of_nonneg hb).comp_antitone hf

/-- Scalar multiplication on the right by a positive element preserves strict monotonicity. -/
/-
**StrictMono.smul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.smul_const [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f 
: γ -> α} (hf : StrictMono f) (hb : 0 < b) : StrictMono fun x => f x • b
参数：hf : StrictMono f；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `strictMono_smul_right_of_pos`：strictMono_smul_right_of_pos [SMulPosStric
tMono α β] (hb : 0 < b) : StrictMono ((· • b) : α -> β)

--- 原说明 ---
Scalar multiplication on the right by a positive element preserves strict monoto
nicity.
-/
lemma StrictMono.smul_const [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f : γ → α}
    (hf : StrictMono f) (hb : 0 < b) : StrictMono fun x ↦ f x • b :=
  (strictMono_smul_right_of_pos hb).comp hf

/-- Scalar multiplication on the right by a positive element preserves strict antitonicity. -/
/-
**StrictAnti.smul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.smul_const [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f 
: γ -> α} (hf : StrictAnti f) (hb : 0 < b) : StrictAnti fun x => f x • b
参数：hf : StrictAnti f；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictAnti`：StrictMono.comp_strictAnti (hg : StrictMono 
g) (hf : StrictAnti f) : StrictAnti (g ∘ f)
· 使用引理 `strictMono_smul_right_of_pos`：strictMono_smul_right_of_pos [SMulPosStric
tMono α β] (hb : 0 < b) : StrictMono ((· • b) : α -> β)

--- 原说明 ---
Scalar multiplication on the right by a positive element preserves strict antito
nicity.
-/
lemma StrictAnti.smul_const [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f : γ → α}
    (hf : StrictAnti f) (hb : 0 < b) : StrictAnti fun x ↦ f x • b :=
  (strictMono_smul_right_of_pos hb).comp_strictAnti hf
/-
**smul_le_smul_of_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {b : β} [inst : SMul α β] [ins
t_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : Zero β] [SMulPosMono α β], a
₁ ≤ a₂ → 0 ≤ b → a₁ • b ≤ a₂ • b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotone_smul_right_of_nonneg`：monotone_smul_right_of_nonneg [SMulPosMon
o α β] (hb : 0 <= b) : Monotone ((· • b) : α -> β)
-/
@[gcongr] lemma smul_le_smul_of_nonneg_right [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : 0 ≤ b) :
    a₁ • b ≤ a₂ • b := monotone_smul_right_of_nonneg hb ha

variable (β) in
@[gcongr, mono]
/-
**smul_one_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_one_mono [One β] [ZeroLEOneClass β] [SMulPosMono α β] : Monotone (fun
 x : α => x • (1 : β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma smul_one_mono [One β] [ZeroLEOneClass β] [SMulPosMono α β] :
    Monotone (fun x : α ↦ x • (1 : β)) :=
  fun _ _ ha ↦ smul_le_smul_of_nonneg_right ha zero_le_one
/-
**smul_lt_smul_of_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {b : β} [inst : SMul α β] [ins
t_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : Zero β] [SMulPosStrictMono α
 β], a₁ < a₂ → 0 < b → a₁ • b < a₂ • b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMono_smul_right_of_pos`：strictMono_smul_right_of_pos [SMulPosStric
tMono α β] (hb : 0 < b) : StrictMono ((· • b) : α -> β)
-/
@[gcongr] lemma smul_lt_smul_of_pos_right [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : 0 < b) :
    a₁ • b < a₂ • b := strictMono_smul_right_of_pos hb ha
/-
**lt_of_smul_lt_smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_smul_lt_smul_right [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb 
: 0 <= b) : a₁ < a₂
参数：h : a₁ • b < a₂ • b；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulPosReflectLT.lt_of_smul_lt_smul_right`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
β}   [self : SMulPosReflectLT α…
-/
lemma lt_of_smul_lt_smul_right [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 ≤ b) :
    a₁ < a₂ := SMulPosReflectLT.lt_of_smul_lt_smul_right hb h
/-
**le_of_smul_le_smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_smul_le_smul_right [SMulPosReflectLE α β] (h : a₁ • b <= a₂ • b) (hb
 : 0 < b) : a₁ <= a₂
参数：h : a₁ • b <= a₂ • b；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulPosReflectLE.le_of_smul_le_smul_right`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
β}   [self : SMulPosReflectLE α…
-/
lemma le_of_smul_le_smul_right [SMulPosReflectLE α β] (h : a₁ • b ≤ a₂ • b) (hb : 0 < b) :
    a₁ ≤ a₂ := SMulPosReflectLE.le_of_smul_le_smul_right hb h

alias lt_of_smul_lt_smul_of_nonneg_right := lt_of_smul_lt_smul_right
alias le_of_smul_le_smul_of_pos_right := le_of_smul_le_smul_right

@[simp]
/-
**smul_le_smul_iff_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_smul_iff_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb
 : 0 < b) : a₁ • b <= a₂ • b ↔ a₁ <= a₂
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_right`：le_of_smul_le_smul_right [SMulPosReflectLE α β
] (h : a₁ • b <= a₂ • b) (hb : 0 < b) : a₁ <= a₂
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma smul_le_smul_iff_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a₁ • b ≤ a₂ • b ↔ a₁ ≤ a₂ :=
  ⟨fun h ↦ le_of_smul_le_smul_right h hb, fun ha ↦ smul_le_smul_of_nonneg_right ha hb.le⟩

@[simp]
/-
**smul_lt_smul_iff_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α 
β] (hb : 0 < b) : a₁ • b < a₂ • b ↔ a₁ < a₂
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma smul_lt_smul_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    a₁ • b < a₂ • b ↔ a₁ < a₂ :=
  ⟨fun h ↦ lt_of_smul_lt_smul_right h hb.le, fun ha ↦ smul_lt_smul_of_pos_right ha hb⟩

end Right

section LeftRight
variable [Zero α] [Zero β]

/-
**smul_lt_smul_of_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_of_le_of_lt [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a
₁ <= a₂) (hb : b₁ < b₂) (h₁ : 0 < a₁) (h₂ : 0 <= b₂) : a₁ • b₁ < a₂ • b₂
参数：ha : a₁ <= a₂；hb : b₁ < b₂；h₁ : 0 < a₁；h₂ : 0 <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma smul_lt_smul_of_le_of_lt [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂)
    (hb : b₁ < b₂) (h₁ : 0 < a₁) (h₂ : 0 ≤ b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂)
/-
**smul_lt_smul_of_le_of_lt'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_of_le_of_lt' [PosSMulStrictMono α β] [SMulPosMono α β] (ha : 
a₁ <= a₂) (hb : b₁ < b₂) (h₂ : 0 < a₂) (h₁ : 0 <= b₁) : a₁ • b₁ < a₂ • b₂
参数：ha : a₁ <= a₂；hb : b₁ < b₂；h₂ : 0 < a₂；h₁ : 0 <= b₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma smul_lt_smul_of_le_of_lt' [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂)
    (hb : b₁ < b₂) (h₂ : 0 < a₂) (h₁ : 0 ≤ b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans_lt (smul_lt_smul_of_pos_left hb h₂)
/-
**smul_lt_smul_of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_of_lt_of_le [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a
₁ < a₂) (hb : b₁ <= b₂) (h₁ : 0 <= a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂
参数：ha : a₁ < a₂；hb : b₁ <= b₂；h₁ : 0 <= a₁；h₂ : 0 < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma smul_lt_smul_of_lt_of_le [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ ≤ b₂) (h₁ : 0 ≤ a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_le_smul_of_nonneg_left hb h₁).trans_lt (smul_lt_smul_of_pos_right ha h₂)
/-
**smul_lt_smul_of_lt_of_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_of_lt_of_le' [PosSMulMono α β] [SMulPosStrictMono α β] (ha : 
a₁ < a₂) (hb : b₁ <= b₂) (h₂ : 0 <= a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂
参数：ha : a₁ < a₂；hb : b₁ <= b₂；h₂ : 0 <= a₂；h₁ : 0 < b₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
lemma smul_lt_smul_of_lt_of_le' [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ ≤ b₂) (h₂ : 0 ≤ a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂)
/-
**smul_lt_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂
) (hb : b₁ < b₂) (h₁ : 0 < a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂
参数：ha : a₁ < a₂；hb : b₁ < b₂；h₁ : 0 < a₁；h₂ : 0 < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma smul_lt_smul [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
    (h₁ : 0 < a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_left hb h₁).trans (smul_lt_smul_of_pos_right ha h₂)
/-
**smul_lt_smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul' [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a
₂) (hb : b₁ < b₂) (h₂ : 0 < a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂
参数：ha : a₁ < a₂；hb : b₁ < b₂；h₂ : 0 < a₂；h₁ : 0 < b₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma smul_lt_smul' [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
    (h₂ : 0 < a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_right ha h₁).trans (smul_lt_smul_of_pos_left hb h₂)
/-
**smul_le_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_smul [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ 
<= b₂) (h₁ : 0 <= a₁) (h₂ : 0 <= b₂) : a₁ • b₁ <= a₂ • b₂
参数：ha : a₁ <= a₂；hb : b₁ <= b₂；h₁ : 0 <= a₁；h₂ : 0 <= b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma smul_le_smul [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ b₂) : a₁ • b₁ ≤ a₂ • b₂ :=
  (smul_le_smul_of_nonneg_left hb h₁).trans (smul_le_smul_of_nonneg_right ha h₂)
/-
**smul_le_smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_smul' [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁
 <= b₂) (h₂ : 0 <= a₂) (h₁ : 0 <= b₁) : a₁ • b₁ <= a₂ • b₂
参数：ha : a₁ <= a₂；hb : b₁ <= b₂；h₂ : 0 <= a₂；h₁ : 0 <= b₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
lemma smul_le_smul' [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₂ : 0 ≤ a₂)
    (h₁ : 0 ≤ b₁) : a₁ • b₁ ≤ a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans (smul_le_smul_of_nonneg_left hb h₂)

end LeftRight
end Preorder

variable (β) in
@[gcongr, mono]
/-
**smul_one_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_one_strictMono [Preorder α] [PartialOrder β] [Zero β] [One β] [ZeroLE
OneClass β] [NeZero (1 : β)] [SMulPosStrictMono α β] : StrictMono (fun x : α => 
x • (1 : β))
参数：1 : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
lemma smul_one_strictMono [Preorder α] [PartialOrder β] [Zero β] [One β] [ZeroLEOneClass β]
    [NeZero (1 : β)] [SMulPosStrictMono α β] :
    StrictMono (fun x : α ↦ x • (1 : β)) :=
  fun _ _ ha ↦ smul_lt_smul_of_pos_right ha (zero_lt_one (α := β))

section PartialOrder
variable [Semiring α] [PartialOrder α]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsOrderedRing.toIsOrderedModule [IsOrderedRing α] :
    IsOrderedModule α α where

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsStrictOrderedRing.toIsStrictOrderedModule [IsStrictOrderedRing α] :
    IsStrictOrderedModule α α where

end PartialOrder

section LinearOrder
variable [Preorder α] [LinearOrder β]

section Left
variable [Zero α]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLE [PosSMulStrictMono α β] :
    PosSMulReflectLE α β where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ := (strictMono_smul_left_of_pos ha).le_iff_le.1
/-
**PosSMulReflectLE.toPosSMulStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulReflectLE.toPosSMulStrictMono [PosSMulReflectLE α β] : PosSMulStric
tMono α β where smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
-/
lemma PosSMulReflectLE.toPosSMulStrictMono [PosSMulReflectLE α β] : PosSMulStrictMono α β where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb :=
    not_le.1 fun h ↦ hb.not_ge <| le_of_smul_le_smul_left h ha
/-
**posSMulStrictMono_iff_PosSMulReflectLE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：posSMulStrictMono_iff_PosSMulReflectLE : PosSMulStrictMono α β ↔ PosSMulRe
flectLE α β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulStrictMono.toPosSMulReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : Preorder α] [inst_2 : LinearOrder β] [inst_3 : Zero α]
   [PosSMulStrictMono α β]…
· 使用引理 `PosSMulReflectLE.toPosSMulStrictMono`：PosSMulReflectLE.toPosSMulStrictMo
no [PosSMulReflectLE α β] : PosSMulStrictMono α β where smul_lt_smul_of_pos_left
 _a ha _b₁ _b₂ hb
-/
lemma posSMulStrictMono_iff_PosSMulReflectLE : PosSMulStrictMono α β ↔ PosSMulReflectLE α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLE.toPosSMulStrictMono⟩
/-
**PosSMulMono.toPosSMulReflectLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosSMulMono.toPosSMulReflectLT [PosSMulMono α β] : PosSMulReflectLT α β wh
ere lt_of_smul_lt_smul_left _a ha _b₁ _b₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
instance PosSMulMono.toPosSMulReflectLT [PosSMulMono α β] : PosSMulReflectLT α β where
  lt_of_smul_lt_smul_left _a ha _b₁ _b₂ := (monotone_smul_left_of_nonneg ha).reflect_lt
/-
**PosSMulReflectLT.toPosSMulMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulReflectLT.toPosSMulMono [PosSMulReflectLT α β] : PosSMulMono α β wh
ere smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
-/
lemma PosSMulReflectLT.toPosSMulMono [PosSMulReflectLT α β] : PosSMulMono α β where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb :=
    not_lt.1 fun h ↦ hb.not_gt <| lt_of_smul_lt_smul_left h ha
/-
**posSMulMono_iff_posSMulReflectLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：posSMulMono_iff_posSMulReflectLT : PosSMulMono α β ↔ PosSMulReflectLT α β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulReflectLT.toPosSMulMono`：PosSMulReflectLT.toPosSMulMono [PosSMulR
eflectLT α β] : PosSMulMono α β where smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ 
hb
-/
lemma posSMulMono_iff_posSMulReflectLT : PosSMulMono α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ ↦ PosSMulMono.toPosSMulReflectLT, fun _ ↦ PosSMulReflectLT.toPosSMulMono⟩
/-
**smul_max_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_max_of_nonneg [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β) : a • max b
₁ b₂ = max (a • b₁) (a • b₂)
参数：ha : 0 <= a；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
lemma smul_max_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (b₁ b₂ : β) :
    a • max b₁ b₂ = max (a • b₁) (a • b₂) := (monotone_smul_left_of_nonneg ha).map_max
/-
**smul_min_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_min_of_nonneg [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β) : a • min b
₁ b₂ = min (a • b₁) (a • b₂)
参数：ha : 0 <= a；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
lemma smul_min_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (b₁ b₂ : β) :
    a • min b₁ b₂ = min (a • b₁) (a • b₂) := (monotone_smul_left_of_nonneg ha).map_min

end Left

section Right
variable [Zero β]

/-
**SMulPosReflectLE.toSMulPosStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLE.toSMulPosStrictMono [SMulPosReflectLE α β] : SMulPosStric
tMono α β where smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_of_smul_le_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ 
: α} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [in
st_3 : Zero β] [SMulP…
-/
lemma SMulPosReflectLE.toSMulPosStrictMono [SMulPosReflectLE α β] : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha :=
    not_le.1 fun h ↦ ha.not_ge <| le_of_smul_le_smul_of_pos_right h hb
/-
**SMulPosReflectLT.toSMulPosMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLT.toSMulPosMono [SMulPosReflectLT α β] : SMulPosMono α β wh
ere smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
-/
lemma SMulPosReflectLT.toSMulPosMono [SMulPosReflectLT α β] : SMulPosMono α β where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha :=
    not_lt.1 fun h ↦ ha.not_gt <| lt_of_smul_lt_smul_right h hb

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [Preorder β]

section Right
variable [Zero β]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SMulPosStrictMono.toSMulPosReflectLE [SMulPosStrictMono α β] :
    SMulPosReflectLE α β where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h :=
    not_lt.1 fun ha ↦ h.not_gt <| smul_lt_smul_of_pos_right ha hb
/-
**SMulPosMono.toSMulPosReflectLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosMono.toSMulPosReflectLT [SMulPosMono α β] : SMulPosReflectLT α β wh
ere lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma SMulPosMono.toSMulPosReflectLT [SMulPosMono α β] : SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h :=
    not_le.1 fun ha ↦ h.not_ge <| smul_le_smul_of_nonneg_right ha hb

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

section Right
variable [Zero β]

/-
**smulPosStrictMono_iff_SMulPosReflectLE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smulPosStrictMono_iff_SMulPosReflectLE : SMulPosStrictMono α β ↔ SMulPosRe
flectLE α β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulPosStrictMono.toSMulPosReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : LinearOrder α] [inst_2 : Preorder β] [inst_3 : Zero β]
   [SMulPosStrictMono α β]…
· 使用引理 `SMulPosReflectLE.toSMulPosStrictMono`：SMulPosReflectLE.toSMulPosStrictMo
no [SMulPosReflectLE α β] : SMulPosStrictMono α β where smul_lt_smul_of_pos_righ
t _b hb _a₁ _a₂ ha
-/
lemma smulPosStrictMono_iff_SMulPosReflectLE : SMulPosStrictMono α β ↔ SMulPosReflectLE α β :=
  ⟨fun _ ↦ SMulPosStrictMono.toSMulPosReflectLE, fun _ ↦ SMulPosReflectLE.toSMulPosStrictMono⟩
/-
**smulPosMono_iff_smulPosReflectLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smulPosMono_iff_smulPosReflectLT : SMulPosMono α β ↔ SMulPosReflectLT α β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosMono.toSMulPosReflectLT`：SMulPosMono.toSMulPosReflectLT [SMulPosM
ono α β] : SMulPosReflectLT α β where lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h
· 使用引理 `SMulPosReflectLT.toSMulPosMono`：SMulPosReflectLT.toSMulPosMono [SMulPosR
eflectLT α β] : SMulPosMono α β where smul_le_smul_of_nonneg_right _b hb _a₁ _a₂
 ha
-/
lemma smulPosMono_iff_smulPosReflectLT : SMulPosMono α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ ↦ SMulPosMono.toSMulPosReflectLT, fun _ ↦ SMulPosReflectLT.toSMulPosMono⟩

end Right
end LinearOrder
end SMul

section SMulZeroClass
variable [Zero α] [Zero β] [SMulZeroClass α β]

section Preorder
variable [Preorder α] [Preorder β]

/-
**smul_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha
/-
**smul_neg_of_pos_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0) :
 a • b < 0
参数：ha : 0 < a；hb : b < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0) : a • b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

@[simp]
/-
**smul_pos_iff_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_pos_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (h
a : 0 < a) : 0 < a • b ↔ 0 < b
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
-/
lemma smul_pos_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    0 < a • b ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₁ := 0) (b₂ := b)
/-
**smul_neg_iff_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_neg_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (h
a : 0 < a) : a • b < 0 ↔ b < 0
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
-/
lemma smul_neg_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b < 0 ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₂ := (0 : β))
/-
**smul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) : 0 <= a • b₁
参数：ha : 0 <= a；hb : 0 <= b₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
lemma smul_nonneg [PosSMulMono α β] (ha : 0 ≤ a) (hb : 0 ≤ b₁) : 0 ≤ a • b₁ := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha
/-
**smul_nonpos_of_nonneg_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_of_nonneg_of_nonpos [PosSMulMono α β] (ha : 0 <= a) (hb : b <=
 0) : a • b <= 0
参数：ha : 0 <= a；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
lemma smul_nonpos_of_nonneg_of_nonpos [PosSMulMono α β] (ha : 0 ≤ a) (hb : b ≤ 0) : a • b ≤ 0 := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha
/-
**pos_of_smul_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pos_of_smul_pos_left [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 <= a) 
: 0 < b
参数：h : 0 < a • b；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma pos_of_smul_pos_left [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha
/-
**neg_of_smul_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_smul_neg_left [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 <= a) 
: b < 0
参数：h : a • b < 0；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma neg_of_smul_neg_left [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha
/-
**nonneg_of_smul_nonneg_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonneg_of_smul_nonneg_of_pos_left [PosSMulReflectLE α β] (h : 0 <= a • b) 
(ha : 0 < a) : 0 <= b
参数：h : 0 <= a • b；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_smul_le_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} 
{b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [ins
t_3 : Zero α] [PosSM…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma nonneg_of_smul_nonneg_of_pos_left [PosSMulReflectLE α β] (h : 0 ≤ a • b) (ha : 0 < a) :
    0 ≤ b :=
  le_of_smul_le_smul_of_pos_left (by simpa) ha
/-
**nonpos_of_smul_nonpos_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonpos_of_smul_nonpos_of_pos_left [PosSMulReflectLE α β] (h : a • b <= 0) 
(ha : 0 < a) : b <= 0
参数：h : a • b <= 0；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_smul_le_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} 
{b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [ins
t_3 : Zero α] [PosSM…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma nonpos_of_smul_nonpos_of_pos_left [PosSMulReflectLE α β] (h : a • b ≤ 0) (ha : 0 < a) :
    b ≤ 0 :=
  le_of_smul_le_smul_of_pos_left (by simpa) ha
/-
**smul_nonneg_iff_nonneg_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg_iff_nonneg_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β
] (ha : 0 < a) : 0 <= a • b ↔ 0 <= b
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonneg_of_smul_nonneg_of_pos_left`：nonneg_of_smul_nonneg_of_pos_left [Po
sSMulReflectLE α β] (h : 0 <= a • b) (ha : 0 < a) : 0 <= b
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma smul_nonneg_iff_nonneg_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    0 ≤ a • b ↔ 0 ≤ b :=
  ⟨(nonneg_of_smul_nonneg_of_pos_left · ha), smul_nonneg ha.le⟩
/-
**smul_nonpos_iff_nonpos_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_iff_nonpos_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β
] (ha : 0 < a) : a • b <= 0 ↔ b <= 0
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonpos_of_smul_nonpos_of_pos_left`：nonpos_of_smul_nonpos_of_pos_left [Po
sSMulReflectLE α β] (h : a • b <= 0) (ha : 0 < a) : b <= 0
· 使用引理 `smul_nonpos_of_nonneg_of_nonpos`：smul_nonpos_of_nonneg_of_nonpos [PosSMu
lMono α β] (ha : 0 <= a) (hb : b <= 0) : a • b <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma smul_nonpos_iff_nonpos_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a • b ≤ 0 ↔ b ≤ 0 :=
  ⟨(nonpos_of_smul_nonpos_of_pos_left · ha), smul_nonpos_of_nonneg_of_nonpos ha.le⟩

end Preorder
end SMulZeroClass

section SMulWithZero
variable [Zero α] [Zero β] [SMulWithZero α β]

section Preorder
variable [Preorder α] [Preorder β]

/-
**smul_pos'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_pos' [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma smul_pos' [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb
/-
**smul_neg_of_neg_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_neg_of_neg_of_pos [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b) :
 a • b < 0
参数：ha : a < 0；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma smul_neg_of_neg_of_pos [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b) : a • b < 0 := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

@[simp]
/-
**smul_pos_iff_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_pos_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (
hb : 0 < b) : 0 < a • b ↔ 0 < a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `smul_lt_smul_iff_of_pos_right`：smul_lt_smul_iff_of_pos_right [SMulPosStr
ictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) : a₁ • b < a₂ • b ↔ a₁ < a₂
-/
lemma smul_pos_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    0 < a • b ↔ 0 < a := by
  simpa only [zero_smul] using smul_lt_smul_iff_of_pos_right hb (a₁ := 0) (a₂ := a)
/-
**smul_nonneg'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg' [SMulPosMono α β] (ha : 0 <= a) (hb : 0 <= b₁) : 0 <= a • b₁
参数：ha : 0 <= a；hb : 0 <= b₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma smul_nonneg' [SMulPosMono α β] (ha : 0 ≤ a) (hb : 0 ≤ b₁) : 0 ≤ a • b₁ := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb
/-
**smul_nonpos_of_nonpos_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_of_nonpos_of_nonneg [SMulPosMono α β] (ha : a <= 0) (hb : 0 <=
 b) : a • b <= 0
参数：ha : a <= 0；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma smul_nonpos_of_nonpos_of_nonneg [SMulPosMono α β] (ha : a ≤ 0) (hb : 0 ≤ b) : a • b ≤ 0 := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb
/-
**pos_of_smul_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pos_of_smul_pos_right [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 <= b)
 : 0 < a
参数：h : 0 < a • b；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma pos_of_smul_pos_right [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb
/-
**neg_of_smul_neg_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_smul_neg_right [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 <= b)
 : a < 0
参数：h : a • b < 0；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma neg_of_smul_neg_right [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb
/-
**pos_iff_pos_of_smul_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pos_iff_pos_of_smul_pos [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab
 : 0 < a • b) : 0 < a ↔ 0 < b
参数：hab : 0 < a • b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pos_of_smul_pos_left`：pos_of_smul_pos_left [PosSMulReflectLT α β] (h : 0
 < a • b) (ha : 0 <= a) : 0 < b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `pos_of_smul_pos_right`：pos_of_smul_pos_right [SMulPosReflectLT α β] (h :
 0 < a • b) (hb : 0 <= b) : 0 < a
-/
lemma pos_iff_pos_of_smul_pos [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab : 0 < a • b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_smul_pos_left hab ∘ le_of_lt, pos_of_smul_pos_right hab ∘ le_of_lt⟩
/-
**nonneg_of_smul_nonneg_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonneg_of_smul_nonneg_of_pos_right [SMulPosReflectLE α β] (h : 0 <= a • b)
 (hb : 0 < b) : 0 <= a
参数：h : 0 <= a • b；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_smul_le_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ 
: α} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [in
st_3 : Zero β] [SMulP…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma nonneg_of_smul_nonneg_of_pos_right [SMulPosReflectLE α β] (h : 0 ≤ a • b) (hb : 0 < b) :
    0 ≤ a :=
  le_of_smul_le_smul_of_pos_right (by simpa) hb
/-
**nonpos_of_smul_nonpos_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonpos_of_smul_nonpos_of_pos_right [SMulPosReflectLE α β] (h : a • b <= 0)
 (hb : 0 < b) : a <= 0
参数：h : a • b <= 0；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_smul_le_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ 
: α} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [in
st_3 : Zero β] [SMulP…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma nonpos_of_smul_nonpos_of_pos_right [SMulPosReflectLE α β] (h : a • b ≤ 0) (hb : 0 < b) :
    a ≤ 0 :=
  le_of_smul_le_smul_of_pos_right (by simpa) hb
/-
**smul_nonneg_iff_nonneg_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg_iff_nonneg_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α 
β] (hb : 0 < b) : 0 <= a • b ↔ 0 <= a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonneg_of_smul_nonneg_of_pos_right`：nonneg_of_smul_nonneg_of_pos_right [
SMulPosReflectLE α β] (h : 0 <= a • b) (hb : 0 < b) : 0 <= a
· 使用引理 `smul_nonneg'`：smul_nonneg' [SMulPosMono α β] (ha : 0 <= a) (hb : 0 <= b₁
) : 0 <= a • b₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma smul_nonneg_iff_nonneg_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    0 ≤ a • b ↔ 0 ≤ a :=
  ⟨(nonneg_of_smul_nonneg_of_pos_right · hb), (smul_nonneg' · hb.le)⟩
/-
**smul_nonpos_iff_nonpos_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_iff_nonpos_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α 
β] (hb : 0 < b) : a • b <= 0 ↔ a <= 0
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonpos_of_smul_nonpos_of_pos_right`：nonpos_of_smul_nonpos_of_pos_right [
SMulPosReflectLE α β] (h : a • b <= 0) (hb : 0 < b) : a <= 0
· 使用引理 `smul_nonpos_of_nonpos_of_nonneg`：smul_nonpos_of_nonpos_of_nonneg [SMulPo
sMono α β] (ha : a <= 0) (hb : 0 <= b) : a • b <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma smul_nonpos_iff_nonpos_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a • b ≤ 0 ↔ a ≤ 0 :=
  ⟨(nonpos_of_smul_nonpos_of_pos_right · hb), (smul_nonpos_of_nonpos_of_nonneg · hb.le)⟩
/-
**IsOrderedModule.of_smul_one_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderedModule.of_smul_one_mono [MulOneClass β] [PosMulMono β] [MulPosMon
o β] [IsScalarTower α β β] (h : Monotone (fun x : α => x • (1 : β))) : IsOrdered
Module α β where smul_le_smul_of_nonneg_left _ ha _ _ hb
参数：h : Monotone (fun x : α => x • (1 : β))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
lemma IsOrderedModule.of_smul_one_mono
    [MulOneClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β]
    (h : Monotone (fun x : α ↦ x • (1 : β))) : IsOrderedModule α β where
  smul_le_smul_of_nonneg_left _ ha _ _ hb := by
    have := mul_le_mul_of_nonneg_left hb (by simpa using h ha)
    simpa
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa using mul_le_mul_of_nonneg_right (h hb) ha
/-
**isOrderedModule_iff_smul_one_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOrderedModule_iff_smul_one_mono [MulOneClass β] [ZeroLEOneClass β] [PosM
ulMono β] [MulPosMono β] [IsScalarTower α β β] : IsOrderedModule α β ↔ Monotone 
(fun x : α => x • (1 : β)) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_one_mono`：smul_one_mono [One β] [ZeroLEOneClass β] [SMulPosMono α β
] : Monotone (fun x : α => x • (1 : β))
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用引理 `IsOrderedModule.of_smul_one_mono`：IsOrderedModule.of_smul_one_mono [MulO
neClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β] (h : Monotone (fu
n x : α => x • (1 : β)…
-/
theorem isOrderedModule_iff_smul_one_mono
    [MulOneClass β] [ZeroLEOneClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β] :
    IsOrderedModule α β ↔ Monotone (fun x : α ↦ x • (1 : β)) where
  mp _ := smul_one_mono _
  mpr := IsOrderedModule.of_smul_one_mono

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β]

/-- A constructor for `PosSMulMono` requiring you to prove `b₁ ≤ b₂ → a • b₁ ≤ a • b₂` only when
`0 < a` -/
/-
**PosSMulMono.of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulMono.of_pos (h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, b₁ <= b₂
 -> a • b₁ <= a • b₂) : PosSMulMono α β where smul_le_smul_of_nonneg_left a ha b
₁ b₂ h
参数：h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, b₁ <= b₂ -> a • b₁ <= a • b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
A constructor for `PosSMulMono` requiring you to prove `b₁ ≤ b₂ → a • b₁ ≤ a • b
₂` only when
`0 < a`
-/
lemma PosSMulMono.of_pos (h₀ : ∀ a : α, 0 < a → ∀ b₁ b₂ : β, b₁ ≤ b₂ → a • b₁ ≤ a • b₂) :
    PosSMulMono α β where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha]
    · exact h₀ _ ha _ _ h

/-- A constructor for `PosSMulReflectLT` requiring you to prove `a • b₁ < a • b₂ → b₁ < b₂` only
when `0 < a` -/
/-
**PosSMulReflectLT.of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulReflectLT.of_pos (h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, a •
 b₁ < a • b₂ -> b₁ < b₂) : PosSMulReflectLT α β where lt_of_smul_lt_smul_left a 
ha b₁ b₂ h
参数：h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, a • b₁ < a • b₂ -> b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
A constructor for `PosSMulReflectLT` requiring you to prove `a • b₁ < a • b₂ → b
₁ < b₂` only
when `0 < a`
-/
lemma PosSMulReflectLT.of_pos (h₀ : ∀ a : α, 0 < a → ∀ b₁ b₂ : β, a • b₁ < a • b₂ → b₁ < b₂) :
    PosSMulReflectLT α β where
  lt_of_smul_lt_smul_left a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha] at h
    · exact h₀ _ ha _ _ h

end PartialOrder

section PartialOrder
variable [Preorder α] [PartialOrder β]

/-- A constructor for `SMulPosMono` requiring you to prove `a₁ ≤ a₂ → a₁ • b ≤ a₂ • b` only when
`0 < b` -/
/-
**SMulPosMono.of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosMono.of_pos (h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ <= a₂
 -> a₁ • b <= a₂ • b) : SMulPosMono α β where smul_le_smul_of_nonneg_right b hb 
a₁ a₂ h
参数：h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ <= a₂ -> a₁ • b <= a₂ • b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
A constructor for `SMulPosMono` requiring you to prove `a₁ ≤ a₂ → a₁ • b ≤ a₂ • 
b` only when
`0 < b`
-/
lemma SMulPosMono.of_pos (h₀ : ∀ b : β, 0 < b → ∀ a₁ a₂ : α, a₁ ≤ a₂ → a₁ • b ≤ a₂ • b) :
    SMulPosMono α β where
  smul_le_smul_of_nonneg_right b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb]
    · exact h₀ _ hb _ _ h

/-- A constructor for `SMulPosReflectLT` requiring you to prove `a₁ • b < a₂ • b → a₁ < a₂` only
when `0 < b` -/
/-
**SMulPosReflectLT.of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLT.of_pos (h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ 
• b < a₂ • b -> a₁ < a₂) : SMulPosReflectLT α β where lt_of_smul_lt_smul_right b
 hb a₁ a₂ h
参数：h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ • b < a₂ • b -> a₁ < a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
A constructor for `SMulPosReflectLT` requiring you to prove `a₁ • b < a₂ • b → a
₁ < a₂` only
when `0 < b`
-/
lemma SMulPosReflectLT.of_pos (h₀ : ∀ b : β, 0 < b → ∀ a₁ a₂ : α, a₁ • b < a₂ • b → a₁ < a₂) :
    SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb] at h
    · exact h₀ _ hb _ _ h

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosSMulStrictMono.toPosSMulMono [PosSMulStrictMono α β] :
    PosSMulMono α β :=
  PosSMulMono.of_pos fun _a ha ↦ (strictMono_smul_left_of_pos ha).monotone

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SMulPosStrictMono.toSMulPosMono [SMulPosStrictMono α β] :
    SMulPosMono α β :=
  SMulPosMono.of_pos fun _b hb ↦ (strictMono_smul_right_of_pos hb).monotone

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosSMulReflectLE.toPosSMulReflectLT [PosSMulReflectLE α β] :
    PosSMulReflectLT α β :=
  PosSMulReflectLT.of_pos fun a ha b₁ b₂ h ↦
    (le_of_smul_le_smul_of_pos_left h.le ha).lt_of_ne <| by rintro rfl; simp at h

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SMulPosReflectLE.toSMulPosReflectLT [SMulPosReflectLE α β] :
    SMulPosReflectLT α β :=
  SMulPosReflectLT.of_pos fun b hb a₁ a₂ h ↦
    (le_of_smul_le_smul_of_pos_right h.le hb).lt_of_ne <| by rintro rfl; simp at h

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsStrictOrderedModule.toIsOrderedModule [IsStrictOrderedModule α β] :
    IsOrderedModule α β where
/-
**smul_eq_smul_iff_eq_and_eq_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_smul_iff_eq_and_eq_of_pos [PosSMulStrictMono α β] [SMulPosStrictMo
no α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₁ : 0 < a₁) (h₂ : 0 < b₂) : a₁ • b₁ = 
a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
参数：ha : a₁ <= a₂；hb : b₁ <= b₂；h₁ : 0 < a₁；h₂ : 0 < b₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `SMulPosStrictMono.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
-/
lemma smul_eq_smul_iff_eq_and_eq_of_pos [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₁ : 0 < a₁) (h₂ : 0 < b₂) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_lt ?_, fun hb ↦ h.not_lt ?_⟩
  · exact (smul_le_smul_of_nonneg_left hb h₁.le).trans_lt (smul_lt_smul_of_pos_right ha h₂)
  · exact (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂.le)
/-
**smul_eq_smul_iff_eq_and_eq_of_pos'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_smul_iff_eq_and_eq_of_pos' [PosSMulStrictMono α β] [SMulPosStrictM
ono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₂ : 0 < a₂) (h₁ : 0 < b₁) : a₁ • b₁ =
 a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
参数：ha : a₁ <= a₂；hb : b₁ <= b₂；h₂ : 0 < a₂；h₁ : 0 < b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `SMulPosStrictMono.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma smul_eq_smul_iff_eq_and_eq_of_pos' [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₂ : 0 < a₂) (h₁ : 0 < b₁) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_lt ?_, fun hb ↦ h.not_lt ?_⟩
  · exact (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂.le)
  · exact (smul_le_smul_of_nonneg_right ha h₁.le).trans_lt (smul_lt_smul_of_pos_left hb h₂)

end PartialOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

/-
**pos_and_pos_or_neg_and_neg_of_smul_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pos_and_pos_or_neg_and_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β]
 (hab : 0 < a • b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
参数：hab : 0 < a • b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用引理 `smul_nonpos_of_nonpos_of_nonneg`：smul_nonpos_of_nonpos_of_nonneg [SMulPo
sMono α β] (ha : a <= 0) (hb : 0 <= b) : a • b <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_nonpos_of_nonneg_of_nonpos`：smul_nonpos_of_nonneg_of_nonpos [PosSMu
lMono α β] (ha : 0 <= a) (hb : b <= 0) : a • b <= 0
-/
lemma pos_and_pos_or_neg_and_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  obtain ha | rfl | ha := lt_trichotomy a 0
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb ↦ ?_) hab⟩
    exact smul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_smul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb ↦ ?_) hab⟩
    exact smul_nonpos_of_nonneg_of_nonpos ha.le hb
/-
**neg_of_smul_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_smul_pos_right [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) 
(ha : a <= 0) : b < 0
参数：h : 0 < a • b；ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `pos_and_pos_or_neg_and_neg_of_smul_pos`：pos_and_pos_or_neg_and_neg_of_sm
ul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) : 0 < a ∧ 0 < b ∨ a
 < 0 ∧ b < 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma neg_of_smul_pos_right [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : a ≤ 0) :
    b < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.1.not_ge ha).2
/-
**neg_of_smul_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (
ha : b <= 0) : a < 0
参数：h : 0 < a • b；ha : b <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `pos_and_pos_or_neg_and_neg_of_smul_pos`：pos_and_pos_or_neg_and_neg_of_sm
ul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) : 0 < a ∧ 0 < b ∨ a
 < 0 ∧ b < 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b ≤ 0) :
    a < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h ↦ h.2.not_ge ha).1
/-
**neg_iff_neg_of_smul_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_iff_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a •
 b) : a < 0 ↔ b < 0
参数：hab : 0 < a • b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `neg_of_smul_pos_right`：neg_of_smul_pos_right [PosSMulMono α β] [SMulPosM
ono α β] (h : 0 < a • b) (ha : a <= 0) : b < 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `neg_of_smul_pos_left`：neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMon
o α β] (h : 0 < a • b) (ha : b <= 0) : a < 0
-/
lemma neg_iff_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    a < 0 ↔ b < 0 :=
  ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩
/-
**neg_of_smul_neg_left'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_smul_neg_left' [SMulPosMono α β] (h : a • b < 0) (ha : 0 <= a) : b 
< 0
参数：h : a • b < 0；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `smul_nonneg'`：smul_nonneg' [SMulPosMono α β] (ha : 0 <= a) (hb : 0 <= b₁
) : 0 <= a • b₁
-/
lemma neg_of_smul_neg_left' [SMulPosMono α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun hb ↦ (smul_nonneg' ha hb).not_gt h
/-
**neg_of_smul_neg_right'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_smul_neg_right' [PosSMulMono α β] (h : a • b < 0) (hb : 0 <= b) : a
 < 0
参数：h : a • b < 0；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
-/
lemma neg_of_smul_neg_right' [PosSMulMono α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun ha ↦ (smul_nonneg ha hb).not_gt h

end LinearOrder
end SMulWithZero

section MulAction
variable [Monoid α] [Zero β] [MulAction α β]

section Preorder
variable [Preorder α] [Preorder β]

@[simp]
/-
**le_smul_iff_one_le_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_smul_iff_one_le_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 <
 b) : b <= a • b ↔ 1 <= a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `smul_le_smul_iff_of_pos_right`：smul_le_smul_iff_of_pos_right [SMulPosMon
o α β] [SMulPosReflectLE α β] (hb : 0 < b) : a₁ • b <= a₂ • b ↔ a₁ <= a₂
-/
lemma le_smul_iff_one_le_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    b ≤ a • b ↔ 1 ≤ a := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
/-
**lt_smul_iff_one_lt_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_smul_iff_one_lt_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb
 : 0 < b) : b < a • b ↔ 1 < a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `smul_lt_smul_iff_of_pos_right`：smul_lt_smul_iff_of_pos_right [SMulPosStr
ictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) : a₁ • b < a₂ • b ↔ a₁ < a₂
-/
lemma lt_smul_iff_one_lt_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    b < a • b ↔ 1 < a := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

@[simp]
/-
**smul_le_iff_le_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_iff_le_one_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 <
 b) : a • b <= b ↔ a <= 1
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `smul_le_smul_iff_of_pos_right`：smul_le_smul_iff_of_pos_right [SMulPosMon
o α β] [SMulPosReflectLE α β] (hb : 0 < b) : a₁ • b <= a₂ • b ↔ a₁ <= a₂
-/
lemma smul_le_iff_le_one_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a • b ≤ b ↔ a ≤ 1 := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
/-
**smul_lt_iff_lt_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_iff_lt_one_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb
 : 0 < b) : a • b < b ↔ a < 1
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `smul_lt_smul_iff_of_pos_right`：smul_lt_smul_iff_of_pos_right [SMulPosStr
ictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) : a₁ • b < a₂ • b ↔ a₁ < a₂
-/
lemma smul_lt_iff_lt_one_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    a • b < b ↔ a < 1 := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)
/-
**smul_le_of_le_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_of_le_one_left [SMulPosMono α β] (hb : 0 <= b) (h : a <= 1) : a • 
b <= b
参数：hb : 0 <= b；h : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma smul_le_of_le_one_left [SMulPosMono α β] (hb : 0 ≤ b) (h : a ≤ 1) : a • b ≤ b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb
/-
**le_smul_of_one_le_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_smul_of_one_le_left [SMulPosMono α β] (hb : 0 <= b) (h : 1 <= a) : b <=
 a • b
参数：hb : 0 <= b；h : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
lemma le_smul_of_one_le_left [SMulPosMono α β] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a • b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb
/-
**smul_lt_of_lt_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_of_lt_one_left [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1) : 
a • b < b
参数：hb : 0 < b；h : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma smul_lt_of_lt_one_left [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1) : a • b < b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb
/-
**lt_smul_of_one_lt_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_smul_of_one_lt_left [SMulPosStrictMono α β] (hb : 0 < b) (h : 1 < a) : 
b < a • b
参数：hb : 0 < b；h : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
lemma lt_smul_of_one_lt_left [SMulPosStrictMono α β] (hb : 0 < b) (h : 1 < a) : b < a • b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

end Preorder
end MulAction

section Semiring
variable [Semiring α] [AddCommGroup β] [Module α β]

/-- Constructor for `PosSMulMono` when the semimodule is in fact a group. -/
/-
**PosSMulMono.of_smul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulMono.of_smul_nonneg [PartialOrder α] [PartialOrder β] [IsOrderedAdd
Monoid β] (h : forall a : α, 0 <= a -> forall b : β, 0 <= b -> 0 <= a • b) : Pos
SMulMono α β where smul_le_smul_of_nonneg_left _a ha b₁ b₂
参数：h : forall a : α, 0 <= a -> forall b : β, 0 <= b -> 0 <= a • b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y

--- 原说明 ---
Constructor for `PosSMulMono` when the semimodule is in fact a group.
-/
lemma PosSMulMono.of_smul_nonneg [PartialOrder α] [PartialOrder β] [IsOrderedAddMonoid β]
    (h : ∀ a : α, 0 ≤ a → ∀ b : β, 0 ≤ b → 0 ≤ a • b) : PosSMulMono α β where
  smul_le_smul_of_nonneg_left _a ha b₁ b₂ := by simpa [sub_nonneg, smul_sub] using h _ ha (b₂ - b₁)

variable [IsDomain α] [Module.IsTorsionFree α β]

section PartialOrder
variable [Preorder α] [PartialOrder β]

/-
**PosSMulMono.toPosSMulStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulMono.toPosSMulStrictMono [PosSMulMono α β] : PosSMulStrictMono α β
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma PosSMulMono.toPosSMulStrictMono [PosSMulMono α β] : PosSMulStrictMono α β :=
  ⟨fun _a ha _b₁ _b₂ hb ↦ (smul_le_smul_of_nonneg_left hb.le ha.le).lt_of_ne <|
    (smul_right_injective _ ha.ne').ne hb.ne⟩
/-
**PosSMulReflectLT.toPosSMulReflectLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosSMulReflectLT.toPosSMulReflectLE [PosSMulReflectLT α β] : PosSMulReflec
tLE α β
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
-/
instance PosSMulReflectLT.toPosSMulReflectLE [PosSMulReflectLT α β] : PosSMulReflectLE α β :=
  ⟨fun _a ha _b₁ _b₂ h ↦ h.eq_or_lt.elim
    (fun h ↦ (smul_right_injective _ ha.ne' h).le) fun h' ↦
    (lt_of_smul_lt_smul_left h' ha.le).le⟩

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

/-
**posSMulMono_iff_posSMulStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：posSMulMono_iff_posSMulStrictMono : PosSMulMono α β ↔ PosSMulStrictMono α 
β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulMono.toPosSMulStrictMono`：PosSMulMono.toPosSMulStrictMono [PosSMu
lMono α β] : PosSMulStrictMono α β
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
-/
lemma posSMulMono_iff_posSMulStrictMono : PosSMulMono α β ↔ PosSMulStrictMono α β :=
  ⟨fun _ ↦ PosSMulMono.toPosSMulStrictMono, fun _ ↦ inferInstance⟩
/-
**PosSMulReflectLE_iff_posSMulReflectLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulReflectLE_iff_posSMulReflectLT : PosSMulReflectLE α β ↔ PosSMulRefl
ectLT α β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulReflectLE.toPosSMulReflectLT`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrde
r α]   [inst_4 : PartialO…
-/
lemma PosSMulReflectLE_iff_posSMulReflectLT : PosSMulReflectLE α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLT.toPosSMulReflectLE⟩

end PartialOrder
end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

/-- Constructor for `IsOrderedModule` when the semimodule is in fact a module. -/
/-
**IsOrderedModule.of_smul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderedModule.of_smul_nonneg [IsOrderedAddMonoid α] [IsOrderedAddMonoid 
β] (h : forall a : α, 0 <= a -> forall b : β, 0 <= b -> 0 <= a • b) : IsOrderedM
odule α β where toPosSMulMono
参数：h : forall a : α, 0 <= a -> forall b : β, 0 <= b -> 0 <= a • b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulMono.of_smul_nonneg`：PosSMulMono.of_smul_nonneg [PartialOrder α] 
[PartialOrder β] [IsOrderedAddMonoid β] (h : forall a : α, 0 <= a -> forall b : 
β, 0 <= b -> 0 <…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y

--- 原说明 ---
Constructor for `IsOrderedModule` when the semimodule is in fact a module.
-/
lemma IsOrderedModule.of_smul_nonneg [IsOrderedAddMonoid α] [IsOrderedAddMonoid β]
    (h : ∀ a : α, 0 ≤ a → ∀ b : β, 0 ≤ b → 0 ≤ a • b) : IsOrderedModule α β where
  toPosSMulMono := .of_smul_nonneg h
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ := by
    simpa [sub_nonneg, sub_smul] using (h (a₂ - a₁) · _ hb)

variable [IsDomain α] [Module.IsTorsionFree α β]
/-
**SMulPosMono.toSMulPosStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosMono.toSMulPosStrictMono [SMulPosMono α β] : SMulPosStrictMono α β
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma SMulPosMono.toSMulPosStrictMono [SMulPosMono α β] : SMulPosStrictMono α β :=
  ⟨fun _b hb _a₁ _a₂ ha ↦ (smul_le_smul_of_nonneg_right ha.le hb.le).lt_of_ne <|
    (smul_left_injective _ hb.ne').ne ha.ne⟩
/-
**smulPosMono_iff_smulPosStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smulPosMono_iff_smulPosStrictMono : SMulPosMono α β ↔ SMulPosStrictMono α 
β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosMono.toSMulPosStrictMono`：SMulPosMono.toSMulPosStrictMono [SMulPo
sMono α β] : SMulPosStrictMono α β
· 使用定理 `SMulPosStrictMono.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
-/
lemma smulPosMono_iff_smulPosStrictMono : SMulPosMono α β ↔ SMulPosStrictMono α β :=
  ⟨fun _ ↦ SMulPosMono.toSMulPosStrictMono, fun _ ↦ inferInstance⟩
/-
**SMulPosReflectLT.toSMulPosReflectLE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLT.toSMulPosReflectLE [SMulPosReflectLT α β] : SMulPosReflec
tLE α β
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
-/
lemma SMulPosReflectLT.toSMulPosReflectLE [SMulPosReflectLT α β] : SMulPosReflectLE α β :=
  ⟨fun _b hb _a₁ _a₂ h ↦ h.eq_or_lt.elim (fun h ↦ (smul_left_injective _ hb.ne' h).le) fun h' ↦
    (lt_of_smul_lt_smul_right h' hb.le).le⟩
/-
**SMulPosReflectLE_iff_smulPosReflectLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLE_iff_smulPosReflectLT : SMulPosReflectLE α β ↔ SMulPosRefl
ectLT α β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulPosReflectLE.toSMulPosReflectLT`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrde
r α]   [inst_4 : PartialO…
· 使用引理 `SMulPosReflectLT.toSMulPosReflectLE`：SMulPosReflectLT.toSMulPosReflectLE
 [SMulPosReflectLT α β] : SMulPosReflectLE α β
-/
lemma SMulPosReflectLE_iff_smulPosReflectLT : SMulPosReflectLE α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ SMulPosReflectLT.toSMulPosReflectLE⟩

end Ring

section GroupWithZero
variable [GroupWithZero α] [Preorder α] [Preorder β] [MulAction α β]

/-
**inv_smul_le_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_smul_le_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < 
a) : a⁻¹ • b₁ <= b₂ ↔ b₁ <= a • b₂
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_le_smul_iff_of_pos_left`：smul_le_smul_iff_of_pos_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : 0 < a) : a • b₁ <= a • b₂ ↔ b₁ <= b₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_smul_le_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a⁻¹ • b₁ ≤ b₂ ↔ b₁ ≤ a • b₂ := by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
/-
**le_inv_smul_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_inv_smul_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < 
a) : b₁ <= a⁻¹ • b₂ ↔ a • b₁ <= b₂
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_le_smul_iff_of_pos_left`：smul_le_smul_iff_of_pos_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : 0 < a) : a • b₁ <= a • b₂ ↔ b₁ <= b₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_inv_smul_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    b₁ ≤ a⁻¹ • b₂ ↔ a • b₁ ≤ b₂ := by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
/-
**inv_smul_lt_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_smul_lt_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha 
: 0 < a) : a⁻¹ • b₁ < b₂ ↔ b₁ < a • b₂
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_smul_lt_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a⁻¹ • b₁ < b₂ ↔ b₁ < a • b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']
/-
**lt_inv_smul_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_inv_smul_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha 
: 0 < a) : b₁ < a⁻¹ • b₂ ↔ a • b₁ < b₂
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_inv_smul_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    b₁ < a⁻¹ • b₂ ↔ a • b₁ < b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

/-- Right scalar multiplication as an order isomorphism. -/
@[simps!]
/-
**OrderIso.smulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.smulRight [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 
0 < a) : β ≃o β where toEquiv
参数：ha : 0 < a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right scalar multiplication as an order isomorphism.
-/
def OrderIso.smulRight [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 0 < a) : β ≃o β where
  toEquiv := Equiv.smulRight ha.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos_left ha

end GroupWithZero

namespace OrderDual

section Left
variable [Preorder α] [Preorder β] [SMul α β] [Zero α]

/-
**OrderDual.instPosSMulMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instPosSMulMono [PosSMulMono α β] : PosSMulMono α βᵒᵈ where smul_le_smul_o
f_nonneg_left _a ha _b₁ _b₂ hb
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α βᵒᵈ where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb := smul_le_smul_of_nonneg_left (β := β) hb ha
/-
**OrderDual.instPosSMulStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α βᵒᵈ wh
ere smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α βᵒᵈ where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb := smul_lt_smul_of_pos_left (β := β) hb ha
/-
**OrderDual.instPosSMulReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instPosSMulReflectLT [PosSMulReflectLT α β] : PosSMulReflectLT α βᵒᵈ where
 lt_of_smul_lt_smul_left _a ha _b₁ _b₂ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_smul_lt_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : 
α} {b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [
inst_3 : Zero α] [PosSM…
-/
instance instPosSMulReflectLT [PosSMulReflectLT α β] : PosSMulReflectLT α βᵒᵈ where
  lt_of_smul_lt_smul_left _a ha _b₁ _b₂ h := lt_of_smul_lt_smul_of_nonneg_left (β := β) h ha
/-
**OrderDual.instPosSMulReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α βᵒᵈ where
 le_of_smul_le_smul_left _a ha _b₁ _b₂ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_smul_le_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} 
{b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [ins
t_3 : Zero α] [PosSM…
-/
instance instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α βᵒᵈ where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h := le_of_smul_le_smul_of_pos_left (β := β) h ha

end Left

section Right
variable [Preorder α] [Monoid α] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [DistribMulAction α β]

/-
**OrderDual.instSMulPosMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instSMulPosMono [SMulPosMono α β] : SMulPosMono α βᵒᵈ where smul_le_smul_o
f_nonneg_right _b hb a₁ a₂ ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `OrderDual.addRightMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c
 : AddRightMono α], AddRightMono αᵒᵈ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
-/
instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α βᵒᵈ where
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ ha := by
    rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg]
    exact smul_le_smul_of_nonneg_right (β := β) ha <| neg_nonneg.2 hb
/-
**OrderDual.instSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α βᵒᵈ wh
ere smul_lt_smul_of_pos_right _b hb a₁ a₂ ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `OrderDual.addLeftStrictMono`：∀ {α : Type u} [inst : LT α] [inst_1 : Add 
α] [c : AddLeftStrictMono α], AddLeftStrictMono αᵒᵈ
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `OrderDual.addRightStrictMono`：∀ {α : Type u} [inst : LT α] [inst_1 : Add
 α] [c : AddRightStrictMono α], AddRightStrictMono αᵒᵈ
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
-/
instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α βᵒᵈ where
  smul_lt_smul_of_pos_right _b hb a₁ a₂ ha := by
    rw [← neg_lt_neg_iff, ← smul_neg, ← smul_neg]
    exact smul_lt_smul_of_pos_right (β := β) ha <| neg_pos.2 hb
/-
**OrderDual.instSMulPosReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α βᵒᵈ where
 lt_of_smul_lt_smul_right _b hb a₁ a₂ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `OrderDual.addLeftStrictMono`：∀ {α : Type u} [inst : LT α] [inst_1 : Add 
α] [c : AddLeftStrictMono α], AddLeftStrictMono αᵒᵈ
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `OrderDual.addRightStrictMono`：∀ {α : Type u} [inst : LT α] [inst_1 : Add
 α] [c : AddRightStrictMono α], AddRightStrictMono αᵒᵈ
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
-/
instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α βᵒᵈ where
  lt_of_smul_lt_smul_right _b hb a₁ a₂ h := by
    rw [← neg_lt_neg_iff, ← smul_neg, ← smul_neg] at h
    exact lt_of_smul_lt_smul_right (β := β) h <| neg_nonneg.2 hb
/-
**OrderDual.instSMulPosReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α βᵒᵈ where
 le_of_smul_le_smul_right _b hb a₁ a₂ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_right`：le_of_smul_le_smul_right [SMulPosReflectLE α β
] (h : a₁ • b <= a₂ • b) (hb : 0 < b) : a₁ <= a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `OrderDual.addRightMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c
 : AddRightMono α], AddRightMono αᵒᵈ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
instance instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α βᵒᵈ where
  le_of_smul_le_smul_right _b hb a₁ a₂ h := by
    rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg] at h
    exact le_of_smul_le_smul_right (β := β) h <| neg_pos.2 hb

end Right

section LeftRight
variable [Preorder α] [MonoidWithZero α] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [DistribMulAction α β]

/-
**OrderDual.instIsOrderedModule** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : MonoidWithZe
ro α] [inst_2 : AddCommGroup β]   [inst_3 : PartialOrder β] [IsOrderedAddMonoid 
β] [inst_5 : DistribMulAction α β] [IsOrderedModule α β],   IsOrderedModule α βᵒ
ᵈ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
-/
instance instIsOrderedModule [IsOrderedModule α β] : IsOrderedModule α βᵒᵈ where
/-
**OrderDual.instIsStrictOrderedModule** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : MonoidWithZe
ro α] [inst_2 : AddCommGroup β]   [inst_3 : PartialOrder β] [IsOrderedAddMonoid 
β] [inst_5 : DistribMulAction α β] [IsStrictOrderedModule α β],   IsStrictOrdere
dModule α βᵒᵈ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toSMulPosStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
-/
instance instIsStrictOrderedModule [IsStrictOrderedModule α β] : IsStrictOrderedModule α βᵒᵈ where

end LeftRight
end OrderDual

section OrderedAddCommMonoid
variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

section PosSMulMono
variable [PosSMulMono α β] {a₁ a₂ : α} {b₁ b₂ : β}

/-- Binary **rearrangement inequality**. -/
/-
**smul_add_smul_le_smul_add_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_add_smul_le_smul_add_smul (ha : a₁ <= a₂) (hb : b₁ <= b₂) : a₁ • b₂ +
 a₂ • b₁ <= a₁ • b₁ + a₂ • b₂
参数：ha : a₁ <= a₂；hb : b₁ <= b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nonneg_add_of_le`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 
: Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftReflectLE α],   a ≤ b → ∃ c, 0
 ≤ c ∧ a + c …
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…

--- 原说明 ---
Binary **rearrangement inequality**.
-/
lemma smul_add_smul_le_smul_add_smul (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ • b₂ + a₂ • b₁ ≤ a₁ • b₁ + a₂ • b₂ := by
  obtain ⟨a, ha₀, rfl⟩ := exists_nonneg_add_of_le ha
  rw [add_smul, add_smul, add_left_comm]
  gcongr

/-- Binary **rearrangement inequality**. -/
/-
**smul_add_smul_le_smul_add_smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_add_smul_le_smul_add_smul' (ha : a₂ <= a₁) (hb : b₂ <= b₁) : a₁ • b₂ 
+ a₂ • b₁ <= a₁ • b₁ + a₂ • b₂
参数：ha : a₂ <= a₁；hb : b₂ <= b₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `smul_add_smul_le_smul_add_smul`：smul_add_smul_le_smul_add_smul (ha : a₁ 
<= a₂) (hb : b₁ <= b₂) : a₁ • b₂ + a₂ • b₁ <= a₁ • b₁ + a₂ • b₂

--- 原说明 ---
Binary **rearrangement inequality**.
-/
lemma smul_add_smul_le_smul_add_smul' (ha : a₂ ≤ a₁) (hb : b₂ ≤ b₁) :
    a₁ • b₂ + a₂ • b₁ ≤ a₁ • b₁ + a₂ • b₂ := by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_le_smul_add_smul ha hb

end PosSMulMono

section PosSMulStrictMono
variable [PosSMulStrictMono α β] {a₁ a₂ : α} {b₁ b₂ : β}

/-- Binary strict **rearrangement inequality**. -/
/-
**smul_add_smul_lt_smul_add_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_add_smul_lt_smul_add_smul (ha : a₁ < a₂) (hb : b₁ < b₂) : a₁ • b₂ + a
₂ • b₁ < a₁ • b₁ + a₂ • b₂
参数：ha : a₁ < a₂；hb : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iff_exists_pos_add`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftStrictMono α]   [AddLeftReflectL
T α], a < b…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…

--- 原说明 ---
Binary strict **rearrangement inequality**.
-/
lemma smul_add_smul_lt_smul_add_smul (ha : a₁ < a₂) (hb : b₁ < b₂) :
    a₁ • b₂ + a₂ • b₁ < a₁ • b₁ + a₂ • b₂ := by
  obtain ⟨a, ha₀, rfl⟩ := lt_iff_exists_pos_add.1 ha
  rw [add_smul, add_smul, add_left_comm]
  gcongr

/-- Binary strict **rearrangement inequality**. -/
/-
**smul_add_smul_lt_smul_add_smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_add_smul_lt_smul_add_smul' (ha : a₂ < a₁) (hb : b₂ < b₁) : a₁ • b₂ + 
a₂ • b₁ < a₁ • b₁ + a₂ • b₂
参数：ha : a₂ < a₁；hb : b₂ < b₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `smul_add_smul_lt_smul_add_smul`：smul_add_smul_lt_smul_add_smul (ha : a₁ 
< a₂) (hb : b₁ < b₂) : a₁ • b₂ + a₂ • b₁ < a₁ • b₁ + a₂ • b₂

--- 原说明 ---
Binary strict **rearrangement inequality**.
-/
lemma smul_add_smul_lt_smul_add_smul' (ha : a₂ < a₁) (hb : b₂ < b₁) :
    a₁ • b₂ + a₂ • b₁ < a₁ • b₁ + a₂ • b₂ := by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_lt_smul_add_smul ha hb

end PosSMulStrictMono
end OrderedAddCommMonoid

section OrderedRing
variable [Ring α] [PartialOrder α] [IsOrderedRing α]

section OrderedAddCommGroup
variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module α β]

section PosSMulMono
variable [PosSMulMono α β]

/-
**smul_le_smul_of_nonpos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_smul_of_nonpos_left (h : b₁ <= b₂) (ha : a <= 0) : a • b₂ <= a • b
₁
参数：h : b₁ <= b₂；ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
lemma smul_le_smul_of_nonpos_left (h : b₁ ≤ b₂) (ha : a ≤ 0) : a • b₂ ≤ a • b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff]
  exact smul_le_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)
/-
**antitone_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·) : β -> β)
参数：ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_le_smul_of_nonpos_left`：smul_le_smul_of_nonpos_left (h : b₁ <= b₂) 
(ha : a <= 0) : a • b₂ <= a • b₁
-/
lemma antitone_smul_left (ha : a ≤ 0) : Antitone ((a • ·) : β → β) :=
  fun _ _ h ↦ smul_le_smul_of_nonpos_left h ha
/-
**PosSMulMono.toSMulPosMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosSMulMono.toSMulPosMono : SMulPosMono α β where smul_le_smul_of_nonneg_r
ight _b hb a₁ a₂ ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
instance PosSMulMono.toSMulPosMono : SMulPosMono α β where
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ ha := by
    rw [← sub_nonneg, ← sub_smul]; exact smul_nonneg (sub_nonneg.2 ha) hb

end PosSMulMono

section PosSMulStrictMono
variable [PosSMulStrictMono α β]

/-
**smul_lt_smul_of_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_of_neg_left (hb : b₁ < b₂) (ha : a < 0) : a • b₂ < a • b₁
参数：hb : b₁ < b₂；ha : a < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
lemma smul_lt_smul_of_neg_left (hb : b₁ < b₂) (ha : a < 0) : a • b₂ < a • b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff]
  exact smul_lt_smul_of_pos_left hb (neg_pos_of_neg ha)
/-
**strictAnti_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_smul_left (ha : a < 0) : StrictAnti ((a • ·) : β -> β)
参数：ha : a < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_lt_smul_of_neg_left`：smul_lt_smul_of_neg_left (hb : b₁ < b₂) (ha : 
a < 0) : a • b₂ < a • b₁
-/
lemma strictAnti_smul_left (ha : a < 0) : StrictAnti ((a • ·) : β → β) :=
  fun _ _ h ↦ smul_lt_smul_of_neg_left h ha
/-
**PosSMulStrictMono.toSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosSMulStrictMono.toSMulPosStrictMono : SMulPosStrictMono α β where smul_l
t_smul_of_pos_right _b hb a₁ a₂ ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_pos`：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0
 < a • b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
instance PosSMulStrictMono.toSMulPosStrictMono : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right _b hb a₁ a₂ ha := by
    rw [← sub_pos, ← sub_smul]; exact smul_pos (sub_pos.2 ha) hb

end PosSMulStrictMono

/-
**le_of_smul_le_smul_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_smul_le_smul_of_neg [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (h
a : a < 0) : b₂ <= b₁
参数：h : a • b₁ <= a • b₂；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_smul_le_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} 
{b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [ins
t_3 : Zero α] [PosSM…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
lemma le_of_smul_le_smul_of_neg [PosSMulReflectLE α β] (h : a • b₁ ≤ a • b₂) (ha : a < 0) :
    b₂ ≤ b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff] at h
  exact le_of_smul_le_smul_of_pos_left h <| neg_pos.2 ha
/-
**lt_of_smul_lt_smul_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_smul_lt_smul_of_nonpos [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) 
(ha : a <= 0) : b₂ < b₁
参数：h : a • b₁ < a • b₂；ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_smul_lt_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : 
α} {b₁ b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [
inst_3 : Zero α] [PosSM…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
lemma lt_of_smul_lt_smul_of_nonpos [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : a ≤ 0) :
    b₂ < b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

omit [IsOrderedRing α] in
/-
**smul_nonneg_of_nonpos_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg_of_nonpos_of_nonpos [SMulPosMono α β] (ha : a <= 0) (hb : b <=
 0) : 0 <= a • b
参数：ha : a <= 0；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_nonpos_of_nonpos_of_nonneg`：smul_nonpos_of_nonpos_of_nonneg [SMulPo
sMono α β] (ha : a <= 0) (hb : 0 <= b) : a • b <= 0
-/
lemma smul_nonneg_of_nonpos_of_nonpos [SMulPosMono α β] (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a • b :=
  smul_nonpos_of_nonpos_of_nonneg (β := βᵒᵈ) ha hb
/-
**smul_le_smul_iff_of_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_le_smul_iff_of_neg_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha 
: a < 0) : a • b₁ <= a • b₂ ↔ b₂ <= b₁
参数：ha : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `smul_le_smul_iff_of_pos_left`：smul_le_smul_iff_of_pos_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : 0 < a) : a • b₁ <= a • b₂ ↔ b₁ <= b₂
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
lemma smul_le_smul_iff_of_neg_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : a < 0) :
    a • b₁ ≤ a • b₂ ↔ b₂ ≤ b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos_left (neg_pos_of_neg ha)

section PosSMulStrictMono
variable [PosSMulStrictMono α β] [PosSMulReflectLT α β]

/-
**smul_lt_smul_iff_of_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lt_smul_iff_of_neg_left (ha : a < 0) : a • b₁ < a • b₂ ↔ b₂ < b₁
参数：ha : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
lemma smul_lt_smul_iff_of_neg_left (ha : a < 0) : a • b₁ < a • b₂ ↔ b₂ < b₁ := by
  rw [← neg_neg a, neg_smul, neg_smul (-a), neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos_left (neg_pos_of_neg ha)
/-
**smul_pos_iff_of_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_pos_iff_of_neg_left (ha : a < 0) : 0 < a • b ↔ b < 0
参数：ha : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_lt_smul_iff_of_neg_left`：smul_lt_smul_iff_of_neg_left (ha : a < 0) 
: a • b₁ < a • b₂ ↔ b₂ < b₁
-/
lemma smul_pos_iff_of_neg_left (ha : a < 0) : 0 < a • b ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₁ := (0 : β))

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg_left
/-
**smul_neg_iff_of_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_neg_iff_of_neg_left (ha : a < 0) : a • b < 0 ↔ 0 < b
参数：ha : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_lt_smul_iff_of_neg_left`：smul_lt_smul_iff_of_neg_left (ha : a < 0) 
: a • b₁ < a • b₂ ↔ b₂ < b₁
-/
lemma smul_neg_iff_of_neg_left (ha : a < 0) : a • b < 0 ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₂ := (0 : β))

end PosSMulStrictMono
end OrderedAddCommGroup

section LinearOrderedAddCommGroup
variable [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulMono α β]
  {a : α} {b b₁ b₂ : β}

/-
**smul_max_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_max_of_nonpos (ha : a <= 0) (b₁ b₂ : β) : a • max b₁ b₂ = min (a • b₁
) (a • b₂)
参数：ha : a <= 0；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_max`：Antitone.map_max (hf : Antitone f) : f (max a b) = min
 (f a) (f b)
· 使用引理 `antitone_smul_left`：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·)
 : β -> β)
-/
lemma smul_max_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • max b₁ b₂ = min (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : β → β)).map_max
/-
**smul_min_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_min_of_nonpos (ha : a <= 0) (b₁ b₂ : β) : a • min b₁ b₂ = max (a • b₁
) (a • b₂)
参数：ha : a <= 0；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Antitone f → f (min a b) = max (f
 a) (f…
· 使用引理 `antitone_smul_left`：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·)
 : β -> β)
-/
lemma smul_min_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • min b₁ b₂ = max (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : β → β)).map_min

end LinearOrderedAddCommGroup
end OrderedRing

section LinearOrderedRing
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulStrictMono α β]
  {a : α} {b : β}

/-
**nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 <= a • b) :
 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
参数：hab : 0 <= a • b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `smul_neg_of_pos_of_neg`：smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (
ha : 0 < a) (hb : b < 0) : a • b < 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `smul_neg_of_neg_of_pos`：smul_neg_of_neg_of_pos [SMulPosStrictMono α β] (
ha : a < 0) (hb : 0 < b) : a • b < 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 ≤ a • b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp only [Decidable.or_iff_not_not_and_not, not_and, not_le]
  refine fun ab nab ↦ hab.not_gt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]
/-
**smul_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg_iff : 0 <= a • b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg`：nonneg_and_nonneg
_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 <= a • b) : 0 <= a ∧ 0 <= b ∨ a <=
 0 ∧ b <= 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用引理 `smul_nonneg_of_nonpos_of_nonpos`：smul_nonneg_of_nonpos_of_nonpos [SMulPo
sMono α β] (ha : a <= 0) (hb : b <= 0) : 0 <= a • b
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma smul_nonneg_iff : 0 ≤ a • b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h ↦ h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩
/-
**smul_nonpos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_iff : a • b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_nonneg_iff`：smul_nonneg_iff : 0 <= a • b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0
 ∧ b <= 0
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma smul_nonpos_iff : a • b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, ← smul_neg, smul_nonneg_iff, neg_nonneg, neg_nonpos]
/-
**smul_nonneg_iff_pos_imp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg_iff_pos_imp_nonneg : 0 <= a • b ↔ (0 < a -> 0 <= b) ∧ (0 < b -
> 0 <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `smul_nonneg_iff`：smul_nonneg_iff : 0 <= a • b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0
 ∧ b <= 0
-/
lemma smul_nonneg_iff_pos_imp_nonneg : 0 ≤ a • b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) :=
  smul_nonneg_iff.trans <| by grind
/-
**smul_nonneg_iff_neg_imp_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonneg_iff_neg_imp_nonpos : 0 <= a • b ↔ (a < 0 -> b <= 0) ∧ (b < 0 -
> a <= 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用引理 `smul_nonneg_iff_pos_imp_nonneg`：smul_nonneg_iff_pos_imp_nonneg : 0 <= a 
• b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_nonneg_iff_neg_imp_nonpos : 0 ≤ a • b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]
/-
**smul_nonpos_iff_pos_imp_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_iff_pos_imp_nonpos : a • b <= 0 ↔ (0 < a -> b <= 0) ∧ (b < 0 -
> 0 <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_nonneg_iff_pos_imp_nonneg`：smul_nonneg_iff_pos_imp_nonneg : 0 <= a 
• b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_nonpos_iff_pos_imp_nonpos : a • b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]
/-
**smul_nonpos_iff_neg_imp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_nonpos_iff_neg_imp_nonneg : a • b <= 0 ↔ (a < 0 -> 0 <= b) ∧ (0 < b -
> a <= 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `smul_nonneg_iff_pos_imp_nonneg`：smul_nonneg_iff_pos_imp_nonneg : 0 <= a 
• b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_nonpos_iff_neg_imp_nonneg : a • b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_smul, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end LinearOrderedRing

namespace Prod
variable {γ : Type*} [Zero α]

section SMul
variable [Preorder α] [Preorder β] [Preorder γ] [SMul α β] [SMul α γ]

/-
**Prod.instPosSMulMono** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instPosSMulMono [PosSMulMono α β] [PosSMulMono α γ] : PosSMulMono α (β × γ
) where smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance instPosSMulMono [PosSMulMono α β] [PosSMulMono α γ] : PosSMulMono α (β × γ) where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb :=
    ⟨smul_le_smul_of_nonneg_left hb.1 ha, smul_le_smul_of_nonneg_left hb.2 ha⟩
/-
**Prod.instPosSMulReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instPosSMulReflectLE [PosSMulReflectLE α β] [PosSMulReflectLE α γ] : PosSM
ulReflectLE α (β × γ) where le_of_smul_le_smul_left _a ha _b₁ _b₂ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance instPosSMulReflectLE [PosSMulReflectLE α β] [PosSMulReflectLE α γ] :
    PosSMulReflectLE α (β × γ) where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h :=
    ⟨le_of_smul_le_smul_left h.1 ha, le_of_smul_le_smul_left h.2 ha⟩

variable [Zero β] [Zero γ]
/-
**Prod.instSMulPosMono** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSMulPosMono [SMulPosMono α β] [SMulPosMono α γ] : SMulPosMono α (β × γ
) where smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance instSMulPosMono [SMulPosMono α β] [SMulPosMono α γ] : SMulPosMono α (β × γ) where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha :=
    ⟨smul_le_smul_of_nonneg_right ha hb.1, smul_le_smul_of_nonneg_right ha hb.2⟩
/-
**Prod.instSMulPosReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSMulPosReflectLE [SMulPosReflectLE α β] [SMulPosReflectLE α γ] : SMulP
osReflectLE α (β × γ) where le_of_smul_le_smul_right _b hb _a₁ _a₂ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.lt_iff`：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 
< y.2
· 使用引理 `le_of_smul_le_smul_right`：le_of_smul_le_smul_right [SMulPosReflectLE α β
] (h : a₁ • b <= a₂ • b) (hb : 0 < b) : a₁ <= a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance instSMulPosReflectLE [SMulPosReflectLE α β] [SMulPosReflectLE α γ] :
    SMulPosReflectLE α (β × γ) where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h := by
    rcases lt_iff.mp hb with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · exact le_of_smul_le_smul_right h.1 h₁
    · exact le_of_smul_le_smul_right h.2 h₁

end SMul

section SMulWithZero
variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]
  [Zero β] [Zero γ] [SMulWithZero α β] [SMulWithZero α γ]

/-
**Prod.instPosSMulStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instPosSMulStrictMono [PosSMulStrictMono α β] [PosSMulStrictMono α γ] : Po
sSMulStrictMono α (β × γ) where smul_lt_smul_of_pos_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance instPosSMulStrictMono [PosSMulStrictMono α β] [PosSMulStrictMono α γ] :
    PosSMulStrictMono α (β × γ) where
  smul_lt_smul_of_pos_left := by
    simp_rw [lt_iff]
    rintro _a ha _b₁ _b₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact .inl ⟨smul_lt_smul_of_pos_left h₁ ha, smul_le_smul_of_nonneg_left h₂ ha.le⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_left h₁ ha.le, smul_lt_smul_of_pos_left h₂ ha⟩
/-
**Prod.instSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSMulPosStrictMono [SMulPosStrictMono α β] [SMulPosStrictMono α γ] : SM
ulPosStrictMono α (β × γ) where smul_lt_smul_of_pos_right
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `SMulPosStrictMono.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance instSMulPosStrictMono [SMulPosStrictMono α β] [SMulPosStrictMono α γ] :
    SMulPosStrictMono α (β × γ) where
  smul_lt_smul_of_pos_right := by
    simp_rw [lt_iff]
    rintro a (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) _b₁ _b₂ hb
    · exact .inl ⟨smul_lt_smul_of_pos_right hb h₁, smul_le_smul_of_nonneg_right hb.le h₂⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_right hb.le h₁, smul_lt_smul_of_pos_right hb h₂⟩
/-
**Prod.instSMulPosReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSMulPosReflectLT [SMulPosReflectLT α β] [SMulPosReflectLT α γ] : SMulP
osReflectLT α (β × γ) where lt_of_smul_lt_smul_right
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance instSMulPosReflectLT [SMulPosReflectLT α β] [SMulPosReflectLT α γ] :
    SMulPosReflectLT α (β × γ) where
  lt_of_smul_lt_smul_right := by
    simp_rw [lt_iff]
    rintro b hb _a₁ _a₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact lt_of_smul_lt_smul_right h₁ hb.1
    · exact lt_of_smul_lt_smul_right h₂ hb.2

end SMulWithZero
end Prod

namespace Pi
variable {ι : Type*} {β : ι → Type*} [Zero α]

section SMul
variable [Preorder α] [∀ i, Preorder (β i)] [∀ i, SMul α (β i)]

/-
**Pi.instPosSMulMono** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instPosSMulMono [forall i, PosSMulMono α (β i)] : PosSMulMono α (forall i,
 β i) where smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb i
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
instance instPosSMulMono [∀ i, PosSMulMono α (β i)] : PosSMulMono α (∀ i, β i) where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb i := smul_le_smul_of_nonneg_left (hb i) ha
/-
**Pi.instPosSMulReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instPosSMulReflectLE [forall i, PosSMulReflectLE α (β i)] : PosSMulReflect
LE α (forall i, β i) where le_of_smul_le_smul_left _a ha _b₁ _b₂ h i
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
-/
instance instPosSMulReflectLE [∀ i, PosSMulReflectLE α (β i)] : PosSMulReflectLE α (∀ i, β i) where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h i := le_of_smul_le_smul_left (h i) ha

variable [∀ i, Zero (β i)]
/-
**Pi.instSMulPosMono** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instSMulPosMono [forall i, SMulPosMono α (β i)] : SMulPosMono α (forall i,
 β i) where smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha i
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
instance instSMulPosMono [∀ i, SMulPosMono α (β i)] : SMulPosMono α (∀ i, β i) where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha i := smul_le_smul_of_nonneg_right ha (hb i)
/-
**Pi.instSMulPosReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instSMulPosReflectLE [forall i, SMulPosReflectLE α (β i)] : SMulPosReflect
LE α (forall i, β i) where le_of_smul_le_smul_right _b hb _a₁ _a₂ h
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用引理 `le_of_smul_le_smul_right`：le_of_smul_le_smul_right [SMulPosReflectLE α β
] (h : a₁ • b <= a₂ • b) (hb : 0 < b) : a₁ <= a₂
-/
instance instSMulPosReflectLE [∀ i, SMulPosReflectLE α (β i)] : SMulPosReflectLE α (∀ i, β i) where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h := by
    obtain ⟨-, i, hi⟩ := lt_def.1 hb; exact le_of_smul_le_smul_right (h _) hi

end SMul


section SMulWithZero
variable [∀ i, Zero (β i)] [PartialOrder α] [∀ i, PartialOrder (β i)] [∀ i, SMulWithZero α (β i)]

/-
**Pi.instPosSMulStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instPosSMulStrictMono [forall i, PosSMulStrictMono α (β i)] : PosSMulStric
tMono α (forall i, β i) where smul_lt_smul_of_pos_left
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
instance instPosSMulStrictMono [∀ i, PosSMulStrictMono α (β i)] :
    PosSMulStrictMono α (∀ i, β i) where
  smul_lt_smul_of_pos_left := by
    simp_rw [lt_def]
    rintro _a ha _b₁ _b₂ ⟨hb, i, hi⟩
    exact ⟨smul_le_smul_of_nonneg_left hb ha.le, i, smul_lt_smul_of_pos_left hi ha⟩
/-
**Pi.instSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instSMulPosStrictMono [forall i, SMulPosStrictMono α (β i)] : SMulPosStric
tMono α (forall i, β i) where smul_lt_smul_of_pos_right
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `SMulPosStrictMono.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
-/
instance instSMulPosStrictMono [∀ i, SMulPosStrictMono α (β i)] :
    SMulPosStrictMono α (∀ i, β i) where
  smul_lt_smul_of_pos_right := by
    simp_rw [lt_def]
    rintro a ⟨ha, i, hi⟩ _b₁ _b₂ hb
    exact ⟨smul_le_smul_of_nonneg_right hb.le ha, i, smul_lt_smul_of_pos_right hb hi⟩

-- Note: There is no interesting instance for `PosSMulReflectLT α (∀ i, β i)` that's not already
-- implied by the other instances
/-
**Pi.instSMulPosReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instSMulPosReflectLT [forall i, SMulPosReflectLT α (β i)] : SMulPosReflect
LT α (forall i, β i) where lt_of_smul_lt_smul_right
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
-/
instance instSMulPosReflectLT [∀ i, SMulPosReflectLT α (β i)] : SMulPosReflectLT α (∀ i, β i) where
  lt_of_smul_lt_smul_right := by
    simp_rw [lt_def]
    rintro b hb _a₁ _a₂ ⟨-, i, hi⟩
    exact lt_of_smul_lt_smul_right hi <| hb _

end SMulWithZero
end Pi

section Lift
variable {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
  [SMul α β] [SMul α γ] (f : β → γ)

section
variable [Zero α]

/-
**PosSMulMono.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulMono.lift [PosSMulMono α γ] (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁
 <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulMono α β where s
mul_le_smul_of_nonneg_left a ha b₁ b₂ hb
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
lemma PosSMulMono.lift [PosSMulMono α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b) : PosSMulMono α β where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hb := by
    simp only [← hf, smul] at *; exact smul_le_smul_of_nonneg_left hb ha
/-
**PosSMulStrictMono.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulStrictMono.lift [PosSMulStrictMono α γ] (hf : forall {b₁ b₂}, f b₁ 
<= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulStri
ctMono α β where smul_lt_smul_of_pos_left a ha b₁ b₂ hb
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
lemma PosSMulStrictMono.lift [PosSMulStrictMono α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b) : PosSMulStrictMono α β where
  smul_lt_smul_of_pos_left a ha b₁ b₂ hb := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact smul_lt_smul_of_pos_left hb ha
/-
**PosSMulReflectLE.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulReflectLE.lift [PosSMulReflectLE α γ] (hf : forall {b₁ b₂}, f b₁ <=
 f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulReflec
tLE α β where le_of_smul_le_smul_left a ha b₁ b₂ h
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma PosSMulReflectLE.lift [PosSMulReflectLE α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b) : PosSMulReflectLE α β where
  le_of_smul_le_smul_left a ha b₁ b₂ h :=
    hf.1 <| le_of_smul_le_smul_left (by simpa only [smul] using hf.2 h) ha
/-
**PosSMulReflectLT.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PosSMulReflectLT.lift [PosSMulReflectLT α γ] (hf : forall {b₁ b₂}, f b₁ <=
 f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulReflec
tLT α β where lt_of_smul_lt_smul_left a ha b₁ b₂ h
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma PosSMulReflectLT.lift [PosSMulReflectLT α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b) : PosSMulReflectLT α β where
  lt_of_smul_lt_smul_left a ha b₁ b₂ h := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact lt_of_smul_lt_smul_left h ha

end

section
variable [Zero β] [Zero γ]

/-
**SMulPosMono.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosMono.lift [SMulPosMono α γ] (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁
 <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) (zero : f 0 = 0) : SMulPo
sMono α β where smul_le_smul_of_nonneg_right b hb a₁ a₂ ha
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b；zero : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma SMulPosMono.lift [SMulPosMono α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosMono α β where
  smul_le_smul_of_nonneg_right b hb a₁ a₂ ha := by
    simp only [← hf, zero, smul] at *; exact smul_le_smul_of_nonneg_right ha hb
/-
**SMulPosStrictMono.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosStrictMono.lift [SMulPosStrictMono α γ] (hf : forall {b₁ b₂}, f b₁ 
<= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) (zero : f 0 =
 0) : SMulPosStrictMono α β where smul_lt_smul_of_pos_right b hb a₁ a₂ ha
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b；zero : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma SMulPosStrictMono.lift [SMulPosStrictMono α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right b hb a₁ a₂ ha := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact smul_lt_smul_of_pos_right ha hb
/-
**SMulPosReflectLE.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLE.lift [SMulPosReflectLE α γ] (hf : forall {b₁ b₂}, f b₁ <=
 f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) (zero : f 0 = 0
) : SMulPosReflectLE α β where le_of_smul_le_smul_right b hb a₁ a₂ h
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b；zero : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_right`：le_of_smul_le_smul_right [SMulPosReflectLE α β
] (h : a₁ • b <= a₂ • b) (hb : 0 < b) : a₁ <= a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma SMulPosReflectLE.lift [SMulPosReflectLE α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosReflectLE α β where
  le_of_smul_le_smul_right b hb a₁ a₂ h := by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact le_of_smul_le_smul_right h hb
/-
**SMulPosReflectLT.lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulPosReflectLT.lift [SMulPosReflectLT α γ] (hf : forall {b₁ b₂}, f b₁ <=
 f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) (zero : f 0 = 0
) : SMulPosReflectLT α β where lt_of_smul_lt_smul_right b hb a₁ a₂ h
参数：hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂；smul : forall (a : α) b, f (a • 
b) = a • f b；zero : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_smul_lt_smul_right`：lt_of_smul_lt_smul_right [SMulPosReflectLT α β
] (h : a₁ • b < a₂ • b) (hb : 0 <= b) : a₁ < a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma SMulPosReflectLT.lift [SMulPosReflectLT α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right b hb a₁ a₂ h := by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact lt_of_smul_lt_smul_right h hb

end

end Lift

section Nat

/-
**OrderedSemiring.toPosSMulMonoNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderedSemiring.toPosSMulMonoNat [Semiring α] [PartialOrder α] [IsOrderedR
ing α] : PosSMulMono Nat α where smul_le_smul_of_nonneg_left _n _ _a _b hab
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
instance OrderedSemiring.toPosSMulMonoNat [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    PosSMulMono ℕ α where
  smul_le_smul_of_nonneg_left _n _ _a _b hab := nsmul_le_nsmul_right hab _
/-
**OrderedSemiring.toSMulPosMonoNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderedSemiring.toSMulPosMonoNat [Semiring α] [PartialOrder α] [IsOrderedR
ing α] : SMulPosMono Nat α where smul_le_smul_of_nonneg_right _a ha _m _n hmn
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_le_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftMono M] {a : M} {n m : ℕ},   0 ≤ a → n ≤ m → n • a ≤ m • a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
instance OrderedSemiring.toSMulPosMonoNat [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    SMulPosMono ℕ α where
  smul_le_smul_of_nonneg_right _a ha _m _n hmn := nsmul_le_nsmul_left ha hmn
/-
**StrictOrderedSemiring.toPosSMulStrictMonoNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StrictOrderedSemiring.toPosSMulStrictMonoNat [Semiring α] [PartialOrder α]
 [IsStrictOrderedRing α] : PosSMulStrictMono Nat α where smul_lt_smul_of_pos_lef
t _n hn _a _b hab
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_right_strictMono`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : 
Preorder M] [AddLeftStrictMono M] [AddRightStrictMono M] {n : ℕ},   n ≠ 0 → Stri
ctMono fun x…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
instance StrictOrderedSemiring.toPosSMulStrictMonoNat
    [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    PosSMulStrictMono ℕ α where
  smul_lt_smul_of_pos_left _n hn _a _b hab := nsmul_right_strictMono hn.ne' hab
/-
**StrictOrderedSemiring.toSMulPosStrictMonoNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：StrictOrderedSemiring.toSMulPosStrictMonoNat [Semiring α] [PartialOrder α]
 [IsStrictOrderedRing α] : SMulPosStrictMono Nat α where smul_lt_smul_of_pos_rig
ht _a ha _m _n hmn
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_lt_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftStrictMono M] {a : M} {n m : ℕ},   0 < a → n < m → n • a < m • 
a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
instance StrictOrderedSemiring.toSMulPosStrictMonoNat
    [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    SMulPosStrictMono ℕ α where
  smul_lt_smul_of_pos_right _a ha _m _n hmn := nsmul_lt_nsmul_left ha hmn

end Nat

-- TODO: Instances for `Int` and `Rat`

