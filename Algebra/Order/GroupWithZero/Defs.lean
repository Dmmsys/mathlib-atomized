/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Util.Notation3

/-!
# (Strict) monotonicity of multiplication by nonnegative (positive) elements

This file defines eight typeclasses expressing monotonicity (strict monotonicity)
of multiplication on the left or right by nonnegative (positive) elements in a preorder.

For left multiplication (`a ↦ b * a`) we define the following typeclasses:
* `PosMulMono`: If `b ≥ 0`, then `a₁ ≤ a₂ → b * a₁ ≤ b * a₂`.
* `PosMulStrictMono`: If `b > 0`, then `a₁ < a₂ → b * a₁ < b * a₂`.
* `PosMulReflectLT`: If `b ≥ 0`, then `b * a₁ < b * a₂ → a₁ < a₂`.
* `PosMulReflectLE`: If `b > 0`, then `b * a₁ ≤ b * a₂ → a₁ ≤ a₂`.

For right multiplication (`a ↦ a * b`) we define the following typeclasses:
* `MulPosMono`: If `b ≥ 0`, then `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b`.
* `MulPosStrictMono`: If `b > 0`, then `a₁ < a₂ → a₁ * b < a₂ * b`.
* `MulPosReflectLT`: If `b ≥ 0`, then `a₁ * b < a₂ * b → a₁ < a₂`.
* `MulPosReflectLE`: If `b > 0`, then `a₁ * b ≤ a₂ * b → a₁ ≤ a₂`.

We then provide statements and instances about these typeclasses not requiring `MulZeroClass`
or higher on the underlying type – those that do can be found in
`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`.

Less granular typeclasses like `IsOrderedAddMonoid` and `IsOrderedRing` should be enough for
most purposes, and the system is set up so that they imply the correct granular typeclasses here.

## Implications

As the underlying type `α` gets more structured, some of the above typeclasses become equivalent.
The commonly used implications are:
* When `α` is a partial order (in `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`):
  * `PosMulStrictMono.toPosMulMono`
  * `MulPosStrictMono.toMulPosMono`
  * `PosMulReflectLE.toPosMulReflectLT`
  * `MulPosReflectLE.toMulPosReflectLT`
* When `α` is a linear order:
  * `PosMulStrictMono.toPosMulReflectLE`
  * `MulPosStrictMono.toMulPosReflectLE`
* When multiplication on `α` is commutative:
  * `posMulMono_iff_mulPosMono`
  * `posMulStrictMono_iff_mulPosStrictMono`
  * `posMulReflectLE_iff_mulPosReflectLE`
  * `posMulReflectLT_iff_mulPosReflectLT`

Furthermore, the bundled non-granular typeclasses imply the granular ones like so:
* `IsOrderedRing → PosMulMono`
* `IsOrderedRing → MulPosMono`
* `IsStrictOrderedRing → PosMulStrictMono`
* `IsStrictOrderedRing → MulPosStrictMono`

All these are registered as instances, which means that in practice you should not worry about these
implications. However, if you encounter a case where you think a statement is true but not covered
by the current implications, please bring it up on Zulip!

## Notation

The following is local notation in this file:
* `α≥0`: `{x : α // 0 ≤ x}`
* `α>0`: `{x : α // 0 < x}`

See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
for a discussion about this notation, and whether to enable it globally (note that the notation is
currently global but broken, hence actually only works locally).
-/

public section

assert_not_exists MulZeroClass

open Function

variable (α : Type*)

/-- Local notation for the nonnegative elements of a type `α`. -/
local notation3 "α≥0" => { x : α // 0 ≤ x }

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the left,
namely `a₁ ≤ a₂ → b * a₁ ≤ b * a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedRing`. -/
/-
**PosMulMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of multiplication by nonnegative elements on the left
,
namely `a₁ ≤ a₂ → b * a₁ ≤ b * a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedRing`.
-/
@[mk_iff] class PosMulMono : Prop where
  /-- Do not use this. Use `_root_.mul_le_mul_of_nonneg_left` instead. -/
  protected mul_le_mul_of_nonneg_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b c : α⦄ (hbc : b ≤ c) : a * b ≤ a * c

/-- Typeclass for strict monotonicity of multiplication by positive elements on the left,
namely `a₁ < a₂ → b * a₁ < b * a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsStrictOrderedRing`. -/
/-
**PosMulStrictMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict monotonicity of multiplication by positive elements on the 
left,
namely `a₁ < a₂ → b * a₁ < b * a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsStrictOrderedRing`.
-/
@[mk_iff] class PosMulStrictMono : Prop where
  /-- Do not use this. Use `_root_.mul_lt_mul_of_pos_left` instead. -/
  protected mul_lt_mul_of_pos_left ⦃a : α⦄ (ha : 0 < a) ⦃b c : α⦄ (hbc : b < c) : a * b < a * c

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the left, namely `b * a₁ < b * a₂ → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsStrictOrderedRing`. -/
/-
**PosMulReflectLT** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of multiplication by nonnegative eleme
nts on
the left, namely `b * a₁ < b * a₂ → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsStrictOrderedRing`.
-/
@[mk_iff] class PosMulReflectLT : Prop extends ContravariantClass α≥0 α (fun x y => x * y) (· < ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the left,
namely `b * a₁ ≤ b * a₂ → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsStrictOrderedRing`. -/
/-
**PosMulReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of multiplication by positive elements on the
 left,
namely `b * a₁ ≤ b * a₂ → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsStrictOrderedRing`.
-/
@[mk_iff] class PosMulReflectLE : Prop extends ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)

/-- Typeclass for monotonicity of multiplication by nonnegative elements on the right,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedRing`. -/
/-
**MulPosMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monotonicity of multiplication by nonnegative elements on the righ
t,
namely `a₁ ≤ a₂ → a₁ * b ≤ a₂ * b` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsOrderedRing`.
-/
@[mk_iff] class MulPosMono : Prop where
  /-- Do not use this. Use `_root_.mul_le_mul_of_nonneg_right` instead. -/
  protected mul_le_mul_of_nonneg_right ⦃c : α⦄ (hc : 0 ≤ c) ⦃a b : α⦄ (hab : a ≤ b) : a * c ≤ b * c

/-- Typeclass for strict monotonicity of multiplication by positive elements on the right,
namely `a₁ < a₂ → a₁ * b < a₂ * b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsStrictOrderedRing`. -/
/-
**MulPosStrictMono** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict monotonicity of multiplication by positive elements on the 
right,
namely `a₁ < a₂ → a₁ * b < a₂ * b` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsStrictOrderedRing`.
-/
@[mk_iff] class MulPosStrictMono : Prop where
  /-- Do not use this. Use `_root_.mul_lt_mul_of_pos_right` instead. -/
  protected mul_lt_mul_of_pos_right ⦃c : α⦄ (hc : 0 < c) ⦃a b : α⦄ (hab : a < b) : a * c < b * c

/-- Typeclass for strict reverse monotonicity of multiplication by nonnegative elements on
the right, namely `a₁ * b < a₂ * b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsStrictOrderedRing`. -/
/-
**MulPosReflectLT** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for strict reverse monotonicity of multiplication by nonnegative eleme
nts on
the right, namely `a₁ * b < a₂ * b → a₁ < a₂` if `0 ≤ b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsStrictOrderedRing`.
-/
@[mk_iff] class MulPosReflectLT : Prop extends ContravariantClass α≥0 α (fun x y => y * x) (· < ·)

/-- Typeclass for reverse monotonicity of multiplication by positive elements on the right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsStrictOrderedRing`. -/
/-
**MulPosReflectLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [Zero α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for reverse monotonicity of multiplication by positive elements on the
 right,
namely `a₁ * b ≤ a₂ * b → a₁ ≤ a₂` if `0 < b`.

You should usually not use this very granular typeclass directly, but rather a t
ypeclass like
`IsStrictOrderedRing`.
-/
@[mk_iff] class MulPosReflectLE : Prop extends ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)

end Abbreviations

variable {α}
variable [Mul α] [Zero α]

section Preorder

variable [Preorder α] {a b c d : α}

/-
**PosMulMono.to_covariantClass_nonneg_mul_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosMulMono.to_covariantClass_nonneg_mul_le [PosMulMono α] : CovariantClass
 α>=0 α (fun x y => x * y) (· <= ·) where elim a _b _c hbc
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.mul_le_mul_of_nonneg_left`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulMono α] ⦃a : α⦄,   0 ≤ a → ∀
 ⦃b c : α⦄, b ≤ c → a * b …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance PosMulMono.to_covariantClass_nonneg_mul_le [PosMulMono α] :
    CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·) where
  elim a _b _c hbc := PosMulMono.mul_le_mul_of_nonneg_left a.2 hbc
/-
**MulPosMono.to_covariantClass_nonneg_mul_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulPosMono.to_covariantClass_nonneg_mul_le [MulPosMono α] : CovariantClass
 α>=0 α (fun x y => y * x) (· <= ·) where elim a _b _c hbc
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosMono.mul_le_mul_of_nonneg_right`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosMono α] ⦃c : α⦄,   0 ≤ c → 
∀ ⦃a b : α⦄, a ≤ b → a * c …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance MulPosMono.to_covariantClass_nonneg_mul_le [MulPosMono α] :
    CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·) where
  elim a _b _c hbc := MulPosMono.mul_le_mul_of_nonneg_right a.2 hbc
/-
**PosMulMono.to_covariantClass_pos_mul_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] : CovariantClass α>
0 α (fun x y => x * y) (· <= ·) where elim a _b _c hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.mul_le_mul_of_nonneg_left`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulMono α] ⦃a : α⦄,   0 ≤ a → ∀
 ⦃b c : α⦄, b ≤ c → a * b …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) where
  elim a _b _c hbc := PosMulMono.mul_le_mul_of_nonneg_left a.2.le hbc
/-
**MulPosMono.to_covariantClass_pos_mul_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] : CovariantClass α>
0 α (fun x y => y * x) (· <= ·) where elim a _b _c hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosMono.mul_le_mul_of_nonneg_right`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosMono α] ⦃c : α⦄,   0 ≤ c → 
∀ ⦃a b : α⦄, a ≤ b → a * c …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) where
  elim a _b _c hbc := MulPosMono.mul_le_mul_of_nonneg_right a.2.le hbc
/-
**PosMulStrictMono.to_covariantClass_pos_mul_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosMulStrictMono.to_covariantClass_pos_mul_le [PosMulStrictMono α] : Covar
iantClass α>0 α (fun x y => x * y) (· < ·) where elim a _b _c hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulStrictMono.mul_lt_mul_of_pos_left`：∀ {α : Type u_1} {inst : Mul α}
 {inst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulStrictMono α] ⦃a : α⦄,   
0 < a → ∀ ⦃b c : α⦄, b < c → …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance PosMulStrictMono.to_covariantClass_pos_mul_le [PosMulStrictMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· < ·) where
  elim a _b _c hbc := PosMulStrictMono.mul_lt_mul_of_pos_left a.2 hbc
/-
**MulPosStrictMono.to_covariantClass_pos_mul_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulPosStrictMono.to_covariantClass_pos_mul_le [MulPosStrictMono α] : Covar
iantClass α>0 α (fun x y => y * x) (· < ·) where elim a _b _c hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosStrictMono.mul_lt_mul_of_pos_right`：∀ {α : Type u_1} {inst : Mul α
} {inst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosStrictMono α] ⦃c : α⦄,  
 0 < c → ∀ ⦃a b : α⦄, a < b → …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance MulPosStrictMono.to_covariantClass_pos_mul_le [MulPosStrictMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· < ·) where
  elim a _b _c hbc := MulPosStrictMono.mul_lt_mul_of_pos_right a.2 hbc
/-
**PosMulReflectLT.to_contravariantClass_pos_mul_lt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] : Con
travariantClass α>0 α (fun x y => x * y) (· < ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `PosMulReflectLT.toContravariantClass`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulReflectLT α],   Contravarian
tClass { x // 0 ≤ x } α (f…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
/-
**MulPosReflectLT.to_contravariantClass_pos_mul_lt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] : Con
travariantClass α>0 α (fun x y => y * x) (· < ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `MulPosReflectLT.toContravariantClass`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosReflectLT α],   Contravarian
tClass { x // 0 ≤ x } α (f…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulLeftMono.toPosMulMono [MulLeftMono α] :
    PosMulMono α where mul_le_mul_of_nonneg_left _ _ _ _ := ‹MulLeftMono α›.elim _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulRightMono.toMulPosMono [MulRightMono α] :
    MulPosMono α where mul_le_mul_of_nonneg_right _ _ _ _ := ‹MulRightMono α›.elim _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulLeftStrictMono.toPosMulStrictMono [MulLeftStrictMono α] :
    PosMulStrictMono α where mul_lt_mul_of_pos_left _ _ _ _ := ‹MulLeftStrictMono α›.elim _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulRightStrictMono.toMulPosStrictMono [MulRightStrictMono α] :
    MulPosStrictMono α where mul_lt_mul_of_pos_right _ _ _ _ := ‹MulRightStrictMono α›.elim _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulLeftMono.toPosMulReflectLT [MulLeftReflectLT α] :
    PosMulReflectLT α where elim _ _ := ‹MulLeftReflectLT α›.elim _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulRightMono.toMulPosReflectLT [MulRightReflectLT α] :
    MulPosReflectLT α where elim _ _ := ‹MulRightReflectLT α›.elim _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulLeftStrictMono.toPosMulReflectLE [MulLeftReflectLE α] :
    PosMulReflectLE α where
  elim _ _ _ := ‹MulLeftReflectLE α›.le_of_mul_le_mul_left'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulRightStrictMono.toMulPosReflectLE [MulRightReflectLE α] :
    MulPosReflectLE α where
  elim _ _ _ := ‹MulRightReflectLE α›.le_of_mul_le_mul_right'

@[gcongr]
/-
**mul_le_mul_of_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b <= c) (ha : 0 <= a) : a 
* b <= a * c
参数：hbc : b <= c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.mul_le_mul_of_nonneg_left`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulMono α] ⦃a : α⦄,   0 ≤ a → ∀
 ⦃b c : α⦄, b ≤ c → a * b …
-/
theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
  PosMulMono.mul_le_mul_of_nonneg_left ha hbc

@[gcongr]
/-
**mul_le_mul_of_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b <= c) (ha : 0 <= a) : b
 * a <= c * a
参数：hbc : b <= c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosMono.mul_le_mul_of_nonneg_right`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosMono α] ⦃c : α⦄,   0 ≤ c → 
∀ ⦃a b : α⦄, a ≤ b → a * c …
-/
theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a :=
  MulPosMono.mul_le_mul_of_nonneg_right ha hbc

@[gcongr]
/-
**mul_lt_mul_of_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc : b < c) (ha : 0 < a) : a
 * b < a * c
参数：hbc : b < c；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulStrictMono.mul_lt_mul_of_pos_left`：∀ {α : Type u_1} {inst : Mul α}
 {inst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulStrictMono α] ⦃a : α⦄,   
0 < a → ∀ ⦃b c : α⦄, b < c → …
-/
theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc : b < c) (ha : 0 < a) : a * b < a * c :=
  PosMulStrictMono.mul_lt_mul_of_pos_left ha hbc

@[gcongr]
/-
**mul_lt_mul_of_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_pos_right [MulPosStrictMono α] (hbc : b < c) (ha : 0 < a) : 
b * a < c * a
参数：hbc : b < c；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosStrictMono.mul_lt_mul_of_pos_right`：∀ {α : Type u_1} {inst : Mul α
} {inst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosStrictMono α] ⦃c : α⦄,  
 0 < c → ∀ ⦃a b : α⦄, a < b → …
-/
theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (hbc : b < c) (ha : 0 < a) : b * a < c * a :=
  MulPosStrictMono.mul_lt_mul_of_pos_right ha hbc
/-
**lt_of_mul_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 <= a
) : b < c
参数：h : a * b < a * c；a0 : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `PosMulReflectLT.toContravariantClass`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulReflectLT α],   Contravarian
tClass { x // 0 ≤ x } α (f…
-/
theorem lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h
/-
**lt_of_mul_lt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 <= 
a) : b < c
参数：h : b * a < c * a；a0 : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `MulPosReflectLT.toContravariantClass`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosReflectLT α],   Contravarian
tClass { x // 0 ≤ x } α (f…
-/
theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h
/-
**le_of_mul_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b <= a * c) (a0 : 0 < 
a) : b <= c
参数：bc : a * b <= a * c；a0 : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `PosMulReflectLE.toContravariantClass`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : PosMulReflectLE α],   Contravarian
tClass { x // 0 < x } α (f…
-/
theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
/-
**le_of_mul_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a <= c * a) (a0 : 0 <
 a) : b <= c
参数：bc : b * a <= c * a；a0 : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
· 使用定理 `MulPosReflectLE.toContravariantClass`：∀ {α : Type u_1} {inst : Mul α} {i
nst_1 : Zero α} {inst_2 : Preorder α} [self : MulPosReflectLE α],   Contravarian
tClass { x // 0 < x } α (f…
-/
theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right
/-- Pullback `PosMulMono`. -/
/-
**Function.Injective.posMulMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.posMulMono [PosMulMono α] {β : Type*} [Zero β] [Mul β] 
[Preorder β] (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * 
f y) (le : forall {x y}, f x <= f y ↔ x <= y) : PosMulMono β where mul_le_mul_of
_nonneg_left a ha b c hbc
参数：f : β -> α；zero : f 0 = 0；mul : forall x y, f (x * y) = f x * f y；le : forall
 {x y}, f x <= f y ↔ x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Pullback `PosMulMono`.
-/
lemma Function.Injective.posMulMono [PosMulMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
    (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) : PosMulMono β where
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le, mul, mul]; exact mul_le_mul_of_nonneg_left (le.2 hbc) (by rwa [← zero, le])

/-- Pullback `MulPosMono`. -/
/-
**Function.Injective.mulPosMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.mulPosMono [MulPosMono α] {β : Type*} [Zero β] [Mul β] 
[Preorder β] (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * 
f y) (le : forall {x y}, f x <= f y ↔ x <= y) : MulPosMono β where mul_le_mul_of
_nonneg_right a ha b c hbc
参数：f : β -> α；zero : f 0 = 0；mul : forall x y, f (x * y) = f x * f y；le : forall
 {x y}, f x <= f y ↔ x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Pullback `MulPosMono`.
-/
lemma Function.Injective.mulPosMono [MulPosMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
    (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) : MulPosMono β where
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le, mul, mul]; exact mul_le_mul_of_nonneg_right (le.2 hbc) (by rwa [← zero, le])

/-- Pullback `PosMulStrictMono`. -/
/-
**Function.Injective.posMulStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.posMulStrictMono [PosMulStrictMono α] {β : Type*} [Zero
 β] [Mul β] [Preorder β] (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x *
 y) = f x * f y) (lt : forall {x y}, f x < f y ↔ x < y) : PosMulStrictMono β whe
re mul_lt_mul_of_pos_left a ha b c hbc
参数：f : β -> α；zero : f 0 = 0；mul : forall x y, f (x * y) = f x * f y；lt : forall
 {x y}, f x < f y ↔ x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Pullback `PosMulStrictMono`.
-/
lemma Function.Injective.posMulStrictMono [PosMulStrictMono α] {β : Type*} [Zero β] [Mul β]
    [Preorder β] (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (lt : ∀ {x y}, f x < f y ↔ x < y) : PosMulStrictMono β where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt, mul, mul]; exact mul_lt_mul_of_pos_left (lt.2 hbc) (by rwa [← zero, lt])

/-- Pullback `MulPosStrictMono`. -/
/-
**Function.Injective.mulPosStrictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.mulPosStrictMono [MulPosStrictMono α] {β : Type*} [Zero
 β] [Mul β] [Preorder β] (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x *
 y) = f x * f y) (lt : forall {x y}, f x < f y ↔ x < y) : MulPosStrictMono β whe
re mul_lt_mul_of_pos_right a ha b c hbc
参数：f : β -> α；zero : f 0 = 0；mul : forall x y, f (x * y) = f x * f y；lt : forall
 {x y}, f x < f y ↔ x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Pullback `MulPosStrictMono`.
-/
lemma Function.Injective.mulPosStrictMono [MulPosStrictMono α] {β : Type*} [Zero β] [Mul β]
    [Preorder β] (f : β → α) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
    (lt : ∀ {x y}, f x < f y ↔ x < y) : MulPosStrictMono β where
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt, mul, mul]; exact mul_lt_mul_of_pos_right (lt.2 hbc) (by rwa [← zero, lt])

@[simp]
/-
**mul_lt_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRightReflectLT α] (a : α) 
{b c : α} : b * a < c * a ↔ b < c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov`：rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M 
N μ r] (m : M) {a b : N} : r (μ m a) (μ m b) ↔ r a b
-/
theorem mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c where
  mp h := lt_of_mul_lt_mul_left h a0.le
  mpr h := mul_lt_mul_of_pos_left h a0

@[simp]
/-
**mul_lt_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftReflectLT α] (a : α) {b 
c : α} : a * b < a * c ↔ b < c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov`：rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M 
N μ r] (m : M) {a b : N} : r (μ m a) (μ m b) ↔ r a b
-/
theorem mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c where
  mp h := lt_of_mul_lt_mul_right h a0.le
  mpr h := mul_lt_mul_of_pos_right h a0

@[simp]
/-
**mul_le_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_iff_right [MulRightMono α] [MulRightReflectLE α] (a : α) {b c :
 α} : b * a <= c * a ↔ b <= c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov'`：rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contrav
ariant M N μ r) {m : M} {a b : N} : r (μ m a) (μ m b) ↔ r a b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `MulRightReflectLE.le_of_mul_le_mul_right'`：∀ {M : Type u_1} {inst : Mul 
M} {inst_1 : LE M} [self : MulRightReflectLE M] {b a₁ a₂ : M}, a₁ * b ≤ a₂ * b →
 a₁ ≤ a₂
-/
theorem mul_le_mul_iff_right₀ [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) :
    a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

@[simp]
/-
**mul_le_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b c : α}
 : a * b <= a * c ↔ b <= c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov'`：rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contrav
ariant M N μ r) {m : M} {a b : N} : r (μ m a) (μ m b) ↔ r a b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `MulLeftReflectLE.le_of_mul_le_mul_left'`：∀ {M : Type u_1} {inst : Mul M}
 {inst_1 : LE M} [self : MulLeftReflectLE M] {a b₁ b₂ : M}, a * b₁ ≤ a * b₂ → b₁
 ≤ b₂
-/
theorem mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) :
    b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_iff_right₀
alias mul_le_mul_iff_of_pos_right := mul_le_mul_iff_left₀
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_iff_right₀
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_iff_left₀
/-
**mul_le_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonneg [PosMulMono α] [MulPosMono α] (h₁ : a <= b) (h₂ : c <
= d) (a0 : 0 <= a) (d0 : 0 <= d) : a * c <= b * d
参数：h₁ : a <= b；h₂ : c <= d；a0 : 0 <= a；d0 : 0 <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem mul_le_mul_of_nonneg [PosMulMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)
/-
**mul_le_mul_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonneg' [PosMulMono α] [MulPosMono α] (h₁ : a <= b) (h₂ : c 
<= d) (c0 : 0 <= c) (b0 : 0 <= b) : a * c <= b * d
参数：h₁ : a <= b；h₂ : c <= d；c0 : 0 <= c；b0 : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_le_mul_of_nonneg' [PosMulMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)
/-
**mul_lt_mul_of_le_of_lt_of_pos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_le_of_lt_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α
] (h₁ : a <= b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 <= d) : a * c < b * d
参数：h₁ : a <= b；h₂ : c < d；a0 : 0 < a；d0 : 0 <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem mul_lt_mul_of_le_of_lt_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

alias mul_lt_mul_of_pos_of_nonneg := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg
/-
**mul_lt_mul_of_le_of_lt_of_nonneg_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_le_of_lt_of_nonneg_of_pos [PosMulStrictMono α] [MulPosMono α
] (h₁ : a <= b) (h₂ : c < d) (c0 : 0 <= c) (b0 : 0 < b) : a * c < b * d
参数：h₁ : a <= b；h₂ : c < d；c0 : 0 <= c；b0 : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem mul_lt_mul_of_le_of_lt_of_nonneg_of_pos [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c < d) (c0 : 0 ≤ c) (b0 : 0 < b) : a * c < b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

alias mul_lt_mul_of_nonneg_of_pos' := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
/-
**mul_lt_mul_of_lt_of_le_of_nonneg_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_lt_of_le_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α
] (h₁ : a < b) (h₂ : c <= d) (a0 : 0 <= a) (d0 : 0 < d) : a * c < b * d
参数：h₁ : a < b；h₂ : c <= d；a0 : 0 <= a；d0 : 0 < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem mul_lt_mul_of_lt_of_le_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

alias mul_lt_mul_of_nonneg_of_pos := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
/-
**mul_lt_mul_of_lt_of_le_of_pos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_lt_of_le_of_pos_of_nonneg [PosMulMono α] [MulPosStrictMono α
] (h₁ : a < b) (h₂ : c <= d) (c0 : 0 < c) (b0 : 0 <= b) : a * c < b * d
参数：h₁ : a < b；h₂ : c <= d；c0 : 0 < c；b0 : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_lt_mul_of_lt_of_le_of_pos_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c ≤ d) (c0 : 0 < c) (b0 : 0 ≤ b) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

alias mul_lt_mul_of_pos_of_nonneg' := mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
/-
**mul_lt_mul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (
h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d；a0 : 0 < a；d0 : 0 < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem mul_lt_mul_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)
/-
**mul_lt_mul_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_pos' [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) 
(h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d；c0 : 0 < c；b0 : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem mul_lt_mul_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

alias mul_le_mul := mul_le_mul_of_nonneg'
attribute [gcongr] mul_le_mul

alias mul_lt_mul := mul_lt_mul_of_pos_of_nonneg'

alias mul_lt_mul' := mul_lt_mul_of_nonneg_of_pos'
/-
**mul_le_of_mul_le_of_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b <= c) (hle : d <
= b) (a0 : 0 <= a) : a * d <= c
参数：h : a * b <= c；hle : d <= b；a0 : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d ≤ c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h
/-
**mul_lt_of_mul_lt_of_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : d <=
 b) (a0 : 0 <= a) : a * d < c
参数：h : a * b < c；hle : d <= b；a0 : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d < c :=
  (mul_le_mul_of_nonneg_left hle a0).trans_lt h
/-
**le_mul_of_le_mul_of_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a <= b * c) (hle : c <
= d) (b0 : 0 <= b) : a <= b * d
参数：h : a <= b * c；hle : c <= d；b0 : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a ≤ b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)
/-
**lt_mul_of_lt_mul_of_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hle : c <=
 d) (b0 : 0 <= b) : a < b * d
参数：h : a < b * c；hle : c <= d；b0 : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a < b * d :=
  h.trans_le (mul_le_mul_of_nonneg_left hle b0)
/-
**mul_le_of_mul_le_of_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b <= c) (hle : d 
<= a) (b0 : 0 <= b) : d * b <= c
参数：h : a * b <= c；hle : d <= a；b0 : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b ≤ c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h
/-
**mul_lt_of_mul_lt_of_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hle : d <
= a) (b0 : 0 <= b) : d * b < c
参数：h : a * b < c；hle : d <= a；b0 : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b < c :=
  (mul_le_mul_of_nonneg_right hle b0).trans_lt h
/-
**le_mul_of_le_mul_of_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a <= b * c) (hle : b 
<= d) (c0 : 0 <= c) : a <= d * c
参数：h : a <= b * c；hle : b <= d；c0 : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a ≤ d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)
/-
**lt_mul_of_lt_mul_of_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hle : b <
= d) (c0 : 0 <= c) : a < d * c
参数：h : a < b * c；hle : b <= d；c0 : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a < d * c :=
  h.trans_le (mul_le_mul_of_nonneg_right hle c0)

variable [IsMulCommutative α]
/-
**posMulMono_iff_mulPosMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp [posMulMono_iff, mulPosMono_iff, mul_comm']
/-
**PosMulMono.toMulPosMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulMono.toMulPosMono [PosMulMono α] : MulPosMono α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulMono_iff_mulPosMono`：posMulMono_iff_mulPosMono : PosMulMono α ↔ Mu
lPosMono α
-/
theorem PosMulMono.toMulPosMono [PosMulMono α] : MulPosMono α := posMulMono_iff_mulPosMono.mp ‹_›
/-
**posMulStrictMono_iff_mulPosStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictM
ono α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp [posMulStrictMono_iff, mulPosStrictMono_iff, mul_comm']
/-
**PosMulStrictMono.toMulPosStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulStrictMono.toMulPosStrictMono [PosMulStrictMono α] : MulPosStrictMon
o α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulStrictMono_iff_mulPosStrictMono`：posMulStrictMono_iff_mulPosStrict
Mono : PosMulStrictMono α ↔ MulPosStrictMono α
-/
theorem PosMulStrictMono.toMulPosStrictMono [PosMulStrictMono α] : MulPosStrictMono α :=
  posMulStrictMono_iff_mulPosStrictMono.mp ‹_›
/-
**posMulReflectLE_iff_mulPosReflectLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE 
α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp [posMulReflectLE_iff, mulPosReflectLE_iff, mul_comm']
/-
**PosMulReflectLE.toMulPosReflectLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulReflectLE.toMulPosReflectLE [PosMulReflectLE α] : MulPosReflectLE α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulReflectLE_iff_mulPosReflectLE`：posMulReflectLE_iff_mulPosReflectLE
 : PosMulReflectLE α ↔ MulPosReflectLE α
-/
theorem PosMulReflectLE.toMulPosReflectLE [PosMulReflectLE α] : MulPosReflectLE α :=
  posMulReflectLE_iff_mulPosReflectLE.mp ‹_›
/-
**posMulReflectLT_iff_mulPosReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT 
α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp [posMulReflectLT_iff, mulPosReflectLT_iff, mul_comm']
/-
**PosMulReflectLT.toMulPosReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulReflectLT.toMulPosReflectLT [PosMulReflectLT α] : MulPosReflectLT α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulReflectLT_iff_mulPosReflectLT`：posMulReflectLT_iff_mulPosReflectLT
 : PosMulReflectLT α ↔ MulPosReflectLT α
-/
theorem PosMulReflectLT.toMulPosReflectLT [PosMulReflectLT α] : MulPosReflectLT α :=
  posMulReflectLT_iff_mulPosReflectLT.mp ‹_›

end Preorder

section LinearOrder

variable [LinearOrder α]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulStrictMono.toPosMulReflectLE [PosMulStrictMono α] :
    PosMulReflectLE α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosStrictMono.toMulPosReflectLE [MulPosStrictMono α] :
    MulPosReflectLE α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim
/-
**PosMulReflectLE.toPosMulStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono 
α where mul_lt_mul_of_pos_left _a ha _b _c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_of_mul_le_mul_left`：le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a
 * b <= a * c) (a0 : 0 < a) : b <= c
-/
theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    not_le.1 fun h ↦ hbc.not_ge <| le_of_mul_le_mul_left h ha
/-
**MulPosReflectLE.toMulPosStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono 
α where mul_lt_mul_of_pos_right _a ha _b _c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
-/
theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
    not_le.1 fun h ↦ hbc.not_ge <| le_of_mul_le_mul_right h ha
/-
**posMulStrictMono_iff_posMulReflectLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectL
E α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `PosMulReflectLE.toPosMulStrictMono`：PosMulReflectLE.toPosMulStrictMono [
PosMulReflectLE α] : PosMulStrictMono α where mul_lt_mul_of_pos_left _a ha _b _c
 hbc
-/
theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α :=
  ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩
/-
**mulPosStrictMono_iff_mulPosReflectLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectL
E α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `MulPosReflectLE.toMulPosStrictMono`：MulPosReflectLE.toMulPosStrictMono [
MulPosReflectLE α] : MulPosStrictMono α where mul_lt_mul_of_pos_right _a ha _b _
c hbc
-/
theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α :=
  ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩
/-
**PosMulReflectLT.toPosMulMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α where mul_
le_mul_of_nonneg_left _a ha _b _c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
-/
theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α where
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    not_lt.1 fun h ↦ hbc.not_gt <| lt_of_mul_lt_mul_left h ha
/-
**MulPosReflectLT.toMulPosMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α where mul_
le_mul_of_nonneg_right _a ha _b _c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `lt_of_mul_lt_mul_right`：lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : 
b * a < c * a) (a0 : 0 <= a) : b < c
-/
theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α where
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    not_lt.1 fun h ↦ hbc.not_gt <| lt_of_mul_lt_mul_right h ha
/-
**PosMulMono.toPosMulReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α where elim
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `covariant_le_iff_contravariant_lt`：covariant_le_iff_contravariant_lt [Li
nearOrder N] : Covariant M N μ (· <= ·) ↔ Contravariant M N μ (· < ·)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc ↦ mul_le_mul_of_nonneg_left hbc a.2
/-
**MulPosMono.toMulPosReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α where elim
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `covariant_le_iff_contravariant_lt`：covariant_le_iff_contravariant_lt [Li
nearOrder N] : Covariant M N μ (· <= ·) ↔ Contravariant M N μ (· < ·)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc ↦ mul_le_mul_of_nonneg_right hbc a.2

/-! TODO: Currently, only one in four of the above are made instances; we could consider making
  both directions of `covariant_le_iff_contravariant_lt` and `covariant_lt_iff_contravariant_le`
  instances, then all of the above become redundant instances, but there are performance issues. -/

/-
**posMulMono_iff_posMulReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.toPosMulReflectLT`：PosMulMono.toPosMulReflectLT [PosMulMono α
] : PosMulReflectLT α where elim
· 使用定理 `PosMulReflectLT.toPosMulMono`：PosMulReflectLT.toPosMulMono [PosMulReflec
tLT α] : PosMulMono α where mul_le_mul_of_nonneg_left _a ha _b _c hbc

--- 原说明 ---
TODO: Currently, only one in four of the above are made instances; we could cons
ider making
  both directions of `covariant_le_iff_contravariant_lt` and `covariant_lt_iff_c
ontravariant_le`
  instances, then all of the above become redundant instances, but there are per
formance issues.
-/
theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩
/-
**mulPosMono_iff_mulPosReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosMono.toMulPosReflectLT`：MulPosMono.toMulPosReflectLT [MulPosMono α
] : MulPosReflectLT α where elim
· 使用定理 `MulPosReflectLT.toMulPosMono`：MulPosReflectLT.toMulPosMono [MulPosReflec
tLT α] : MulPosMono α where mul_le_mul_of_nonneg_right _a ha _b _c hbc
-/
theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

end LinearOrder

