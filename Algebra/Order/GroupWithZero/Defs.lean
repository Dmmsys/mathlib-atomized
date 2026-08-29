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
local notation3 "α>=0" => { x : α // 0 <= x }

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

/--
Definition of `PosMulMono` / `PosMulMono` 的定义

English:
class PosMulMono
  parameters: : Prop where
  axioms and operations (1):
    - mul_le_mul_of_nonneg_left(⦃a) : α⦄ (ha : 0 <= a) ⦃b c : α⦄ (hbc : b <= c) : a * b <= a * c

中文:
类 PosMulMono
  参数: : 命题 where
  公理与运算 (1 个):
    - mul_le_mul_of_nonneg_left(⦃a) : α⦄ (ha : 0 <= a) ⦃b c : α⦄ (hbc : b <= c) : a * b <= a * c
-/
@[mk_iff] class PosMulMono : Prop where
  /-- Do not use this. Use `_root_.mul_le_mul_of_nonneg_left` instead. -/
  protected mul_le_mul_of_nonneg_left ⦃a : α⦄ (ha : 0 <= a) ⦃b c : α⦄ (hbc : b <= c) : a * b <= a * c

/--
Definition of `PosMulStrictMono` / `PosMulStrictMono` 的定义

English:
class PosMulStrictMono
  parameters: : Prop where
  axioms and operations (1):
    - mul_lt_mul_of_pos_left(⦃a) : α⦄ (ha : 0 < a) ⦃b c : α⦄ (hbc : b < c) : a * b < a * c

中文:
类 PosMulStrictMono
  参数: : 命题 where
  公理与运算 (1 个):
    - mul_lt_mul_of_pos_left(⦃a) : α⦄ (ha : 0 < a) ⦃b c : α⦄ (hbc : b < c) : a * b < a * c
-/
@[mk_iff] class PosMulStrictMono : Prop where
  /-- Do not use this. Use `_root_.mul_lt_mul_of_pos_left` instead. -/
  protected mul_lt_mul_of_pos_left ⦃a : α⦄ (ha : 0 < a) ⦃b c : α⦄ (hbc : b < c) : a * b < a * c

/--
Definition of `PosMulReflectLT` / `PosMulReflectLT` 的定义

English:
class PosMulReflectLT
  parameters: : Prop extends ContravariantClass α>=0 α (fun x y => x * y) (· < ·)
  extends: ContravariantClass α>=0 α (fun x y => x * y) (· < ·)
  (no additional axioms)

中文:
类 PosMulReflectLT
  参数: : 命题 extends ContravariantClass α>=0 α (fun x y => x * y) (· < ·)
  继承: ContravariantClass α>=0 α (fun x y => x * y) (· < ·)
  (无附加公理)
-/
@[mk_iff] class PosMulReflectLT : Prop extends ContravariantClass α>=0 α (fun x y => x * y) (· < ·)

/--
Definition of `PosMulReflectLE` / `PosMulReflectLE` 的定义

English:
class PosMulReflectLE
  parameters: : Prop extends ContravariantClass α>0 α (fun x y => x * y) (· <= ·)
  extends: ContravariantClass α>0 α (fun x y => x * y) (· <= ·)
  (no additional axioms)

中文:
类 PosMulReflectLE
  参数: : 命题 extends ContravariantClass α>0 α (fun x y => x * y) (· <= ·)
  继承: ContravariantClass α>0 α (fun x y => x * y) (· <= ·)
  (无附加公理)
-/
@[mk_iff] class PosMulReflectLE : Prop extends ContravariantClass α>0 α (fun x y => x * y) (· <= ·)

/--
Definition of `MulPosMono` / `MulPosMono` 的定义

English:
class MulPosMono
  parameters: : Prop where
  axioms and operations (1):
    - mul_le_mul_of_nonneg_right(⦃c) : α⦄ (hc : 0 <= c) ⦃a b : α⦄ (hab : a <= b) : a * c <= b * c

中文:
类 MulPosMono
  参数: : 命题 where
  公理与运算 (1 个):
    - mul_le_mul_of_nonneg_right(⦃c) : α⦄ (hc : 0 <= c) ⦃a b : α⦄ (hab : a <= b) : a * c <= b * c
-/
@[mk_iff] class MulPosMono : Prop where
  /-- Do not use this. Use `_root_.mul_le_mul_of_nonneg_right` instead. -/
  protected mul_le_mul_of_nonneg_right ⦃c : α⦄ (hc : 0 <= c) ⦃a b : α⦄ (hab : a <= b) : a * c <= b * c

/--
Definition of `MulPosStrictMono` / `MulPosStrictMono` 的定义

English:
class MulPosStrictMono
  parameters: : Prop where
  axioms and operations (1):
    - mul_lt_mul_of_pos_right(⦃c) : α⦄ (hc : 0 < c) ⦃a b : α⦄ (hab : a < b) : a * c < b * c

中文:
类 MulPosStrictMono
  参数: : 命题 where
  公理与运算 (1 个):
    - mul_lt_mul_of_pos_right(⦃c) : α⦄ (hc : 0 < c) ⦃a b : α⦄ (hab : a < b) : a * c < b * c
-/
@[mk_iff] class MulPosStrictMono : Prop where
  /-- Do not use this. Use `_root_.mul_lt_mul_of_pos_right` instead. -/
  protected mul_lt_mul_of_pos_right ⦃c : α⦄ (hc : 0 < c) ⦃a b : α⦄ (hab : a < b) : a * c < b * c

/--
Definition of `MulPosReflectLT` / `MulPosReflectLT` 的定义

English:
class MulPosReflectLT
  parameters: : Prop extends ContravariantClass α>=0 α (fun x y => y * x) (· < ·)
  extends: ContravariantClass α>=0 α (fun x y => y * x) (· < ·)
  (no additional axioms)

中文:
类 MulPosReflectLT
  参数: : 命题 extends ContravariantClass α>=0 α (fun x y => y * x) (· < ·)
  继承: ContravariantClass α>=0 α (fun x y => y * x) (· < ·)
  (无附加公理)
-/
@[mk_iff] class MulPosReflectLT : Prop extends ContravariantClass α>=0 α (fun x y => y * x) (· < ·)

/--
Definition of `MulPosReflectLE` / `MulPosReflectLE` 的定义

English:
class MulPosReflectLE
  parameters: : Prop extends ContravariantClass α>0 α (fun x y => y * x) (· <= ·)
  extends: ContravariantClass α>0 α (fun x y => y * x) (· <= ·)
  (no additional axioms)

中文:
类 MulPosReflectLE
  参数: : 命题 extends ContravariantClass α>0 α (fun x y => y * x) (· <= ·)
  继承: ContravariantClass α>0 α (fun x y => y * x) (· <= ·)
  (无附加公理)
-/
@[mk_iff] class MulPosReflectLE : Prop extends ContravariantClass α>0 α (fun x y => y * x) (· <= ·)

end Abbreviations

variable {α}
variable [Mul α] [Zero α]

section Preorder

variable [Preorder α] {a b c d : α}

/--
Instance `PosMulMono.to_covariantClass_nonneg_mul_le` / 实例 `PosMulMono.to_covariantClass_nonneg_mul_le`

English:
instance PosMulMono.to_covariantClass_nonneg_mul_le
  signature: [PosMulMono α]
  body: PosMulMono.mul_le_mul_of_nonneg_left a.2 hbc

中文:
实例 PosMulMono.to_covariantClass_nonneg_mul_le
  签名: [PosMulMono α]
  定义体: PosMulMono.mul_le_mul_of_nonneg_left a.2 hbc

Depends on / 依赖: PosMulMono, PosMulMono.mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_left
-/
instance PosMulMono.to_covariantClass_nonneg_mul_le [PosMulMono α] :
    CovariantClass α>=0 α (fun x y => x * y) (· <= ·) where
  elim a _b _c hbc := PosMulMono.mul_le_mul_of_nonneg_left a.2 hbc

/--
Instance `MulPosMono.to_covariantClass_nonneg_mul_le` / 实例 `MulPosMono.to_covariantClass_nonneg_mul_le`

English:
instance MulPosMono.to_covariantClass_nonneg_mul_le
  signature: [MulPosMono α]
  body: MulPosMono.mul_le_mul_of_nonneg_right a.2 hbc

中文:
实例 MulPosMono.to_covariantClass_nonneg_mul_le
  签名: [MulPosMono α]
  定义体: MulPosMono.mul_le_mul_of_nonneg_right a.2 hbc

Depends on / 依赖: MulPosMono, MulPosMono.mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_right
-/
instance MulPosMono.to_covariantClass_nonneg_mul_le [MulPosMono α] :
    CovariantClass α>=0 α (fun x y => y * x) (· <= ·) where
  elim a _b _c hbc := MulPosMono.mul_le_mul_of_nonneg_right a.2 hbc

/--
Instance `PosMulMono.to_covariantClass_pos_mul_le` / 实例 `PosMulMono.to_covariantClass_pos_mul_le`

English:
instance PosMulMono.to_covariantClass_pos_mul_le
  signature: [PosMulMono α]
  body: PosMulMono.mul_le_mul_of_nonneg_left a.2.le hbc

中文:
实例 PosMulMono.to_covariantClass_pos_mul_le
  签名: [PosMulMono α]
  定义体: PosMulMono.mul_le_mul_of_nonneg_left a.2.le hbc

Depends on / 依赖: PosMulMono, PosMulMono.mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_left
-/
instance PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· <= ·) where
  elim a _b _c hbc := PosMulMono.mul_le_mul_of_nonneg_left a.2.le hbc

/--
Instance `MulPosMono.to_covariantClass_pos_mul_le` / 实例 `MulPosMono.to_covariantClass_pos_mul_le`

English:
instance MulPosMono.to_covariantClass_pos_mul_le
  signature: [MulPosMono α]
  body: MulPosMono.mul_le_mul_of_nonneg_right a.2.le hbc

中文:
实例 MulPosMono.to_covariantClass_pos_mul_le
  签名: [MulPosMono α]
  定义体: MulPosMono.mul_le_mul_of_nonneg_right a.2.le hbc

Depends on / 依赖: MulPosMono, MulPosMono.mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_right
-/
instance MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· <= ·) where
  elim a _b _c hbc := MulPosMono.mul_le_mul_of_nonneg_right a.2.le hbc

/--
Instance `PosMulStrictMono.to_covariantClass_pos_mul_le` / 实例 `PosMulStrictMono.to_covariantClass_pos_mul_le`

English:
instance PosMulStrictMono.to_covariantClass_pos_mul_le
  signature: [PosMulStrictMono α]
  body: PosMulStrictMono.mul_lt_mul_of_pos_left a.2 hbc

中文:
实例 PosMulStrictMono.to_covariantClass_pos_mul_le
  签名: [PosMulStrictMono α]
  定义体: PosMulStrictMono.mul_lt_mul_of_pos_left a.2 hbc

Depends on / 依赖: PosMulStrictMono, PosMulStrictMono.mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_left
-/
instance PosMulStrictMono.to_covariantClass_pos_mul_le [PosMulStrictMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· < ·) where
  elim a _b _c hbc := PosMulStrictMono.mul_lt_mul_of_pos_left a.2 hbc

/--
Instance `MulPosStrictMono.to_covariantClass_pos_mul_le` / 实例 `MulPosStrictMono.to_covariantClass_pos_mul_le`

English:
instance MulPosStrictMono.to_covariantClass_pos_mul_le
  signature: [MulPosStrictMono α]
  body: MulPosStrictMono.mul_lt_mul_of_pos_right a.2 hbc

中文:
实例 MulPosStrictMono.to_covariantClass_pos_mul_le
  签名: [MulPosStrictMono α]
  定义体: MulPosStrictMono.mul_lt_mul_of_pos_right a.2 hbc

Depends on / 依赖: MulPosStrictMono, MulPosStrictMono.mul_lt_mul_of_pos_right, mul_lt_mul_of_pos_right
-/
instance MulPosStrictMono.to_covariantClass_pos_mul_le [MulPosStrictMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· < ·) where
  elim a _b _c hbc := MulPosStrictMono.mul_lt_mul_of_pos_right a.2 hbc

/--
Instance `PosMulReflectLT.to_contravariantClass_pos_mul_lt` / 实例 `PosMulReflectLT.to_contravariantClass_pos_mul_lt`

English:
instance PosMulReflectLT.to_contravariantClass_pos_mul_lt
  signature: [PosMulReflectLT α]
  body: ⟨fun a _ _ bc => @ContravariantClass.elim α>=0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

中文:
实例 PosMulReflectLT.to_contravariantClass_pos_mul_lt
  签名: [PosMulReflectLT α]
  定义体: ⟨fun a _ _ bc => @ContravariantClass.elim α>=0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
instance PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α>=0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

/--
Instance `MulPosReflectLT.to_contravariantClass_pos_mul_lt` / 实例 `MulPosReflectLT.to_contravariantClass_pos_mul_lt`

English:
instance MulPosReflectLT.to_contravariantClass_pos_mul_lt
  signature: [MulPosReflectLT α]
  body: ⟨fun a _ _ bc => @ContravariantClass.elim α>=0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

中文:
实例 MulPosReflectLT.to_contravariantClass_pos_mul_lt
  签名: [MulPosReflectLT α]
  定义体: ⟨fun a _ _ bc => @ContravariantClass.elim α>=0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
instance MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a _ _ bc => @ContravariantClass.elim α>=0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance (priority := 100) MulLeftMono.toPosMulMono [MulLeftMono α] :
    PosMulMono α where mul_le_mul_of_nonneg_left _ _ _ _ := ‹MulLeftMono α›.elim _

instance (priority := 100) MulRightMono.toMulPosMono [MulRightMono α] :
    MulPosMono α where mul_le_mul_of_nonneg_right _ _ _ _ := ‹MulRightMono α›.elim _

instance (priority := 100) MulLeftStrictMono.toPosMulStrictMono [MulLeftStrictMono α] :
    PosMulStrictMono α where mul_lt_mul_of_pos_left _ _ _ _ := ‹MulLeftStrictMono α›.elim _

instance (priority := 100) MulRightStrictMono.toMulPosStrictMono [MulRightStrictMono α] :
    MulPosStrictMono α where mul_lt_mul_of_pos_right _ _ _ _ := ‹MulRightStrictMono α›.elim _

instance (priority := 100) MulLeftMono.toPosMulReflectLT [MulLeftReflectLT α] :
    PosMulReflectLT α where elim _ _ := ‹MulLeftReflectLT α›.elim _

instance (priority := 100) MulRightMono.toMulPosReflectLT [MulRightReflectLT α] :
    MulPosReflectLT α where elim _ _ := ‹MulRightReflectLT α›.elim _

instance (priority := 100) MulLeftStrictMono.toPosMulReflectLE [MulLeftReflectLE α] :
    PosMulReflectLE α where
  elim _ _ _ := ‹MulLeftReflectLE α›.le_of_mul_le_mul_left'

instance (priority := 100) MulRightStrictMono.toMulPosReflectLE [MulRightReflectLE α] :
    MulPosReflectLE α where
  elim _ _ _ := ‹MulRightReflectLE α›.le_of_mul_le_mul_right'

@[gcongr]
/--
theorem `mul_le_mul_of_nonneg_left` / 定理 `mul_le_mul_of_nonneg_left`

English:
theorem mul_le_mul_of_nonneg_left
  given: [PosMulMono α] (hbc : b <= c) (ha : 0 <= a)
  statement: a * b <= a * c
  proof: PosMulMono.mul_le_mul_of_nonneg_left ha hbc

@[gcongr]

中文:
定理 mul_le_mul_of_nonneg_left
  条件: [PosMulMono α] (hbc : b <= c) (ha : 0 <= a)
  结论: a * b <= a * c
  证明: PosMulMono.mul_le_mul_of_nonneg_left ha hbc

@[gcongr]

Depends on / 依赖: PosMulMono, PosMulMono.mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_left
-/
theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b <= c) (ha : 0 <= a) : a * b <= a * c :=
  PosMulMono.mul_le_mul_of_nonneg_left ha hbc

@[gcongr]
/--
theorem `mul_le_mul_of_nonneg_right` / 定理 `mul_le_mul_of_nonneg_right`

English:
theorem mul_le_mul_of_nonneg_right
  given: [MulPosMono α] (hbc : b <= c) (ha : 0 <= a)
  statement: b * a <= c * a
  proof: MulPosMono.mul_le_mul_of_nonneg_right ha hbc

@[gcongr]

中文:
定理 mul_le_mul_of_nonneg_right
  条件: [MulPosMono α] (hbc : b <= c) (ha : 0 <= a)
  结论: b * a <= c * a
  证明: MulPosMono.mul_le_mul_of_nonneg_right ha hbc

@[gcongr]

Depends on / 依赖: MulPosMono, MulPosMono.mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_right
-/
theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b <= c) (ha : 0 <= a) : b * a <= c * a :=
  MulPosMono.mul_le_mul_of_nonneg_right ha hbc

@[gcongr]
/--
theorem `mul_lt_mul_of_pos_left` / 定理 `mul_lt_mul_of_pos_left`

English:
theorem mul_lt_mul_of_pos_left
  given: [PosMulStrictMono α] (hbc : b < c) (ha : 0 < a)
  statement: a * b < a * c
  proof: PosMulStrictMono.mul_lt_mul_of_pos_left ha hbc

@[gcongr]

中文:
定理 mul_lt_mul_of_pos_left
  条件: [PosMulStrictMono α] (hbc : b < c) (ha : 0 < a)
  结论: a * b < a * c
  证明: PosMulStrictMono.mul_lt_mul_of_pos_left ha hbc

@[gcongr]

Depends on / 依赖: PosMulStrictMono, PosMulStrictMono.mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_left
-/
theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc : b < c) (ha : 0 < a) : a * b < a * c :=
  PosMulStrictMono.mul_lt_mul_of_pos_left ha hbc

@[gcongr]
/--
theorem `mul_lt_mul_of_pos_right` / 定理 `mul_lt_mul_of_pos_right`

English:
theorem mul_lt_mul_of_pos_right
  given: [MulPosStrictMono α] (hbc : b < c) (ha : 0 < a)
  statement: b * a < c * a
  proof: MulPosStrictMono.mul_lt_mul_of_pos_right ha hbc

中文:
定理 mul_lt_mul_of_pos_right
  条件: [MulPosStrictMono α] (hbc : b < c) (ha : 0 < a)
  结论: b * a < c * a
  证明: MulPosStrictMono.mul_lt_mul_of_pos_right ha hbc

Depends on / 依赖: MulPosStrictMono, MulPosStrictMono.mul_lt_mul_of_pos_right, mul_lt_mul_of_pos_right
-/
theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (hbc : b < c) (ha : 0 < a) : b * a < c * a :=
  MulPosStrictMono.mul_lt_mul_of_pos_right ha hbc

/--
theorem `lt_of_mul_lt_mul_left` / 定理 `lt_of_mul_lt_mul_left`

English:
theorem lt_of_mul_lt_mul_left
  given: [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 <= a)
  statement: b < c
  proof: @ContravariantClass.elim α>=0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h

中文:
定理 lt_of_mul_lt_mul_left
  条件: [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 <= a)
  结论: b < c
  证明: @ContravariantClass.elim α>=0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
theorem lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 <= a) : b < c :=
  @ContravariantClass.elim α>=0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h

/--
theorem `lt_of_mul_lt_mul_right` / 定理 `lt_of_mul_lt_mul_right`

English:
theorem lt_of_mul_lt_mul_right
  given: [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 <= a)
  statement: b < c
  proof: @ContravariantClass.elim α>=0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h

中文:
定理 lt_of_mul_lt_mul_right
  条件: [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 <= a)
  结论: b < c
  证明: @ContravariantClass.elim α>=0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 <= a) : b < c :=
  @ContravariantClass.elim α>=0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h

/--
theorem `le_of_mul_le_mul_left` / 定理 `le_of_mul_le_mul_left`

English:
theorem le_of_mul_le_mul_left
  given: [PosMulReflectLE α] (bc : a * b <= a * c) (a0 : 0 < a)
  statement: b <= c
  proof: @ContravariantClass.elim α>0 α (fun x y => x * y) (· <= ·) _ ⟨a, a0⟩ _ _ bc

中文:
定理 le_of_mul_le_mul_left
  条件: [PosMulReflectLE α] (bc : a * b <= a * c) (a0 : 0 < a)
  结论: b <= c
  证明: @ContravariantClass.elim α>0 α (fun x y => x * y) (· <= ·) _ ⟨a, a0⟩ _ _ bc

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b <= a * c) (a0 : 0 < a) : b <= c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· <= ·) _ ⟨a, a0⟩ _ _ bc

/--
theorem `le_of_mul_le_mul_right` / 定理 `le_of_mul_le_mul_right`

English:
theorem le_of_mul_le_mul_right
  given: [MulPosReflectLE α] (bc : b * a <= c * a) (a0 : 0 < a)
  statement: b <= c
  proof: @ContravariantClass.elim α>0 α (fun x y => y * x) (· <= ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
alias le_of_mul_le_mul_of_pos_right

中文:
定理 le_of_mul_le_mul_right
  条件: [MulPosReflectLE α] (bc : b * a <= c * a) (a0 : 0 < a)
  结论: b <= c
  证明: @ContravariantClass.elim α>0 α (fun x y => y * x) (· <= ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
alias le_of_mul_le_mul_of_pos_right

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a <= c * a) (a0 : 0 < a) : b <= c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· <= ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right
/--
lemma `Function.Injective.posMulMono` / 引理 `Function.Injective.posMulMono`

English:
lemma Function.Injective.posMulMono
  statement: [PosMulMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
  proof: by
    rw [← le]; rw [mul]; rw [mul]; exact mul_le_mul_of_nonneg_left (le.2 hbc) (by rwa [← zero, le])

中文:
引理 Function.Injective.posMulMono
  结论: [PosMulMono α] {β : 类型} [Zero β] [Mul β] [Preorder β]
  证明: by
    rw [← le]; rw [mul]; rw [mul]; exact mul_le_mul_of_nonneg_left (le.2 hbc) (by rwa [← zero, le])

Depends on / 依赖: mul_le_mul_of_nonneg_left
-/
lemma Function.Injective.posMulMono [PosMulMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
    (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y)
    (le : forall {x y}, f x <= f y ↔ x <= y) : PosMulMono β where
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; exact mul_le_mul_of_nonneg_left (le.2 hbc) (by rwa [← zero, le])

/--
lemma `Function.Injective.mulPosMono` / 引理 `Function.Injective.mulPosMono`

English:
lemma Function.Injective.mulPosMono
  statement: [MulPosMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
  proof: by
    rw [← le]; rw [mul]; rw [mul]; exact mul_le_mul_of_nonneg_right (le.2 hbc) (by rwa [← zero, le])

中文:
引理 Function.Injective.mulPosMono
  结论: [MulPosMono α] {β : 类型} [Zero β] [Mul β] [Preorder β]
  证明: by
    rw [← le]; rw [mul]; rw [mul]; exact mul_le_mul_of_nonneg_right (le.2 hbc) (by rwa [← zero, le])

Depends on / 依赖: mul_le_mul_of_nonneg_right
-/
lemma Function.Injective.mulPosMono [MulPosMono α] {β : Type*} [Zero β] [Mul β] [Preorder β]
    (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y)
    (le : forall {x y}, f x <= f y ↔ x <= y) : MulPosMono β where
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; exact mul_le_mul_of_nonneg_right (le.2 hbc) (by rwa [← zero, le])

/--
lemma `Function.Injective.posMulStrictMono` / 引理 `Function.Injective.posMulStrictMono`

English:
lemma Function.Injective.posMulStrictMono
  statement: [PosMulStrictMono α] {β : Type*} [Zero β] [Mul β]
  proof: by
    rw [← lt]; rw [mul]; rw [mul]; exact mul_lt_mul_of_pos_left (lt.2 hbc) (by rwa [← zero, lt])

中文:
引理 Function.Injective.posMulStrictMono
  结论: [PosMulStrictMono α] {β : 类型} [Zero β] [Mul β]
  证明: by
    rw [← lt]; rw [mul]; rw [mul]; exact mul_lt_mul_of_pos_left (lt.2 hbc) (by rwa [← zero, lt])

Depends on / 依赖: mul_lt_mul_of_pos_left
-/
lemma Function.Injective.posMulStrictMono [PosMulStrictMono α] {β : Type*} [Zero β] [Mul β]
    [Preorder β] (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y)
    (lt : forall {x y}, f x < f y ↔ x < y) : PosMulStrictMono β where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; exact mul_lt_mul_of_pos_left (lt.2 hbc) (by rwa [← zero, lt])

/--
lemma `Function.Injective.mulPosStrictMono` / 引理 `Function.Injective.mulPosStrictMono`

English:
lemma Function.Injective.mulPosStrictMono
  statement: [MulPosStrictMono α] {β : Type*} [Zero β] [Mul β]
  proof: by
    rw [← lt]; rw [mul]; rw [mul]; exact mul_lt_mul_of_pos_right (lt.2 hbc) (by rwa [← zero, lt])

@[simp]

中文:
引理 Function.Injective.mulPosStrictMono
  结论: [MulPosStrictMono α] {β : 类型} [Zero β] [Mul β]
  证明: by
    rw [← lt]; rw [mul]; rw [mul]; exact mul_lt_mul_of_pos_right (lt.2 hbc) (by rwa [← zero, lt])

@[simp]

Depends on / 依赖: mul_lt_mul_of_pos_right
-/
lemma Function.Injective.mulPosStrictMono [MulPosStrictMono α] {β : Type*} [Zero β] [Mul β]
    [Preorder β] (f : β -> α) (zero : f 0 = 0) (mul : forall x y, f (x * y) = f x * f y)
    (lt : forall {x y}, f x < f y ↔ x < y) : MulPosStrictMono β where
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; exact mul_lt_mul_of_pos_right (lt.2 hbc) (by rwa [← zero, lt])

@[simp]
/--
theorem `mul_lt_mul_iff_right₀` / 定理 `mul_lt_mul_iff_right₀`

English:
theorem mul_lt_mul_iff_right₀
  given: [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a)
  proof: lt_of_mul_lt_mul_left h a0.le
  mpr h := mul_lt_mul_of_pos_left h a0

@[simp]

中文:
定理 mul_lt_mul_iff_right₀
  条件: [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a)
  证明: lt_of_mul_lt_mul_left h a0.le
  mpr h := mul_lt_mul_of_pos_left h a0

@[simp]

Depends on / 依赖: a0.le, lt_of_mul_lt_mul_left
-/
theorem mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c where
  mp h := lt_of_mul_lt_mul_left h a0.le
  mpr h := mul_lt_mul_of_pos_left h a0

@[simp]
/--
theorem `mul_lt_mul_iff_left₀` / 定理 `mul_lt_mul_iff_left₀`

English:
theorem mul_lt_mul_iff_left₀
  given: [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a)
  proof: lt_of_mul_lt_mul_right h a0.le
  mpr h := mul_lt_mul_of_pos_right h a0

@[simp]

中文:
定理 mul_lt_mul_iff_left₀
  条件: [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a)
  证明: lt_of_mul_lt_mul_right h a0.le
  mpr h := mul_lt_mul_of_pos_right h a0

@[simp]

Depends on / 依赖: a0.le, lt_of_mul_lt_mul_right
-/
theorem mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c where
  mp h := lt_of_mul_lt_mul_right h a0.le
  mpr h := mul_lt_mul_of_pos_right h a0

@[simp]
/--
theorem `mul_le_mul_iff_right₀` / 定理 `mul_le_mul_iff_right₀`

English:
theorem mul_le_mul_iff_right₀
  given: [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a)
  proof: @rel_iff_cov α>0 α (fun x y => x * y) (· <= ·) _ _ ⟨a, a0⟩ _ _

@[simp]

中文:
定理 mul_le_mul_iff_right₀
  条件: [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a)
  证明: @rel_iff_cov α>0 α (fun x y => x * y) (· <= ·) _ _ ⟨a, a0⟩ _ _

@[simp]

Depends on / 依赖: rel_iff_cov
-/
theorem mul_le_mul_iff_right₀ [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) :
    a * b <= a * c ↔ b <= c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· <= ·) _ _ ⟨a, a0⟩ _ _

@[simp]
/--
theorem `mul_le_mul_iff_left₀` / 定理 `mul_le_mul_iff_left₀`

English:
theorem mul_le_mul_iff_left₀
  given: [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a)
  proof: @rel_iff_cov α>0 α (fun x y => y * x) (· <= ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_iff_right₀
alias mul_le_mul_iff_of_pos_right := mul_le_mul_iff_left₀
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_iff_right₀
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_iff_left₀

中文:
定理 mul_le_mul_iff_left₀
  条件: [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a)
  证明: @rel_iff_cov α>0 α (fun x y => y * x) (· <= ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_iff_right₀
alias mul_le_mul_iff_of_pos_right := mul_le_mul_iff_left₀
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_iff_right₀
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_iff_left₀

Depends on / 依赖: rel_iff_cov
-/
theorem mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) :
    b * a <= c * a ↔ b <= c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· <= ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_iff_right₀
alias mul_le_mul_iff_of_pos_right := mul_le_mul_iff_left₀
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_iff_right₀
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_iff_left₀

/--
theorem `mul_le_mul_of_nonneg` / 定理 `mul_le_mul_of_nonneg`

English:
theorem mul_le_mul_of_nonneg
  statement: [PosMulMono α] [MulPosMono α]
  proof: (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)

中文:
定理 mul_le_mul_of_nonneg
  结论: [PosMulMono α] [MulPosMono α]
  证明: (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right
-/
theorem mul_le_mul_of_nonneg [PosMulMono α] [MulPosMono α]
    (h₁ : a <= b) (h₂ : c <= d) (a0 : 0 <= a) (d0 : 0 <= d) : a * c <= b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)

/--
theorem `mul_le_mul_of_nonneg'` / 定理 `mul_le_mul_of_nonneg'`

English:
theorem mul_le_mul_of_nonneg'
  statement: [PosMulMono α] [MulPosMono α]
  proof: (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)

中文:
定理 mul_le_mul_of_nonneg'
  结论: [PosMulMono α] [MulPosMono α]
  证明: (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right
-/
theorem mul_le_mul_of_nonneg' [PosMulMono α] [MulPosMono α]
    (h₁ : a <= b) (h₂ : c <= d) (c0 : 0 <= c) (b0 : 0 <= b) : a * c <= b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)

/--
theorem `mul_lt_mul_of_le_of_lt_of_pos_of_nonneg` / 定理 `mul_lt_mul_of_le_of_lt_of_pos_of_nonneg`

English:
theorem mul_lt_mul_of_le_of_lt_of_pos_of_nonneg
  statement: [PosMulStrictMono α] [MulPosMono α]
  proof: (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

alias mul_lt_mul_of_pos_of_nonneg := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg

中文:
定理 mul_lt_mul_of_le_of_lt_of_pos_of_nonneg
  结论: [PosMulStrictMono α] [MulPosMono α]
  证明: (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

alias mul_lt_mul_of_pos_of_nonneg := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg

Depends on / 依赖: mul_le_mul_of_nonneg_right, mul_lt_mul_of_pos_left, trans_le
-/
theorem mul_lt_mul_of_le_of_lt_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a <= b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 <= d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

alias mul_lt_mul_of_pos_of_nonneg := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg

/--
theorem `mul_lt_mul_of_le_of_lt_of_nonneg_of_pos` / 定理 `mul_lt_mul_of_le_of_lt_of_nonneg_of_pos`

English:
theorem mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
  statement: [PosMulStrictMono α] [MulPosMono α]
  proof: (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

alias mul_lt_mul_of_nonneg_of_pos' := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos

中文:
定理 mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
  结论: [PosMulStrictMono α] [MulPosMono α]
  证明: (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

alias mul_lt_mul_of_nonneg_of_pos' := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos

Depends on / 依赖: mul_le_mul_of_nonneg_right, mul_lt_mul_of_pos_left, trans_lt
-/
theorem mul_lt_mul_of_le_of_lt_of_nonneg_of_pos [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a <= b) (h₂ : c < d) (c0 : 0 <= c) (b0 : 0 < b) : a * c < b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

alias mul_lt_mul_of_nonneg_of_pos' := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos

/--
theorem `mul_lt_mul_of_lt_of_le_of_nonneg_of_pos` / 定理 `mul_lt_mul_of_lt_of_le_of_nonneg_of_pos`

English:
theorem mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
  statement: [PosMulMono α] [MulPosStrictMono α]
  proof: (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

alias mul_lt_mul_of_nonneg_of_pos := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos

中文:
定理 mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
  结论: [PosMulMono α] [MulPosStrictMono α]
  证明: (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

alias mul_lt_mul_of_nonneg_of_pos := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_lt_mul_of_pos_right, trans_lt
-/
theorem mul_lt_mul_of_lt_of_le_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c <= d) (a0 : 0 <= a) (d0 : 0 < d) : a * c < b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

alias mul_lt_mul_of_nonneg_of_pos := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos

/--
theorem `mul_lt_mul_of_lt_of_le_of_pos_of_nonneg` / 定理 `mul_lt_mul_of_lt_of_le_of_pos_of_nonneg`

English:
theorem mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
  statement: [PosMulMono α] [MulPosStrictMono α]
  proof: (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

alias mul_lt_mul_of_pos_of_nonneg' := mul_lt_mul_of_lt_of_le_of_pos_of_nonneg

中文:
定理 mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
  结论: [PosMulMono α] [MulPosStrictMono α]
  证明: (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

alias mul_lt_mul_of_pos_of_nonneg' := mul_lt_mul_of_lt_of_le_of_pos_of_nonneg

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_lt_mul_of_pos_right, trans_le
-/
theorem mul_lt_mul_of_lt_of_le_of_pos_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c <= d) (c0 : 0 < c) (b0 : 0 <= b) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

alias mul_lt_mul_of_pos_of_nonneg' := mul_lt_mul_of_lt_of_le_of_pos_of_nonneg

/--
theorem `mul_lt_mul_of_pos` / 定理 `mul_lt_mul_of_pos`

English:
theorem mul_lt_mul_of_pos
  statement: [PosMulStrictMono α] [MulPosStrictMono α]
  proof: (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)

中文:
定理 mul_lt_mul_of_pos
  结论: [PosMulStrictMono α] [MulPosStrictMono α]
  证明: (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)

Depends on / 依赖: mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_right
-/
theorem mul_lt_mul_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)

/--
theorem `mul_lt_mul_of_pos'` / 定理 `mul_lt_mul_of_pos'`

English:
theorem mul_lt_mul_of_pos'
  statement: [PosMulStrictMono α] [MulPosStrictMono α]
  proof: (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

alias mul_le_mul := mul_le_mul_of_nonneg'

中文:
定理 mul_lt_mul_of_pos'
  结论: [PosMulStrictMono α] [MulPosStrictMono α]
  证明: (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

alias mul_le_mul := mul_le_mul_of_nonneg'

Depends on / 依赖: mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_right
-/
theorem mul_lt_mul_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

alias mul_le_mul := mul_le_mul_of_nonneg'
attribute [gcongr] mul_le_mul

alias mul_lt_mul := mul_lt_mul_of_pos_of_nonneg'

alias mul_lt_mul' := mul_lt_mul_of_nonneg_of_pos'

/--
theorem `mul_le_of_mul_le_of_nonneg_left` / 定理 `mul_le_of_mul_le_of_nonneg_left`

English:
theorem mul_le_of_mul_le_of_nonneg_left
  given: [PosMulMono α] (h : a * b <= c) (hle : d <= b) (a0 : 0 <= a)
  proof: (mul_le_mul_of_nonneg_left hle a0).trans h

中文:
定理 mul_le_of_mul_le_of_nonneg_left
  条件: [PosMulMono α] (h : a * b <= c) (hle : d <= b) (a0 : 0 <= a)
  证明: (mul_le_mul_of_nonneg_left hle a0).trans h

Depends on / 依赖: mul_le_mul_of_nonneg_left
-/
theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b <= c) (hle : d <= b) (a0 : 0 <= a) :
    a * d <= c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h

/--
theorem `mul_lt_of_mul_lt_of_nonneg_left` / 定理 `mul_lt_of_mul_lt_of_nonneg_left`

English:
theorem mul_lt_of_mul_lt_of_nonneg_left
  given: [PosMulMono α] (h : a * b < c) (hle : d <= b) (a0 : 0 <= a)
  proof: (mul_le_mul_of_nonneg_left hle a0).trans_lt h

中文:
定理 mul_lt_of_mul_lt_of_nonneg_left
  条件: [PosMulMono α] (h : a * b < c) (hle : d <= b) (a0 : 0 <= a)
  证明: (mul_le_mul_of_nonneg_left hle a0).trans_lt h

Depends on / 依赖: mul_le_mul_of_nonneg_left, trans_lt
-/
theorem mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : d <= b) (a0 : 0 <= a) :
    a * d < c :=
  (mul_le_mul_of_nonneg_left hle a0).trans_lt h

/--
theorem `le_mul_of_le_mul_of_nonneg_left` / 定理 `le_mul_of_le_mul_of_nonneg_left`

English:
theorem le_mul_of_le_mul_of_nonneg_left
  given: [PosMulMono α] (h : a <= b * c) (hle : c <= d) (b0 : 0 <= b)
  proof: h.trans (mul_le_mul_of_nonneg_left hle b0)

中文:
定理 le_mul_of_le_mul_of_nonneg_left
  条件: [PosMulMono α] (h : a <= b * c) (hle : c <= d) (b0 : 0 <= b)
  证明: h.trans (mul_le_mul_of_nonneg_left hle b0)

Depends on / 依赖: h.trans, mul_le_mul_of_nonneg_left
-/
theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a <= b * c) (hle : c <= d) (b0 : 0 <= b) :
    a <= b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)

/--
theorem `lt_mul_of_lt_mul_of_nonneg_left` / 定理 `lt_mul_of_lt_mul_of_nonneg_left`

English:
theorem lt_mul_of_lt_mul_of_nonneg_left
  given: [PosMulMono α] (h : a < b * c) (hle : c <= d) (b0 : 0 <= b)
  proof: h.trans_le (mul_le_mul_of_nonneg_left hle b0)

中文:
定理 lt_mul_of_lt_mul_of_nonneg_left
  条件: [PosMulMono α] (h : a < b * c) (hle : c <= d) (b0 : 0 <= b)
  证明: h.trans_le (mul_le_mul_of_nonneg_left hle b0)

Depends on / 依赖: h.trans_le, mul_le_mul_of_nonneg_left, trans_le
-/
theorem lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hle : c <= d) (b0 : 0 <= b) :
    a < b * d :=
  h.trans_le (mul_le_mul_of_nonneg_left hle b0)

/--
theorem `mul_le_of_mul_le_of_nonneg_right` / 定理 `mul_le_of_mul_le_of_nonneg_right`

English:
theorem mul_le_of_mul_le_of_nonneg_right
  given: [MulPosMono α] (h : a * b <= c) (hle : d <= a) (b0 : 0 <= b)
  proof: (mul_le_mul_of_nonneg_right hle b0).trans h

中文:
定理 mul_le_of_mul_le_of_nonneg_right
  条件: [MulPosMono α] (h : a * b <= c) (hle : d <= a) (b0 : 0 <= b)
  证明: (mul_le_mul_of_nonneg_right hle b0).trans h

Depends on / 依赖: mul_le_mul_of_nonneg_right
-/
theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b <= c) (hle : d <= a) (b0 : 0 <= b) :
    d * b <= c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h

/--
theorem `mul_lt_of_mul_lt_of_nonneg_right` / 定理 `mul_lt_of_mul_lt_of_nonneg_right`

English:
theorem mul_lt_of_mul_lt_of_nonneg_right
  given: [MulPosMono α] (h : a * b < c) (hle : d <= a) (b0 : 0 <= b)
  proof: (mul_le_mul_of_nonneg_right hle b0).trans_lt h

中文:
定理 mul_lt_of_mul_lt_of_nonneg_right
  条件: [MulPosMono α] (h : a * b < c) (hle : d <= a) (b0 : 0 <= b)
  证明: (mul_le_mul_of_nonneg_right hle b0).trans_lt h

Depends on / 依赖: mul_le_mul_of_nonneg_right, trans_lt
-/
theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hle : d <= a) (b0 : 0 <= b) :
    d * b < c :=
  (mul_le_mul_of_nonneg_right hle b0).trans_lt h

/--
theorem `le_mul_of_le_mul_of_nonneg_right` / 定理 `le_mul_of_le_mul_of_nonneg_right`

English:
theorem le_mul_of_le_mul_of_nonneg_right
  given: [MulPosMono α] (h : a <= b * c) (hle : b <= d) (c0 : 0 <= c)
  proof: h.trans (mul_le_mul_of_nonneg_right hle c0)

中文:
定理 le_mul_of_le_mul_of_nonneg_right
  条件: [MulPosMono α] (h : a <= b * c) (hle : b <= d) (c0 : 0 <= c)
  证明: h.trans (mul_le_mul_of_nonneg_right hle c0)

Depends on / 依赖: h.trans, mul_le_mul_of_nonneg_right
-/
theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a <= b * c) (hle : b <= d) (c0 : 0 <= c) :
    a <= d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)

/--
theorem `lt_mul_of_lt_mul_of_nonneg_right` / 定理 `lt_mul_of_lt_mul_of_nonneg_right`

English:
theorem lt_mul_of_lt_mul_of_nonneg_right
  given: [MulPosMono α] (h : a < b * c) (hle : b <= d) (c0 : 0 <= c)
  proof: h.trans_le (mul_le_mul_of_nonneg_right hle c0)

中文:
定理 lt_mul_of_lt_mul_of_nonneg_right
  条件: [MulPosMono α] (h : a < b * c) (hle : b <= d) (c0 : 0 <= c)
  证明: h.trans_le (mul_le_mul_of_nonneg_right hle c0)

Depends on / 依赖: h.trans_le, mul_le_mul_of_nonneg_right, trans_le
-/
theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hle : b <= d) (c0 : 0 <= c) :
    a < d * c :=
  h.trans_le (mul_le_mul_of_nonneg_right hle c0)

variable [IsMulCommutative α]

/--
theorem `posMulMono_iff_mulPosMono` / 定理 `posMulMono_iff_mulPosMono`

English:
theorem posMulMono_iff_mulPosMono
  statement: PosMulMono α ↔ MulPosMono α
  proof: by
  simp [posMulMono_iff, mulPosMono_iff, mul_comm']

中文:
定理 posMulMono_iff_mulPosMono
  结论: PosMulMono α ↔ MulPosMono α
  证明: by
  simp [posMulMono_iff, mulPosMono_iff, mul_comm']

Depends on / 依赖: mulPosMono_iff, mul_comm, posMulMono_iff
-/
theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp [posMulMono_iff, mulPosMono_iff, mul_comm']

/--
theorem `PosMulMono.toMulPosMono` / 定理 `PosMulMono.toMulPosMono`

English:
theorem PosMulMono.toMulPosMono
  given: [PosMulMono α]
  statement: MulPosMono α
  proof: posMulMono_iff_mulPosMono.mp ‹_›

中文:
定理 PosMulMono.toMulPosMono
  条件: [PosMulMono α]
  结论: MulPosMono α
  证明: posMulMono_iff_mulPosMono.mp ‹_›

Depends on / 依赖: posMulMono_iff_mulPosMono, posMulMono_iff_mulPosMono.mp
-/
theorem PosMulMono.toMulPosMono [PosMulMono α] : MulPosMono α := posMulMono_iff_mulPosMono.mp ‹_›

/--
theorem `posMulStrictMono_iff_mulPosStrictMono` / 定理 `posMulStrictMono_iff_mulPosStrictMono`

English:
theorem posMulStrictMono_iff_mulPosStrictMono
  statement: PosMulStrictMono α ↔ MulPosStrictMono α
  proof: by
  simp [posMulStrictMono_iff, mulPosStrictMono_iff, mul_comm']

中文:
定理 posMulStrictMono_iff_mulPosStrictMono
  结论: PosMulStrictMono α ↔ MulPosStrictMono α
  证明: by
  simp [posMulStrictMono_iff, mulPosStrictMono_iff, mul_comm']

Depends on / 依赖: mulPosStrictMono_iff, mul_comm, posMulStrictMono_iff
-/
theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp [posMulStrictMono_iff, mulPosStrictMono_iff, mul_comm']

/--
theorem `PosMulStrictMono.toMulPosStrictMono` / 定理 `PosMulStrictMono.toMulPosStrictMono`

English:
theorem PosMulStrictMono.toMulPosStrictMono
  given: [PosMulStrictMono α]
  statement: MulPosStrictMono α
  proof: posMulStrictMono_iff_mulPosStrictMono.mp ‹_›

中文:
定理 PosMulStrictMono.toMulPosStrictMono
  条件: [PosMulStrictMono α]
  结论: MulPosStrictMono α
  证明: posMulStrictMono_iff_mulPosStrictMono.mp ‹_›

Depends on / 依赖: posMulStrictMono_iff_mulPosStrictMono, posMulStrictMono_iff_mulPosStrictMono.mp
-/
theorem PosMulStrictMono.toMulPosStrictMono [PosMulStrictMono α] : MulPosStrictMono α :=
  posMulStrictMono_iff_mulPosStrictMono.mp ‹_›

/--
theorem `posMulReflectLE_iff_mulPosReflectLE` / 定理 `posMulReflectLE_iff_mulPosReflectLE`

English:
theorem posMulReflectLE_iff_mulPosReflectLE
  statement: PosMulReflectLE α ↔ MulPosReflectLE α
  proof: by
  simp [posMulReflectLE_iff, mulPosReflectLE_iff, mul_comm']

中文:
定理 posMulReflectLE_iff_mulPosReflectLE
  结论: PosMulReflectLE α ↔ MulPosReflectLE α
  证明: by
  simp [posMulReflectLE_iff, mulPosReflectLE_iff, mul_comm']

Depends on / 依赖: mulPosReflectLE_iff, mul_comm, posMulReflectLE_iff
-/
theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp [posMulReflectLE_iff, mulPosReflectLE_iff, mul_comm']

/--
theorem `PosMulReflectLE.toMulPosReflectLE` / 定理 `PosMulReflectLE.toMulPosReflectLE`

English:
theorem PosMulReflectLE.toMulPosReflectLE
  given: [PosMulReflectLE α]
  statement: MulPosReflectLE α
  proof: posMulReflectLE_iff_mulPosReflectLE.mp ‹_›

中文:
定理 PosMulReflectLE.toMulPosReflectLE
  条件: [PosMulReflectLE α]
  结论: MulPosReflectLE α
  证明: posMulReflectLE_iff_mulPosReflectLE.mp ‹_›

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toZeroLEOneClass, posMulReflectLE_iff_mulPosReflectLE, posMulReflectLE_iff_mulPosReflectLE.mp, toZeroLEOneClass
-/
theorem PosMulReflectLE.toMulPosReflectLE [PosMulReflectLE α] : MulPosReflectLE α :=
  posMulReflectLE_iff_mulPosReflectLE.mp ‹_›

/--
theorem `posMulReflectLT_iff_mulPosReflectLT` / 定理 `posMulReflectLT_iff_mulPosReflectLT`

English:
theorem posMulReflectLT_iff_mulPosReflectLT
  statement: PosMulReflectLT α ↔ MulPosReflectLT α
  proof: by
  simp [posMulReflectLT_iff, mulPosReflectLT_iff, mul_comm']

中文:
定理 posMulReflectLT_iff_mulPosReflectLT
  结论: PosMulReflectLT α ↔ MulPosReflectLT α
  证明: by
  simp [posMulReflectLT_iff, mulPosReflectLT_iff, mul_comm']

Depends on / 依赖: mulPosReflectLT_iff, mul_comm, posMulReflectLT_iff
-/
theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp [posMulReflectLT_iff, mulPosReflectLT_iff, mul_comm']

/--
theorem `PosMulReflectLT.toMulPosReflectLT` / 定理 `PosMulReflectLT.toMulPosReflectLT`

English:
theorem PosMulReflectLT.toMulPosReflectLT
  given: [PosMulReflectLT α]
  statement: MulPosReflectLT α
  proof: posMulReflectLT_iff_mulPosReflectLT.mp ‹_›

中文:
定理 PosMulReflectLT.toMulPosReflectLT
  条件: [PosMulReflectLT α]
  结论: MulPosReflectLT α
  证明: posMulReflectLT_iff_mulPosReflectLT.mp ‹_›

Depends on / 依赖: NonUnitalNonAssocSemiring, posMulReflectLT_iff_mulPosReflectLT, posMulReflectLT_iff_mulPosReflectLT.mp, toMulLeftMono
-/
theorem PosMulReflectLT.toMulPosReflectLT [PosMulReflectLT α] : MulPosReflectLT α :=
  posMulReflectLT_iff_mulPosReflectLT.mp ‹_›

end Preorder

section LinearOrder

variable [LinearOrder α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulReflectLE [PosMulStrictMono α] :
    PosMulReflectLE α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosReflectLE [MulPosStrictMono α] :
    MulPosReflectLE α where
  elim := (covariant_lt_iff_contravariant_le _ _ _).1 CovariantClass.elim

/--
theorem `PosMulReflectLE.toPosMulStrictMono` / 定理 `PosMulReflectLE.toPosMulStrictMono`

English:
theorem PosMulReflectLE.toPosMulStrictMono
  given: [PosMulReflectLE α]
  statement: PosMulStrictMono α where
  proof: not_le.1 fun h => hbc.not_ge le_of_mul_le_mul_left h ha

中文:
定理 PosMulReflectLE.toPosMulStrictMono
  条件: [PosMulReflectLE α]
  结论: PosMulStrictMono α where
  证明: not_le.1 fun h => hbc.not_ge le_of_mul_le_mul_left h ha

Depends on / 依赖: NonUnitalNonAssocSemiring, hbc.not_ge, le_of_mul_le_mul_left, not_ge, not_le, toMulRightMono
-/
theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
not_le.1 fun h => hbc.not_ge le_of_mul_le_mul_left h ha

/--
theorem `MulPosReflectLE.toMulPosStrictMono` / 定理 `MulPosReflectLE.toMulPosStrictMono`

English:
theorem MulPosReflectLE.toMulPosStrictMono
  given: [MulPosReflectLE α]
  statement: MulPosStrictMono α where
  proof: not_le.1 fun h => hbc.not_ge le_of_mul_le_mul_right h ha

中文:
定理 MulPosReflectLE.toMulPosStrictMono
  条件: [MulPosReflectLE α]
  结论: MulPosStrictMono α where
  证明: not_le.1 fun h => hbc.not_ge le_of_mul_le_mul_right h ha

Depends on / 依赖: hbc.not_ge, le_of_mul_le_mul_right, not_ge, not_le
-/
theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
not_le.1 fun h => hbc.not_ge le_of_mul_le_mul_right h ha

/--
theorem `posMulStrictMono_iff_posMulReflectLE` / 定理 `posMulStrictMono_iff_posMulReflectLE`

English:
theorem posMulStrictMono_iff_posMulReflectLE
  statement: PosMulStrictMono α ↔ PosMulReflectLE α
  proof: ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩

中文:
定理 posMulStrictMono_iff_posMulReflectLE
  结论: PosMulStrictMono α ↔ PosMulReflectLE α
  证明: ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩

Depends on / 依赖: PosMulReflectLE, PosMulReflectLE.toPosMulStrictMono, PosMulStrictMono, PosMulStrictMono.toPosMulReflectLE, toPosMulReflectLE, toPosMulStrictMono
-/
theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α :=
  ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩

/--
theorem `mulPosStrictMono_iff_mulPosReflectLE` / 定理 `mulPosStrictMono_iff_mulPosReflectLE`

English:
theorem mulPosStrictMono_iff_mulPosReflectLE
  statement: MulPosStrictMono α ↔ MulPosReflectLE α
  proof: ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩

中文:
定理 mulPosStrictMono_iff_mulPosReflectLE
  结论: MulPosStrictMono α ↔ MulPosReflectLE α
  证明: ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩

Depends on / 依赖: MulPosReflectLE, MulPosReflectLE.toMulPosStrictMono, MulPosStrictMono, MulPosStrictMono.toMulPosReflectLE, toMulPosReflectLE, toMulPosStrictMono
-/
theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α :=
  ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩

/--
theorem `PosMulReflectLT.toPosMulMono` / 定理 `PosMulReflectLT.toPosMulMono`

English:
theorem PosMulReflectLT.toPosMulMono
  given: [PosMulReflectLT α]
  statement: PosMulMono α where
  proof: not_lt.1 fun h => hbc.not_gt lt_of_mul_lt_mul_left h ha

中文:
定理 PosMulReflectLT.toPosMulMono
  条件: [PosMulReflectLT α]
  结论: PosMulMono α where
  证明: not_lt.1 fun h => hbc.not_gt lt_of_mul_lt_mul_left h ha

Depends on / 依赖: hbc.not_gt, lt_of_mul_lt_mul_left, not_gt, not_lt
-/
theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α where
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
not_lt.1 fun h => hbc.not_gt lt_of_mul_lt_mul_left h ha

/--
theorem `MulPosReflectLT.toMulPosMono` / 定理 `MulPosReflectLT.toMulPosMono`

English:
theorem MulPosReflectLT.toMulPosMono
  given: [MulPosReflectLT α]
  statement: MulPosMono α where
  proof: not_lt.1 fun h => hbc.not_gt lt_of_mul_lt_mul_right h ha

中文:
定理 MulPosReflectLT.toMulPosMono
  条件: [MulPosReflectLT α]
  结论: MulPosMono α where
  证明: not_lt.1 fun h => hbc.not_gt lt_of_mul_lt_mul_right h ha

Depends on / 依赖: hbc.not_gt, lt_of_mul_lt_mul_right, not_gt, not_lt
-/
theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α where
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
not_lt.1 fun h => hbc.not_gt lt_of_mul_lt_mul_right h ha

/--
theorem `PosMulMono.toPosMulReflectLT` / 定理 `PosMulMono.toPosMulReflectLT`

English:
theorem PosMulMono.toPosMulReflectLT
  given: [PosMulMono α]
  statement: PosMulReflectLT α where
  proof: (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc => mul_le_mul_of_nonneg_left hbc a.2

中文:
定理 PosMulMono.toPosMulReflectLT
  条件: [PosMulMono α]
  结论: PosMulReflectLT α where
  证明: (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc => mul_le_mul_of_nonneg_left hbc a.2

Depends on / 依赖: covariant_le_iff_contravariant_lt
-/
theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc => mul_le_mul_of_nonneg_left hbc a.2

/--
theorem `MulPosMono.toMulPosReflectLT` / 定理 `MulPosMono.toMulPosReflectLT`

English:
theorem MulPosMono.toMulPosReflectLT
  given: [MulPosMono α]
  statement: MulPosReflectLT α where
  proof: (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc => mul_le_mul_of_nonneg_right hbc a.2

中文:
定理 MulPosMono.toMulPosReflectLT
  条件: [MulPosMono α]
  结论: MulPosReflectLT α where
  证明: (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc => mul_le_mul_of_nonneg_right hbc a.2

Depends on / 依赖: covariant_le_iff_contravariant_lt
-/
theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc => mul_le_mul_of_nonneg_right hbc a.2


/--
theorem `posMulMono_iff_posMulReflectLT` / 定理 `posMulMono_iff_posMulReflectLT`

English:
theorem posMulMono_iff_posMulReflectLT
  statement: PosMulMono α ↔ PosMulReflectLT α
  proof: ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩

中文:
定理 posMulMono_iff_posMulReflectLT
  结论: PosMulMono α ↔ PosMulReflectLT α
  证明: ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩

Depends on / 依赖: PosMulMono, PosMulMono.toPosMulReflectLT, PosMulReflectLT, PosMulReflectLT.toPosMulMono, toPosMulMono, toPosMulReflectLT
-/
theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩

/--
theorem `mulPosMono_iff_mulPosReflectLT` / 定理 `mulPosMono_iff_mulPosReflectLT`

English:
theorem mulPosMono_iff_mulPosReflectLT
  statement: MulPosMono α ↔ MulPosReflectLT α
  proof: ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

中文:
定理 mulPosMono_iff_mulPosReflectLT
  结论: MulPosMono α ↔ MulPosReflectLT α
  证明: ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

Depends on / 依赖: MulPosMono, MulPosMono.toMulPosReflectLT, MulPosReflectLT, MulPosReflectLT.toMulPosMono, toMulPosMono, toMulPosReflectLT
-/
theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

end LinearOrder
