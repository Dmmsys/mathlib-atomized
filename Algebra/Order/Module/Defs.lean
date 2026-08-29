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

/--
Definition of `PosSMulMono` / `PosSMulMono` 的定义

English:
class PosSMulMono
  parameters: : Prop where
  axioms and operations (1):
    - smul_le_smul_of_nonneg_left(⦃a) : α⦄ (ha : 0 <= a) ⦃b₁ b₂ : β⦄ (hb : b₁ <= b₂) : a • b₁ <= a • b₂

中文:
类 PosSMulMono
  参数: : 命题 where
  公理与运算 (1 个):
    - smul_le_smul_of_nonneg_left(⦃a) : α⦄ (ha : 0 <= a) ⦃b₁ b₂ : β⦄ (hb : b₁ <= b₂) : a • b₁ <= a • b₂
-/
class PosSMulMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_left` instead. -/
  protected smul_le_smul_of_nonneg_left ⦃a : α⦄ (ha : 0 <= a) ⦃b₁ b₂ : β⦄ (hb : b₁ <= b₂) :
    a • b₁ <= a • b₂

/--
Definition of `PosSMulStrictMono` / `PosSMulStrictMono` 的定义

English:
class PosSMulStrictMono
  parameters: : Prop where
  axioms and operations (1):
    - smul_lt_smul_of_pos_left(⦃a) : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : b₁ < b₂) : a • b₁ < a • b₂

中文:
类 PosSMulStrictMono
  参数: : 命题 where
  公理与运算 (1 个):
    - smul_lt_smul_of_pos_left(⦃a) : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : b₁ < b₂) : a • b₁ < a • b₂
-/
class PosSMulStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_left` instead. -/
  protected smul_lt_smul_of_pos_left ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : b₁ < b₂) :
    a • b₁ < a • b₂

/--
Definition of `PosSMulReflectLT` / `PosSMulReflectLT` 的定义

English:
class PosSMulReflectLT
  parameters: : Prop where
  axioms and operations (1):
    - lt_of_smul_lt_smul_left(⦃a) : α⦄ (ha : 0 <= a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) : b₁ < b₂

中文:
类 PosSMulReflectLT
  参数: : 命题 where
  公理与运算 (1 个):
    - lt_of_smul_lt_smul_left(⦃a) : α⦄ (ha : 0 <= a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) : b₁ < b₂
-/
class PosSMulReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_left` instead. -/
  protected lt_of_smul_lt_smul_left ⦃a : α⦄ (ha : 0 <= a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) :
    b₁ < b₂

/--
Definition of `PosSMulReflectLE` / `PosSMulReflectLE` 的定义

English:
class PosSMulReflectLE
  parameters: : Prop where
  axioms and operations (1):
    - le_of_smul_le_smul_left(⦃a) : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ <= a • b₂) : b₁ <= b₂

中文:
类 PosSMulReflectLE
  参数: : 命题 where
  公理与运算 (1 个):
    - le_of_smul_le_smul_left(⦃a) : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ <= a • b₂) : b₁ <= b₂
-/
class PosSMulReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_le_smul_left` instead. -/
  protected le_of_smul_le_smul_left ⦃a : α⦄ (ha : 0 < a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ <= a • b₂) :
    b₁ <= b₂

end Left

section Right
variable [Zero β]

/--
Definition of `SMulPosMono` / `SMulPosMono` 的定义

English:
class SMulPosMono
  parameters: : Prop where
  axioms and operations (1):
    - smul_le_smul_of_nonneg_right(⦃b) : β⦄ (hb : 0 <= b) ⦃a₁ a₂ : α⦄ (ha : a₁ <= a₂) : a₁ • b <= a₂ • b

中文:
类 SMulPosMono
  参数: : 命题 where
  公理与运算 (1 个):
    - smul_le_smul_of_nonneg_right(⦃b) : β⦄ (hb : 0 <= b) ⦃a₁ a₂ : α⦄ (ha : a₁ <= a₂) : a₁ • b <= a₂ • b
-/
class SMulPosMono : Prop where
  /-- Do not use this. Use `smul_le_smul_of_nonneg_right` instead. -/
  protected smul_le_smul_of_nonneg_right ⦃b : β⦄ (hb : 0 <= b) ⦃a₁ a₂ : α⦄ (ha : a₁ <= a₂) :
    a₁ • b <= a₂ • b

/--
Definition of `SMulPosStrictMono` / `SMulPosStrictMono` 的定义

English:
class SMulPosStrictMono
  parameters: : Prop where
  axioms and operations (1):
    - smul_lt_smul_of_pos_right(⦃b) : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (ha : a₁ < a₂) : a₁ • b < a₂ • b

中文:
类 SMulPosStrictMono
  参数: : 命题 where
  公理与运算 (1 个):
    - smul_lt_smul_of_pos_right(⦃b) : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (ha : a₁ < a₂) : a₁ • b < a₂ • b
-/
class SMulPosStrictMono : Prop where
  /-- Do not use this. Use `smul_lt_smul_of_pos_right` instead. -/
  protected smul_lt_smul_of_pos_right ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (ha : a₁ < a₂) :
    a₁ • b < a₂ • b

/--
Definition of `SMulPosReflectLT` / `SMulPosReflectLT` 的定义

English:
class SMulPosReflectLT
  parameters: : Prop where
  axioms and operations (1):
    - lt_of_smul_lt_smul_right(⦃b) : β⦄ (hb : 0 <= b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b < a₂ • b) : a₁ < a₂

中文:
类 SMulPosReflectLT
  参数: : 命题 where
  公理与运算 (1 个):
    - lt_of_smul_lt_smul_right(⦃b) : β⦄ (hb : 0 <= b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b < a₂ • b) : a₁ < a₂
-/
class SMulPosReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_right` instead. -/
  protected lt_of_smul_lt_smul_right ⦃b : β⦄ (hb : 0 <= b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b < a₂ • b) :
    a₁ < a₂

/--
Definition of `SMulPosReflectLE` / `SMulPosReflectLE` 的定义

English:
class SMulPosReflectLE
  parameters: : Prop where
  axioms and operations (1):
    - le_of_smul_le_smul_right(⦃b) : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b <= a₂ • b) : a₁ <= a₂

中文:
类 SMulPosReflectLE
  参数: : 命题 where
  公理与运算 (1 个):
    - le_of_smul_le_smul_right(⦃b) : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b <= a₂ • b) : a₁ <= a₂
-/
class SMulPosReflectLE : Prop where
  /-- Do not use this. Use `le_of_smul_le_smul_right` instead. -/
  protected le_of_smul_le_smul_right ⦃b : β⦄ (hb : 0 < b) ⦃a₁ a₂ : α⦄ (hb : a₁ • b <= a₂ • b) :
    a₁ <= a₂

end Right

section LeftRight
variable [Zero α] [Zero β]

/--
Definition of `IsOrderedModule` / `IsOrderedModule` 的定义

English:
class IsOrderedModule
  parameters: extends PosSMulMono α β, SMulPosMono α β
  extends: PosSMulMono α β, SMulPosMono α β
  (no additional axioms)

中文:
类 IsOrderedModule
  参数: extends PosSMulMono α β, SMulPosMono α β
  继承: PosSMulMono α β, SMulPosMono α β
  (无附加公理)
-/
class IsOrderedModule extends PosSMulMono α β, SMulPosMono α β

/--
Definition of `IsStrictOrderedModule` / `IsStrictOrderedModule` 的定义

English:
class IsStrictOrderedModule
  parameters: extends PosSMulStrictMono α β, SMulPosStrictMono α β
  extends: PosSMulStrictMono α β, SMulPosStrictMono α β
  (no additional axioms)

中文:
类 IsStrictOrderedModule
  参数: extends PosSMulStrictMono α β, SMulPosStrictMono α β
  继承: PosSMulStrictMono α β, SMulPosStrictMono α β
  (无附加公理)
-/
class IsStrictOrderedModule extends PosSMulStrictMono α β, SMulPosStrictMono α β

end LeftRight
end Defs

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

section Mul
variable [Zero α] [Mul α] [Preorder α]

-- See note [lower instance priority]
instance (priority := 100) PosMulMono.toPosSMulMono [PosMulMono α] : PosSMulMono α α where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb := mul_le_mul_of_nonneg_left hb ha

-- See note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosSMulStrictMono [PosMulStrictMono α] :
    PosSMulStrictMono α α where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb := mul_lt_mul_of_pos_left hb ha

-- See note [lower instance priority]
instance (priority := 100) PosMulReflectLT.toPosSMulReflectLT [PosMulReflectLT α] :
    PosSMulReflectLT α α where
  lt_of_smul_lt_smul_left _a ha _b₁ _b₂ h := lt_of_mul_lt_mul_left h ha

-- See note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosSMulReflectLE [PosMulReflectLE α] :
    PosSMulReflectLE α α where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h := le_of_mul_le_mul_left h ha

-- See note [lower instance priority]
instance (priority := 100) MulPosMono.toSMulPosMono [MulPosMono α] : SMulPosMono α α where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := mul_le_mul_of_nonneg_right ha hb

-- See note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toSMulPosStrictMono [MulPosStrictMono α] :
    SMulPosStrictMono α α where
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := mul_lt_mul_of_pos_right ha hb

-- See note [lower instance priority]
instance (priority := 100) MulPosReflectLT.toSMulPosReflectLT [MulPosReflectLT α] :
    SMulPosReflectLT α α where
  lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h := lt_of_mul_lt_mul_right h hb

-- See note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toSMulPosReflectLE [MulPosReflectLE α] :
    SMulPosReflectLE α α where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h := le_of_mul_le_mul_right h hb

end Mul

instance {M : Type*} [PartialOrder M] [AddCommMonoid M] [IsOrderedAddMonoid M] :
    PosSMulMono Nat M where
  smul_le_smul_of_nonneg_left _n _ _a _b hab := nsmul_le_nsmul_right hab _

instance {M : Type*} [PartialOrder M] [AddCommMonoid M] [IsOrderedAddMonoid M] :
    SMulPosMono Nat M where
  smul_le_smul_of_nonneg_right _a ha _m _n hmn := nsmul_le_nsmul_left ha hmn

instance {M : Type*} [PartialOrder M] [AddCancelCommMonoid M] [IsOrderedAddMonoid M] :
    PosSMulStrictMono Nat M where
  smul_lt_smul_of_pos_left _n hn _m₁ _m₂ := nsmul_lt_nsmul_right hn.ne'

instance {M : Type*} [PartialOrder M] [AddCommMonoid M] [IsOrderedCancelAddMonoid M] :
    SMulPosStrictMono Nat M where
  smul_lt_smul_of_pos_right _a ha _m _n hmn := nsmul_lt_nsmul_left ha hmn

instance {G : Type*} [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] :
    PosSMulStrictMono Int G where
  smul_lt_smul_of_pos_left _n hn _m₁ _m₂ := zsmul_lt_zsmul_right hn

instance {G : Type*} [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] :
    SMulPosStrictMono Int G where
  smul_lt_smul_of_pos_right _a ha _m _n hmn := zsmul_lt_zsmul_left ha hmn

section SMul
variable [SMul α β]

section Preorder
variable [Preorder α] [Preorder β]

section Left
variable [Zero α]

/--
lemma `monotone_smul_left_of_nonneg` / 引理 `monotone_smul_left_of_nonneg`

English:
lemma monotone_smul_left_of_nonneg
  given: [PosSMulMono α β] (ha : 0 <= a)
  statement: Monotone ((a • ·) : β -> β)
  proof: PosSMulMono.smul_le_smul_of_nonneg_left ha

中文:
引理 monotone_smul_left_of_nonneg
  条件: [PosSMulMono α β] (ha : 0 <= a)
  结论: Monotone ((a • ·) : β -> β)
  证明: PosSMulMono.smul_le_smul_of_nonneg_left ha

Depends on / 依赖: PosSMulMono, PosSMulMono.smul_le_smul_of_nonneg_left, smul_le_smul_of_nonneg_left
-/
lemma monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β) :=
  PosSMulMono.smul_le_smul_of_nonneg_left ha

/--
lemma `strictMono_smul_left_of_pos` / 引理 `strictMono_smul_left_of_pos`

English:
lemma strictMono_smul_left_of_pos
  given: [PosSMulStrictMono α β] (ha : 0 < a)
  proof: PosSMulStrictMono.smul_lt_smul_of_pos_left ha

中文:
引理 strictMono_smul_left_of_pos
  条件: [PosSMulStrictMono α β] (ha : 0 < a)
  证明: PosSMulStrictMono.smul_lt_smul_of_pos_left ha

Depends on / 依赖: PosSMulStrictMono, PosSMulStrictMono.smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_left
-/
lemma strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) :
    StrictMono ((a • ·) : β -> β) := PosSMulStrictMono.smul_lt_smul_of_pos_left ha

/--
lemma `smul_le_smul_of_nonneg_left` / 引理 `smul_le_smul_of_nonneg_left`

English:
lemma smul_le_smul_of_nonneg_left
  given: [PosSMulMono α β] (hb : b₁ <= b₂) (ha : 0 <= a)
  proof: monotone_smul_left_of_nonneg ha hb

中文:
引理 smul_le_smul_of_nonneg_left
  条件: [PosSMulMono α β] (hb : b₁ <= b₂) (ha : 0 <= a)
  证明: monotone_smul_left_of_nonneg ha hb
-/
@[gcongr] lemma smul_le_smul_of_nonneg_left [PosSMulMono α β] (hb : b₁ <= b₂) (ha : 0 <= a) :
    a • b₁ <= a • b₂ := monotone_smul_left_of_nonneg ha hb

/--
lemma `smul_lt_smul_of_pos_left` / 引理 `smul_lt_smul_of_pos_left`

English:
lemma smul_lt_smul_of_pos_left
  given: [PosSMulStrictMono α β] (hb : b₁ < b₂) (ha : 0 < a)
  proof: strictMono_smul_left_of_pos ha hb

中文:
引理 smul_lt_smul_of_pos_left
  条件: [PosSMulStrictMono α β] (hb : b₁ < b₂) (ha : 0 < a)
  证明: strictMono_smul_left_of_pos ha hb
-/
@[gcongr] lemma smul_lt_smul_of_pos_left [PosSMulStrictMono α β] (hb : b₁ < b₂) (ha : 0 < a) :
    a • b₁ < a • b₂ := strictMono_smul_left_of_pos ha hb

/--
lemma `Monotone.const_smul` / 引理 `Monotone.const_smul`

English:
lemma Monotone.const_smul
  statement: [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
  proof: (monotone_smul_left_of_nonneg ha).comp hf

中文:
引理 Monotone.const_smul
  结论: [PosSMulMono α β] {γ : 类型} [Preorder γ] {f : γ -> β}
  证明: (monotone_smul_left_of_nonneg ha).comp hf

Depends on / 依赖: monotone_smul_left_of_nonneg
-/
lemma Monotone.const_smul [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
    (hf : Monotone f) (ha : 0 <= a) : Monotone fun x => a • f x :=
  (monotone_smul_left_of_nonneg ha).comp hf

/--
lemma `Antitone.const_smul` / 引理 `Antitone.const_smul`

English:
lemma Antitone.const_smul
  statement: [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
  proof: (monotone_smul_left_of_nonneg ha).comp_antitone hf

中文:
引理 Antitone.const_smul
  结论: [PosSMulMono α β] {γ : 类型} [Preorder γ] {f : γ -> β}
  证明: (monotone_smul_left_of_nonneg ha).comp_antitone hf

Depends on / 依赖: comp_antitone, monotone_smul_left_of_nonneg
-/
lemma Antitone.const_smul [PosSMulMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
    (hf : Antitone f) (ha : 0 <= a) : Antitone fun x => a • f x :=
  (monotone_smul_left_of_nonneg ha).comp_antitone hf

/--
lemma `StrictMono.const_smul` / 引理 `StrictMono.const_smul`

English:
lemma StrictMono.const_smul
  statement: [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
  proof: (strictMono_smul_left_of_pos ha).comp hf

中文:
引理 StrictMono.const_smul
  结论: [PosSMulStrictMono α β] {γ : 类型} [Preorder γ] {f : γ -> β}
  证明: (strictMono_smul_left_of_pos ha).comp hf

Depends on / 依赖: strictMono_smul_left_of_pos
-/
lemma StrictMono.const_smul [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
    (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x => a • f x :=
  (strictMono_smul_left_of_pos ha).comp hf

/--
lemma `StrictAnti.const_smul` / 引理 `StrictAnti.const_smul`

English:
lemma StrictAnti.const_smul
  statement: [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
  proof: (strictMono_smul_left_of_pos ha).comp_strictAnti hf

中文:
引理 StrictAnti.const_smul
  结论: [PosSMulStrictMono α β] {γ : 类型} [Preorder γ] {f : γ -> β}
  证明: (strictMono_smul_left_of_pos ha).comp_strictAnti hf

Depends on / 依赖: comp_strictAnti, strictMono_smul_left_of_pos
-/
lemma StrictAnti.const_smul [PosSMulStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> β}
    (hf : StrictAnti f) (ha : 0 < a) : StrictAnti fun x => a • f x :=
  (strictMono_smul_left_of_pos ha).comp_strictAnti hf

/--
lemma `lt_of_smul_lt_smul_left` / 引理 `lt_of_smul_lt_smul_left`

English:
lemma lt_of_smul_lt_smul_left
  given: [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : 0 <= a)
  statement: b₁ < b₂
  proof: PosSMulReflectLT.lt_of_smul_lt_smul_left ha h

中文:
引理 lt_of_smul_lt_smul_left
  条件: [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : 0 <= a)
  结论: b₁ < b₂
  证明: PosSMulReflectLT.lt_of_smul_lt_smul_left ha h

Depends on / 依赖: PosSMulReflectLT, PosSMulReflectLT.lt_of_smul_lt_smul_left, lt_of_smul_lt_smul_left
-/
lemma lt_of_smul_lt_smul_left [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂ :=
  PosSMulReflectLT.lt_of_smul_lt_smul_left ha h

/--
lemma `le_of_smul_le_smul_left` / 引理 `le_of_smul_le_smul_left`

English:
lemma le_of_smul_le_smul_left
  given: [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha : 0 < a)
  statement: b₁ <= b₂
  proof: PosSMulReflectLE.le_of_smul_le_smul_left ha h

alias lt_of_smul_lt_smul_of_nonneg_left := lt_of_smul_lt_smul_left
alias le_of_smul_le_smul_of_pos_left := le_of_smul_le_smul_left

@[simp]

中文:
引理 le_of_smul_le_smul_left
  条件: [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha : 0 < a)
  结论: b₁ <= b₂
  证明: PosSMulReflectLE.le_of_smul_le_smul_left ha h

alias lt_of_smul_lt_smul_of_nonneg_left := lt_of_smul_lt_smul_left
alias le_of_smul_le_smul_of_pos_left := le_of_smul_le_smul_left

@[simp]

Depends on / 依赖: PosSMulReflectLE, PosSMulReflectLE.le_of_smul_le_smul_left, le_of_smul_le_smul_left
-/
lemma le_of_smul_le_smul_left [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂ :=
  PosSMulReflectLE.le_of_smul_le_smul_left ha h

alias lt_of_smul_lt_smul_of_nonneg_left := lt_of_smul_lt_smul_left
alias le_of_smul_le_smul_of_pos_left := le_of_smul_le_smul_left

@[simp]
/--
lemma `smul_le_smul_iff_of_pos_left` / 引理 `smul_le_smul_iff_of_pos_left`

English:
lemma smul_le_smul_iff_of_pos_left
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  proof: ⟨fun h => le_of_smul_le_smul_left h ha, fun h => smul_le_smul_of_nonneg_left h ha.le⟩

@[simp]

中文:
引理 smul_le_smul_iff_of_pos_left
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  证明: ⟨fun h => le_of_smul_le_smul_left h ha, fun h => smul_le_smul_of_nonneg_left h ha.le⟩

@[simp]

Depends on / 依赖: ha.le, le_of_smul_le_smul_left, smul_le_smul_of_nonneg_left
-/
lemma smul_le_smul_iff_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a • b₁ <= a • b₂ ↔ b₁ <= b₂ :=
  ⟨fun h => le_of_smul_le_smul_left h ha, fun h => smul_le_smul_of_nonneg_left h ha.le⟩

@[simp]
/--
lemma `smul_lt_smul_iff_of_pos_left` / 引理 `smul_lt_smul_iff_of_pos_left`

English:
lemma smul_lt_smul_iff_of_pos_left
  given: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  proof: ⟨fun h => lt_of_smul_lt_smul_left h ha.le, fun hb => smul_lt_smul_of_pos_left hb ha⟩

中文:
引理 smul_lt_smul_iff_of_pos_left
  条件: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  证明: ⟨fun h => lt_of_smul_lt_smul_left h ha.le, fun hb => smul_lt_smul_of_pos_left hb ha⟩

Depends on / 依赖: ha.le, lt_of_smul_lt_smul_left, smul_lt_smul_of_pos_left
-/
lemma smul_lt_smul_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b₁ < a • b₂ ↔ b₁ < b₂ :=
  ⟨fun h => lt_of_smul_lt_smul_left h ha.le, fun hb => smul_lt_smul_of_pos_left hb ha⟩

end Left

section Right
variable [Zero β]

/--
lemma `monotone_smul_right_of_nonneg` / 引理 `monotone_smul_right_of_nonneg`

English:
lemma monotone_smul_right_of_nonneg
  given: [SMulPosMono α β] (hb : 0 <= b)
  statement: Monotone ((· • b) : α -> β)
  proof: SMulPosMono.smul_le_smul_of_nonneg_right hb

中文:
引理 monotone_smul_right_of_nonneg
  条件: [SMulPosMono α β] (hb : 0 <= b)
  结论: Monotone ((· • b) : α -> β)
  证明: SMulPosMono.smul_le_smul_of_nonneg_right hb

Depends on / 依赖: SMulPosMono, SMulPosMono.smul_le_smul_of_nonneg_right, smul_le_smul_of_nonneg_right
-/
lemma monotone_smul_right_of_nonneg [SMulPosMono α β] (hb : 0 <= b) : Monotone ((· • b) : α -> β) :=
  SMulPosMono.smul_le_smul_of_nonneg_right hb

/--
lemma `strictMono_smul_right_of_pos` / 引理 `strictMono_smul_right_of_pos`

English:
lemma strictMono_smul_right_of_pos
  given: [SMulPosStrictMono α β] (hb : 0 < b)
  proof: SMulPosStrictMono.smul_lt_smul_of_pos_right hb

中文:
引理 strictMono_smul_right_of_pos
  条件: [SMulPosStrictMono α β] (hb : 0 < b)
  证明: SMulPosStrictMono.smul_lt_smul_of_pos_right hb

Depends on / 依赖: SMulPosStrictMono, SMulPosStrictMono.smul_lt_smul_of_pos_right, smul_lt_smul_of_pos_right
-/
lemma strictMono_smul_right_of_pos [SMulPosStrictMono α β] (hb : 0 < b) :
    StrictMono ((· • b) : α -> β) := SMulPosStrictMono.smul_lt_smul_of_pos_right hb

/--
lemma `Monotone.smul_const` / 引理 `Monotone.smul_const`

English:
lemma Monotone.smul_const
  statement: [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
  proof: (monotone_smul_right_of_nonneg hb).comp hf

中文:
引理 Monotone.smul_const
  结论: [SMulPosMono α β] {γ : 类型} [Preorder γ] {f : γ -> α}
  证明: (monotone_smul_right_of_nonneg hb).comp hf

Depends on / 依赖: monotone_smul_right_of_nonneg
-/
lemma Monotone.smul_const [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
    (hf : Monotone f) (hb : 0 <= b) : Monotone fun x => f x • b :=
  (monotone_smul_right_of_nonneg hb).comp hf

/--
lemma `Antitone.smul_const` / 引理 `Antitone.smul_const`

English:
lemma Antitone.smul_const
  statement: [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
  proof: (monotone_smul_right_of_nonneg hb).comp_antitone hf

中文:
引理 Antitone.smul_const
  结论: [SMulPosMono α β] {γ : 类型} [Preorder γ] {f : γ -> α}
  证明: (monotone_smul_right_of_nonneg hb).comp_antitone hf

Depends on / 依赖: comp_antitone, monotone_smul_right_of_nonneg
-/
lemma Antitone.smul_const [SMulPosMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
    (hf : Antitone f) (hb : 0 <= b) : Antitone fun x => f x • b :=
  (monotone_smul_right_of_nonneg hb).comp_antitone hf

/--
lemma `StrictMono.smul_const` / 引理 `StrictMono.smul_const`

English:
lemma StrictMono.smul_const
  statement: [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
  proof: (strictMono_smul_right_of_pos hb).comp hf

中文:
引理 StrictMono.smul_const
  结论: [SMulPosStrictMono α β] {γ : 类型} [Preorder γ] {f : γ -> α}
  证明: (strictMono_smul_right_of_pos hb).comp hf

Depends on / 依赖: strictMono_smul_right_of_pos
-/
lemma StrictMono.smul_const [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
    (hf : StrictMono f) (hb : 0 < b) : StrictMono fun x => f x • b :=
  (strictMono_smul_right_of_pos hb).comp hf

/--
lemma `StrictAnti.smul_const` / 引理 `StrictAnti.smul_const`

English:
lemma StrictAnti.smul_const
  statement: [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
  proof: (strictMono_smul_right_of_pos hb).comp_strictAnti hf

中文:
引理 StrictAnti.smul_const
  结论: [SMulPosStrictMono α β] {γ : 类型} [Preorder γ] {f : γ -> α}
  证明: (strictMono_smul_right_of_pos hb).comp_strictAnti hf

Depends on / 依赖: comp_strictAnti, strictMono_smul_right_of_pos
-/
lemma StrictAnti.smul_const [SMulPosStrictMono α β] {γ : Type*} [Preorder γ] {f : γ -> α}
    (hf : StrictAnti f) (hb : 0 < b) : StrictAnti fun x => f x • b :=
  (strictMono_smul_right_of_pos hb).comp_strictAnti hf

/--
lemma `smul_le_smul_of_nonneg_right` / 引理 `smul_le_smul_of_nonneg_right`

English:
lemma smul_le_smul_of_nonneg_right
  given: [SMulPosMono α β] (ha : a₁ <= a₂) (hb : 0 <= b)
  proof: monotone_smul_right_of_nonneg hb ha

中文:
引理 smul_le_smul_of_nonneg_right
  条件: [SMulPosMono α β] (ha : a₁ <= a₂) (hb : 0 <= b)
  证明: monotone_smul_right_of_nonneg hb ha
-/
@[gcongr] lemma smul_le_smul_of_nonneg_right [SMulPosMono α β] (ha : a₁ <= a₂) (hb : 0 <= b) :
    a₁ • b <= a₂ • b := monotone_smul_right_of_nonneg hb ha

variable (β) in
@[gcongr, mono]
/--
lemma `smul_one_mono` / 引理 `smul_one_mono`

English:
lemma smul_one_mono
  given: [One β] [ZeroLEOneClass β] [SMulPosMono α β]
  proof: fun _ _ ha => smul_le_smul_of_nonneg_right ha zero_le_one

中文:
引理 smul_one_mono
  条件: [One β] [ZeroLEOneClass β] [SMulPosMono α β]
  证明: fun _ _ ha => smul_le_smul_of_nonneg_right ha zero_le_one

Depends on / 依赖: smul_le_smul_of_nonneg_right, zero_le_one
-/
lemma smul_one_mono [One β] [ZeroLEOneClass β] [SMulPosMono α β] :
    Monotone (fun x : α => x • (1 : β)) :=
  fun _ _ ha => smul_le_smul_of_nonneg_right ha zero_le_one

/--
lemma `smul_lt_smul_of_pos_right` / 引理 `smul_lt_smul_of_pos_right`

English:
lemma smul_lt_smul_of_pos_right
  given: [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : 0 < b)
  proof: strictMono_smul_right_of_pos hb ha

中文:
引理 smul_lt_smul_of_pos_right
  条件: [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : 0 < b)
  证明: strictMono_smul_right_of_pos hb ha
-/
@[gcongr] lemma smul_lt_smul_of_pos_right [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : 0 < b) :
    a₁ • b < a₂ • b := strictMono_smul_right_of_pos hb ha

/--
lemma `lt_of_smul_lt_smul_right` / 引理 `lt_of_smul_lt_smul_right`

English:
lemma lt_of_smul_lt_smul_right
  given: [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 <= b)
  proof: SMulPosReflectLT.lt_of_smul_lt_smul_right hb h

中文:
引理 lt_of_smul_lt_smul_right
  条件: [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 <= b)
  证明: SMulPosReflectLT.lt_of_smul_lt_smul_right hb h

Depends on / 依赖: SMulPosReflectLT, SMulPosReflectLT.lt_of_smul_lt_smul_right, lt_of_smul_lt_smul_right
-/
lemma lt_of_smul_lt_smul_right [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 <= b) :
    a₁ < a₂ := SMulPosReflectLT.lt_of_smul_lt_smul_right hb h

/--
lemma `le_of_smul_le_smul_right` / 引理 `le_of_smul_le_smul_right`

English:
lemma le_of_smul_le_smul_right
  given: [SMulPosReflectLE α β] (h : a₁ • b <= a₂ • b) (hb : 0 < b)
  proof: SMulPosReflectLE.le_of_smul_le_smul_right hb h

alias lt_of_smul_lt_smul_of_nonneg_right := lt_of_smul_lt_smul_right
alias le_of_smul_le_smul_of_pos_right := le_of_smul_le_smul_right

@[simp]

中文:
引理 le_of_smul_le_smul_right
  条件: [SMulPosReflectLE α β] (h : a₁ • b <= a₂ • b) (hb : 0 < b)
  证明: SMulPosReflectLE.le_of_smul_le_smul_right hb h

alias lt_of_smul_lt_smul_of_nonneg_right := lt_of_smul_lt_smul_right
alias le_of_smul_le_smul_of_pos_right := le_of_smul_le_smul_right

@[simp]

Depends on / 依赖: SMulPosReflectLE, SMulPosReflectLE.le_of_smul_le_smul_right, le_of_smul_le_smul_right
-/
lemma le_of_smul_le_smul_right [SMulPosReflectLE α β] (h : a₁ • b <= a₂ • b) (hb : 0 < b) :
    a₁ <= a₂ := SMulPosReflectLE.le_of_smul_le_smul_right hb h

alias lt_of_smul_lt_smul_of_nonneg_right := lt_of_smul_lt_smul_right
alias le_of_smul_le_smul_of_pos_right := le_of_smul_le_smul_right

@[simp]
/--
lemma `smul_le_smul_iff_of_pos_right` / 引理 `smul_le_smul_iff_of_pos_right`

English:
lemma smul_le_smul_iff_of_pos_right
  given: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  proof: ⟨fun h => le_of_smul_le_smul_right h hb, fun ha => smul_le_smul_of_nonneg_right ha hb.le⟩

@[simp]

中文:
引理 smul_le_smul_iff_of_pos_right
  条件: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  证明: ⟨fun h => le_of_smul_le_smul_right h hb, fun ha => smul_le_smul_of_nonneg_right ha hb.le⟩

@[simp]

Depends on / 依赖: hb.le, le_of_smul_le_smul_right, smul_le_smul_of_nonneg_right
-/
lemma smul_le_smul_iff_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a₁ • b <= a₂ • b ↔ a₁ <= a₂ :=
  ⟨fun h => le_of_smul_le_smul_right h hb, fun ha => smul_le_smul_of_nonneg_right ha hb.le⟩

@[simp]
/--
lemma `smul_lt_smul_iff_of_pos_right` / 引理 `smul_lt_smul_iff_of_pos_right`

English:
lemma smul_lt_smul_iff_of_pos_right
  given: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  proof: ⟨fun h => lt_of_smul_lt_smul_right h hb.le, fun ha => smul_lt_smul_of_pos_right ha hb⟩

中文:
引理 smul_lt_smul_iff_of_pos_right
  条件: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  证明: ⟨fun h => lt_of_smul_lt_smul_right h hb.le, fun ha => smul_lt_smul_of_pos_right ha hb⟩

Depends on / 依赖: hb.le, lt_of_smul_lt_smul_right, smul_lt_smul_of_pos_right
-/
lemma smul_lt_smul_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    a₁ • b < a₂ • b ↔ a₁ < a₂ :=
  ⟨fun h => lt_of_smul_lt_smul_right h hb.le, fun ha => smul_lt_smul_of_pos_right ha hb⟩

end Right

section LeftRight
variable [Zero α] [Zero β]

/--
lemma `smul_lt_smul_of_le_of_lt` / 引理 `smul_lt_smul_of_le_of_lt`

English:
lemma smul_lt_smul_of_le_of_lt
  statement: [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ <= a₂)
  proof: (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂)

中文:
引理 smul_lt_smul_of_le_of_lt
  结论: [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ <= a₂)
  证明: (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂)

Depends on / 依赖: smul_le_smul_of_nonneg_right, smul_lt_smul_of_pos_left, trans_le
-/
lemma smul_lt_smul_of_le_of_lt [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ <= a₂)
    (hb : b₁ < b₂) (h₁ : 0 < a₁) (h₂ : 0 <= b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂)

/--
lemma `smul_lt_smul_of_le_of_lt'` / 引理 `smul_lt_smul_of_le_of_lt'`

English:
lemma smul_lt_smul_of_le_of_lt'
  statement: [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ <= a₂)
  proof: (smul_le_smul_of_nonneg_right ha h₁).trans_lt (smul_lt_smul_of_pos_left hb h₂)

中文:
引理 smul_lt_smul_of_le_of_lt'
  结论: [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ <= a₂)
  证明: (smul_le_smul_of_nonneg_right ha h₁).trans_lt (smul_lt_smul_of_pos_left hb h₂)

Depends on / 依赖: smul_le_smul_of_nonneg_right, smul_lt_smul_of_pos_left, trans_lt
-/
lemma smul_lt_smul_of_le_of_lt' [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ <= a₂)
    (hb : b₁ < b₂) (h₂ : 0 < a₂) (h₁ : 0 <= b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans_lt (smul_lt_smul_of_pos_left hb h₂)

/--
lemma `smul_lt_smul_of_lt_of_le` / 引理 `smul_lt_smul_of_lt_of_le`

English:
lemma smul_lt_smul_of_lt_of_le
  statement: [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
  proof: (smul_le_smul_of_nonneg_left hb h₁).trans_lt (smul_lt_smul_of_pos_right ha h₂)

中文:
引理 smul_lt_smul_of_lt_of_le
  结论: [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
  证明: (smul_le_smul_of_nonneg_left hb h₁).trans_lt (smul_lt_smul_of_pos_right ha h₂)

Depends on / 依赖: smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_right, trans_lt
-/
lemma smul_lt_smul_of_lt_of_le [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ <= b₂) (h₁ : 0 <= a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_le_smul_of_nonneg_left hb h₁).trans_lt (smul_lt_smul_of_pos_right ha h₂)

/--
lemma `smul_lt_smul_of_lt_of_le'` / 引理 `smul_lt_smul_of_lt_of_le'`

English:
lemma smul_lt_smul_of_lt_of_le'
  statement: [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
  proof: (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂)

中文:
引理 smul_lt_smul_of_lt_of_le'
  结论: [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
  证明: (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂)

Depends on / 依赖: smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_right, trans_le
-/
lemma smul_lt_smul_of_lt_of_le' [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ <= b₂) (h₂ : 0 <= a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂)

/--
lemma `smul_lt_smul` / 引理 `smul_lt_smul`

English:
lemma smul_lt_smul
  statement: [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
  proof: (smul_lt_smul_of_pos_left hb h₁).trans (smul_lt_smul_of_pos_right ha h₂)

中文:
引理 smul_lt_smul
  结论: [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
  证明: (smul_lt_smul_of_pos_left hb h₁).trans (smul_lt_smul_of_pos_right ha h₂)

Depends on / 依赖: smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_right
-/
lemma smul_lt_smul [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
    (h₁ : 0 < a₁) (h₂ : 0 < b₂) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_left hb h₁).trans (smul_lt_smul_of_pos_right ha h₂)

/--
lemma `smul_lt_smul'` / 引理 `smul_lt_smul'`

English:
lemma smul_lt_smul'
  statement: [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
  proof: (smul_lt_smul_of_pos_right ha h₁).trans (smul_lt_smul_of_pos_left hb h₂)

中文:
引理 smul_lt_smul'
  结论: [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
  证明: (smul_lt_smul_of_pos_right ha h₁).trans (smul_lt_smul_of_pos_left hb h₂)

Depends on / 依赖: smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_right
-/
lemma smul_lt_smul' [PosSMulStrictMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂) (hb : b₁ < b₂)
    (h₂ : 0 < a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ :=
  (smul_lt_smul_of_pos_right ha h₁).trans (smul_lt_smul_of_pos_left hb h₂)

/--
lemma `smul_le_smul` / 引理 `smul_le_smul`

English:
lemma smul_le_smul
  statement: [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂)
  proof: (smul_le_smul_of_nonneg_left hb h₁).trans (smul_le_smul_of_nonneg_right ha h₂)

中文:
引理 smul_le_smul
  结论: [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂)
  证明: (smul_le_smul_of_nonneg_left hb h₁).trans (smul_le_smul_of_nonneg_right ha h₂)

Depends on / 依赖: smul_le_smul_of_nonneg_left, smul_le_smul_of_nonneg_right
-/
lemma smul_le_smul [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂)
    (h₁ : 0 <= a₁) (h₂ : 0 <= b₂) : a₁ • b₁ <= a₂ • b₂ :=
  (smul_le_smul_of_nonneg_left hb h₁).trans (smul_le_smul_of_nonneg_right ha h₂)

/--
lemma `smul_le_smul'` / 引理 `smul_le_smul'`

English:
lemma smul_le_smul'
  statement: [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₂ : 0 <= a₂)
  proof: (smul_le_smul_of_nonneg_right ha h₁).trans (smul_le_smul_of_nonneg_left hb h₂)

中文:
引理 smul_le_smul'
  结论: [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₂ : 0 <= a₂)
  证明: (smul_le_smul_of_nonneg_right ha h₁).trans (smul_le_smul_of_nonneg_left hb h₂)

Depends on / 依赖: smul_le_smul_of_nonneg_left, smul_le_smul_of_nonneg_right
-/
lemma smul_le_smul' [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₂ : 0 <= a₂)
    (h₁ : 0 <= b₁) : a₁ • b₁ <= a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans (smul_le_smul_of_nonneg_left hb h₂)

end LeftRight
end Preorder

variable (β) in
@[gcongr, mono]
/--
lemma `smul_one_strictMono` / 引理 `smul_one_strictMono`

English:
lemma smul_one_strictMono
  statement: [Preorder α] [PartialOrder β] [Zero β] [One β] [ZeroLEOneClass β]
  proof: fun _ _ ha => smul_lt_smul_of_pos_right ha (zero_lt_one (α := β))

中文:
引理 smul_one_strictMono
  结论: [Preorder α] [PartialOrder β] [Zero β] [One β] [ZeroLEOneClass β]
  证明: fun _ _ ha => smul_lt_smul_of_pos_right ha (zero_lt_one (α := β))

Depends on / 依赖: smul_lt_smul_of_pos_right, zero_lt_one
-/
lemma smul_one_strictMono [Preorder α] [PartialOrder β] [Zero β] [One β] [ZeroLEOneClass β]
    [NeZero (1 : β)] [SMulPosStrictMono α β] :
    StrictMono (fun x : α => x • (1 : β)) :=
  fun _ _ ha => smul_lt_smul_of_pos_right ha (zero_lt_one (α := β))

section PartialOrder
variable [Semiring α] [PartialOrder α]

-- See note [lower instance priority]
instance (priority := 100) IsOrderedRing.toIsOrderedModule [IsOrderedRing α] :
    IsOrderedModule α α where

-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toIsStrictOrderedModule [IsStrictOrderedRing α] :
    IsStrictOrderedModule α α where

end PartialOrder

section LinearOrder
variable [Preorder α] [LinearOrder β]

section Left
variable [Zero α]

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLE [PosSMulStrictMono α β] :
    PosSMulReflectLE α β where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ := (strictMono_smul_left_of_pos ha).le_iff_le.1

/--
lemma `PosSMulReflectLE.toPosSMulStrictMono` / 引理 `PosSMulReflectLE.toPosSMulStrictMono`

English:
lemma PosSMulReflectLE.toPosSMulStrictMono
  given: [PosSMulReflectLE α β]
  statement: PosSMulStrictMono α β where
  proof: not_le.1 fun h => hb.not_ge le_of_smul_le_smul_left h ha

中文:
引理 PosSMulReflectLE.toPosSMulStrictMono
  条件: [PosSMulReflectLE α β]
  结论: PosSMulStrictMono α β where
  证明: not_le.1 fun h => hb.not_ge le_of_smul_le_smul_left h ha

Depends on / 依赖: hb.not_ge, le_of_smul_le_smul_left, not_ge, not_le
-/
lemma PosSMulReflectLE.toPosSMulStrictMono [PosSMulReflectLE α β] : PosSMulStrictMono α β where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb :=
not_le.1 fun h => hb.not_ge le_of_smul_le_smul_left h ha

/--
lemma `posSMulStrictMono_iff_PosSMulReflectLE` / 引理 `posSMulStrictMono_iff_PosSMulReflectLE`

English:
lemma posSMulStrictMono_iff_PosSMulReflectLE
  statement: PosSMulStrictMono α β ↔ PosSMulReflectLE α β
  proof: ⟨fun _ => inferInstance, fun _ => PosSMulReflectLE.toPosSMulStrictMono⟩

中文:
引理 posSMulStrictMono_iff_PosSMulReflectLE
  结论: PosSMulStrictMono α β ↔ PosSMulReflectLE α β
  证明: ⟨fun _ => inferInstance, fun _ => PosSMulReflectLE.toPosSMulStrictMono⟩

Depends on / 依赖: PosSMulReflectLE, PosSMulReflectLE.toPosSMulStrictMono, toPosSMulStrictMono
-/
lemma posSMulStrictMono_iff_PosSMulReflectLE : PosSMulStrictMono α β ↔ PosSMulReflectLE α β :=
  ⟨fun _ => inferInstance, fun _ => PosSMulReflectLE.toPosSMulStrictMono⟩

/--
Instance `PosSMulMono.toPosSMulReflectLT` / 实例 `PosSMulMono.toPosSMulReflectLT`

English:
instance PosSMulMono.toPosSMulReflectLT
  signature: [PosSMulMono α β]
  body: (monotone_smul_left_of_nonneg ha).reflect_lt

中文:
实例 PosSMulMono.toPosSMulReflectLT
  签名: [PosSMulMono α β]
  定义体: (monotone_smul_left_of_nonneg ha).reflect_lt

Depends on / 依赖: monotone_smul_left_of_nonneg, reflect_lt
-/
instance PosSMulMono.toPosSMulReflectLT [PosSMulMono α β] : PosSMulReflectLT α β where
  lt_of_smul_lt_smul_left _a ha _b₁ _b₂ := (monotone_smul_left_of_nonneg ha).reflect_lt

/--
lemma `PosSMulReflectLT.toPosSMulMono` / 引理 `PosSMulReflectLT.toPosSMulMono`

English:
lemma PosSMulReflectLT.toPosSMulMono
  given: [PosSMulReflectLT α β]
  statement: PosSMulMono α β where
  proof: not_lt.1 fun h => hb.not_gt lt_of_smul_lt_smul_left h ha

中文:
引理 PosSMulReflectLT.toPosSMulMono
  条件: [PosSMulReflectLT α β]
  结论: PosSMulMono α β where
  证明: not_lt.1 fun h => hb.not_gt lt_of_smul_lt_smul_left h ha

Depends on / 依赖: hb.not_gt, lt_of_smul_lt_smul_left, not_gt, not_lt
-/
lemma PosSMulReflectLT.toPosSMulMono [PosSMulReflectLT α β] : PosSMulMono α β where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb :=
not_lt.1 fun h => hb.not_gt lt_of_smul_lt_smul_left h ha

/--
lemma `posSMulMono_iff_posSMulReflectLT` / 引理 `posSMulMono_iff_posSMulReflectLT`

English:
lemma posSMulMono_iff_posSMulReflectLT
  statement: PosSMulMono α β ↔ PosSMulReflectLT α β
  proof: ⟨fun _ => PosSMulMono.toPosSMulReflectLT, fun _ => PosSMulReflectLT.toPosSMulMono⟩

中文:
引理 posSMulMono_iff_posSMulReflectLT
  结论: PosSMulMono α β ↔ PosSMulReflectLT α β
  证明: ⟨fun _ => PosSMulMono.toPosSMulReflectLT, fun _ => PosSMulReflectLT.toPosSMulMono⟩

Depends on / 依赖: PosSMulMono, PosSMulMono.toPosSMulReflectLT, PosSMulReflectLT, PosSMulReflectLT.toPosSMulMono, toPosSMulMono, toPosSMulReflectLT
-/
lemma posSMulMono_iff_posSMulReflectLT : PosSMulMono α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ => PosSMulMono.toPosSMulReflectLT, fun _ => PosSMulReflectLT.toPosSMulMono⟩

/--
lemma `smul_max_of_nonneg` / 引理 `smul_max_of_nonneg`

English:
lemma smul_max_of_nonneg
  given: [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β)
  proof: (monotone_smul_left_of_nonneg ha).map_max

中文:
引理 smul_max_of_nonneg
  条件: [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β)
  证明: (monotone_smul_left_of_nonneg ha).map_max

Depends on / 依赖: map_max, monotone_smul_left_of_nonneg
-/
lemma smul_max_of_nonneg [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β) :
    a • max b₁ b₂ = max (a • b₁) (a • b₂) := (monotone_smul_left_of_nonneg ha).map_max

/--
lemma `smul_min_of_nonneg` / 引理 `smul_min_of_nonneg`

English:
lemma smul_min_of_nonneg
  given: [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β)
  proof: (monotone_smul_left_of_nonneg ha).map_min

中文:
引理 smul_min_of_nonneg
  条件: [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β)
  证明: (monotone_smul_left_of_nonneg ha).map_min

Depends on / 依赖: map_min, monotone_smul_left_of_nonneg
-/
lemma smul_min_of_nonneg [PosSMulMono α β] (ha : 0 <= a) (b₁ b₂ : β) :
    a • min b₁ b₂ = min (a • b₁) (a • b₂) := (monotone_smul_left_of_nonneg ha).map_min

end Left

section Right
variable [Zero β]

/--
lemma `SMulPosReflectLE.toSMulPosStrictMono` / 引理 `SMulPosReflectLE.toSMulPosStrictMono`

English:
lemma SMulPosReflectLE.toSMulPosStrictMono
  given: [SMulPosReflectLE α β]
  statement: SMulPosStrictMono α β where
  proof: not_le.1 fun h => ha.not_ge le_of_smul_le_smul_of_pos_right h hb

中文:
引理 SMulPosReflectLE.toSMulPosStrictMono
  条件: [SMulPosReflectLE α β]
  结论: SMulPosStrictMono α β where
  证明: not_le.1 fun h => ha.not_ge le_of_smul_le_smul_of_pos_right h hb

Depends on / 依赖: ha.not_ge, le_of_smul_le_smul_of_pos_right, not_ge, not_le
-/
lemma SMulPosReflectLE.toSMulPosStrictMono [SMulPosReflectLE α β] : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha :=
not_le.1 fun h => ha.not_ge le_of_smul_le_smul_of_pos_right h hb

/--
lemma `SMulPosReflectLT.toSMulPosMono` / 引理 `SMulPosReflectLT.toSMulPosMono`

English:
lemma SMulPosReflectLT.toSMulPosMono
  given: [SMulPosReflectLT α β]
  statement: SMulPosMono α β where
  proof: not_lt.1 fun h => ha.not_gt lt_of_smul_lt_smul_right h hb

中文:
引理 SMulPosReflectLT.toSMulPosMono
  条件: [SMulPosReflectLT α β]
  结论: SMulPosMono α β where
  证明: not_lt.1 fun h => ha.not_gt lt_of_smul_lt_smul_right h hb

Depends on / 依赖: ha.not_gt, lt_of_smul_lt_smul_right, not_gt, not_lt
-/
lemma SMulPosReflectLT.toSMulPosMono [SMulPosReflectLT α β] : SMulPosMono α β where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha :=
not_lt.1 fun h => ha.not_gt lt_of_smul_lt_smul_right h hb

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [Preorder β]

section Right
variable [Zero β]

-- See note [lower instance priority]
instance (priority := 100) SMulPosStrictMono.toSMulPosReflectLE [SMulPosStrictMono α β] :
    SMulPosReflectLE α β where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h :=
not_lt.1 fun ha => h.not_gt smul_lt_smul_of_pos_right ha hb

/--
lemma `SMulPosMono.toSMulPosReflectLT` / 引理 `SMulPosMono.toSMulPosReflectLT`

English:
lemma SMulPosMono.toSMulPosReflectLT
  given: [SMulPosMono α β]
  statement: SMulPosReflectLT α β where
  proof: not_le.1 fun ha => h.not_ge smul_le_smul_of_nonneg_right ha hb

中文:
引理 SMulPosMono.toSMulPosReflectLT
  条件: [SMulPosMono α β]
  结论: SMulPosReflectLT α β where
  证明: not_le.1 fun ha => h.not_ge smul_le_smul_of_nonneg_right ha hb

Depends on / 依赖: h.not_ge, not_ge, not_le, smul_le_smul_of_nonneg_right
-/
lemma SMulPosMono.toSMulPosReflectLT [SMulPosMono α β] : SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h :=
not_le.1 fun ha => h.not_ge smul_le_smul_of_nonneg_right ha hb

end Right
end LinearOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

section Right
variable [Zero β]

/--
lemma `smulPosStrictMono_iff_SMulPosReflectLE` / 引理 `smulPosStrictMono_iff_SMulPosReflectLE`

English:
lemma smulPosStrictMono_iff_SMulPosReflectLE
  statement: SMulPosStrictMono α β ↔ SMulPosReflectLE α β
  proof: ⟨fun _ => SMulPosStrictMono.toSMulPosReflectLE, fun _ => SMulPosReflectLE.toSMulPosStrictMono⟩

中文:
引理 smulPosStrictMono_iff_SMulPosReflectLE
  结论: SMulPosStrictMono α β ↔ SMulPosReflectLE α β
  证明: ⟨fun _ => SMulPosStrictMono.toSMulPosReflectLE, fun _ => SMulPosReflectLE.toSMulPosStrictMono⟩

Depends on / 依赖: SMulPosReflectLE, SMulPosReflectLE.toSMulPosStrictMono, SMulPosStrictMono, SMulPosStrictMono.toSMulPosReflectLE, toSMulPosReflectLE, toSMulPosStrictMono
-/
lemma smulPosStrictMono_iff_SMulPosReflectLE : SMulPosStrictMono α β ↔ SMulPosReflectLE α β :=
  ⟨fun _ => SMulPosStrictMono.toSMulPosReflectLE, fun _ => SMulPosReflectLE.toSMulPosStrictMono⟩

/--
lemma `smulPosMono_iff_smulPosReflectLT` / 引理 `smulPosMono_iff_smulPosReflectLT`

English:
lemma smulPosMono_iff_smulPosReflectLT
  statement: SMulPosMono α β ↔ SMulPosReflectLT α β
  proof: ⟨fun _ => SMulPosMono.toSMulPosReflectLT, fun _ => SMulPosReflectLT.toSMulPosMono⟩

中文:
引理 smulPosMono_iff_smulPosReflectLT
  结论: SMulPosMono α β ↔ SMulPosReflectLT α β
  证明: ⟨fun _ => SMulPosMono.toSMulPosReflectLT, fun _ => SMulPosReflectLT.toSMulPosMono⟩

Depends on / 依赖: SMulPosMono, SMulPosMono.toSMulPosReflectLT, SMulPosReflectLT, SMulPosReflectLT.toSMulPosMono, toSMulPosMono, toSMulPosReflectLT
-/
lemma smulPosMono_iff_smulPosReflectLT : SMulPosMono α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ => SMulPosMono.toSMulPosReflectLT, fun _ => SMulPosReflectLT.toSMulPosMono⟩

end Right
end LinearOrder
end SMul

section SMulZeroClass
variable [Zero α] [Zero β] [SMulZeroClass α β]

section Preorder
variable [Preorder α] [Preorder β]

/--
lemma `smul_pos` / 引理 `smul_pos`

English:
lemma smul_pos
  given: [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a • b
  proof: by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

中文:
引理 smul_pos
  条件: [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a • b
  证明: by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

Depends on / 依赖: smul_lt_smul_of_pos_left, smul_zero
-/
lemma smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

/--
lemma `smul_neg_of_pos_of_neg` / 引理 `smul_neg_of_pos_of_neg`

English:
lemma smul_neg_of_pos_of_neg
  given: [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0)
  statement: a • b < 0
  proof: by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

@[simp]

中文:
引理 smul_neg_of_pos_of_neg
  条件: [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0)
  结论: a • b < 0
  证明: by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

@[simp]

Depends on / 依赖: smul_lt_smul_of_pos_left, smul_zero
-/
lemma smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0) : a • b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

@[simp]
/--
lemma `smul_pos_iff_of_pos_left` / 引理 `smul_pos_iff_of_pos_left`

English:
lemma smul_pos_iff_of_pos_left
  given: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  proof: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₁ := 0) (b₂ := b)

中文:
引理 smul_pos_iff_of_pos_left
  条件: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  证明: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₁ := 0) (b₂ := b)

Depends on / 依赖: smul_lt_smul_iff_of_pos_left, smul_zero
-/
lemma smul_pos_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    0 < a • b ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₁ := 0) (b₂ := b)

/--
lemma `smul_neg_iff_of_pos_left` / 引理 `smul_neg_iff_of_pos_left`

English:
lemma smul_neg_iff_of_pos_left
  given: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  proof: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₂ := (0 : β))

中文:
引理 smul_neg_iff_of_pos_left
  条件: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  证明: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₂ := (0 : β))

Depends on / 依赖: smul_lt_smul_iff_of_pos_left, smul_zero
-/
lemma smul_neg_iff_of_pos_left [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a • b < 0 ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_pos_left ha (b₂ := (0 : β))

/--
lemma `smul_nonneg` / 引理 `smul_nonneg`

English:
lemma smul_nonneg
  given: [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁)
  statement: 0 <= a • b₁
  proof: by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

中文:
引理 smul_nonneg
  条件: [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁)
  结论: 0 <= a • b₁
  证明: by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

Depends on / 依赖: smul_le_smul_of_nonneg_left, smul_zero
-/
lemma smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) : 0 <= a • b₁ := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

/--
lemma `smul_nonpos_of_nonneg_of_nonpos` / 引理 `smul_nonpos_of_nonneg_of_nonpos`

English:
lemma smul_nonpos_of_nonneg_of_nonpos
  given: [PosSMulMono α β] (ha : 0 <= a) (hb : b <= 0)
  statement: a • b <= 0
  proof: by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

中文:
引理 smul_nonpos_of_nonneg_of_nonpos
  条件: [PosSMulMono α β] (ha : 0 <= a) (hb : b <= 0)
  结论: a • b <= 0
  证明: by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

Depends on / 依赖: smul_le_smul_of_nonneg_left, smul_zero
-/
lemma smul_nonpos_of_nonneg_of_nonpos [PosSMulMono α β] (ha : 0 <= a) (hb : b <= 0) : a • b <= 0 := by
  simpa only [smul_zero] using smul_le_smul_of_nonneg_left hb ha

/--
lemma `pos_of_smul_pos_left` / 引理 `pos_of_smul_pos_left`

English:
lemma pos_of_smul_pos_left
  given: [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 <= a)
  statement: 0 < b
  proof: lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

中文:
引理 pos_of_smul_pos_left
  条件: [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 <= a)
  结论: 0 < b
  证明: lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

Depends on / 依赖: lt_of_smul_lt_smul_left, smul_zero
-/
lemma pos_of_smul_pos_left [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 <= a) : 0 < b :=
  lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

/--
lemma `neg_of_smul_neg_left` / 引理 `neg_of_smul_neg_left`

English:
lemma neg_of_smul_neg_left
  given: [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 <= a)
  statement: b < 0
  proof: lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

中文:
引理 neg_of_smul_neg_left
  条件: [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 <= a)
  结论: b < 0
  证明: lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

Depends on / 依赖: lt_of_smul_lt_smul_left, smul_zero
-/
lemma neg_of_smul_neg_left [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 <= a) : b < 0 :=
  lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

/--
lemma `nonneg_of_smul_nonneg_of_pos_left` / 引理 `nonneg_of_smul_nonneg_of_pos_left`

English:
lemma nonneg_of_smul_nonneg_of_pos_left
  given: [PosSMulReflectLE α β] (h : 0 <= a • b) (ha : 0 < a)
  proof: le_of_smul_le_smul_of_pos_left (by simpa) ha

中文:
引理 nonneg_of_smul_nonneg_of_pos_left
  条件: [PosSMulReflectLE α β] (h : 0 <= a • b) (ha : 0 < a)
  证明: le_of_smul_le_smul_of_pos_left (by simpa) ha

Depends on / 依赖: le_of_smul_le_smul_of_pos_left
-/
lemma nonneg_of_smul_nonneg_of_pos_left [PosSMulReflectLE α β] (h : 0 <= a • b) (ha : 0 < a) :
    0 <= b :=
  le_of_smul_le_smul_of_pos_left (by simpa) ha

/--
lemma `nonpos_of_smul_nonpos_of_pos_left` / 引理 `nonpos_of_smul_nonpos_of_pos_left`

English:
lemma nonpos_of_smul_nonpos_of_pos_left
  given: [PosSMulReflectLE α β] (h : a • b <= 0) (ha : 0 < a)
  proof: le_of_smul_le_smul_of_pos_left (by simpa) ha

中文:
引理 nonpos_of_smul_nonpos_of_pos_left
  条件: [PosSMulReflectLE α β] (h : a • b <= 0) (ha : 0 < a)
  证明: le_of_smul_le_smul_of_pos_left (by simpa) ha

Depends on / 依赖: le_of_smul_le_smul_of_pos_left
-/
lemma nonpos_of_smul_nonpos_of_pos_left [PosSMulReflectLE α β] (h : a • b <= 0) (ha : 0 < a) :
    b <= 0 :=
  le_of_smul_le_smul_of_pos_left (by simpa) ha

/--
lemma `smul_nonneg_iff_nonneg_of_pos_left` / 引理 `smul_nonneg_iff_nonneg_of_pos_left`

English:
lemma smul_nonneg_iff_nonneg_of_pos_left
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  proof: ⟨(nonneg_of_smul_nonneg_of_pos_left · ha), smul_nonneg ha.le⟩

中文:
引理 smul_nonneg_iff_nonneg_of_pos_left
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  证明: ⟨(nonneg_of_smul_nonneg_of_pos_left · ha), smul_nonneg ha.le⟩

Depends on / 依赖: ha.le, nonneg_of_smul_nonneg_of_pos_left, smul_nonneg
-/
lemma smul_nonneg_iff_nonneg_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    0 <= a • b ↔ 0 <= b :=
  ⟨(nonneg_of_smul_nonneg_of_pos_left · ha), smul_nonneg ha.le⟩

/--
lemma `smul_nonpos_iff_nonpos_of_pos_left` / 引理 `smul_nonpos_iff_nonpos_of_pos_left`

English:
lemma smul_nonpos_iff_nonpos_of_pos_left
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  proof: ⟨(nonpos_of_smul_nonpos_of_pos_left · ha), smul_nonpos_of_nonneg_of_nonpos ha.le⟩

中文:
引理 smul_nonpos_iff_nonpos_of_pos_left
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  证明: ⟨(nonpos_of_smul_nonpos_of_pos_left · ha), smul_nonpos_of_nonneg_of_nonpos ha.le⟩

Depends on / 依赖: ha.le, nonpos_of_smul_nonpos_of_pos_left, smul_nonpos_of_nonneg_of_nonpos
-/
lemma smul_nonpos_iff_nonpos_of_pos_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a • b <= 0 ↔ b <= 0 :=
  ⟨(nonpos_of_smul_nonpos_of_pos_left · ha), smul_nonpos_of_nonneg_of_nonpos ha.le⟩

end Preorder
end SMulZeroClass

section SMulWithZero
variable [Zero α] [Zero β] [SMulWithZero α β]

section Preorder
variable [Preorder α] [Preorder β]

/--
lemma `smul_pos'` / 引理 `smul_pos'`

English:
lemma smul_pos'
  given: [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a • b
  proof: by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

中文:
引理 smul_pos'
  条件: [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a • b
  证明: by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

Depends on / 依赖: smul_lt_smul_of_pos_right, zero_smul
-/
lemma smul_pos' [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

/--
lemma `smul_neg_of_neg_of_pos` / 引理 `smul_neg_of_neg_of_pos`

English:
lemma smul_neg_of_neg_of_pos
  given: [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b)
  statement: a • b < 0
  proof: by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

@[simp]

中文:
引理 smul_neg_of_neg_of_pos
  条件: [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b)
  结论: a • b < 0
  证明: by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

@[simp]

Depends on / 依赖: smul_lt_smul_of_pos_right, zero_smul
-/
lemma smul_neg_of_neg_of_pos [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b) : a • b < 0 := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

@[simp]
/--
lemma `smul_pos_iff_of_pos_right` / 引理 `smul_pos_iff_of_pos_right`

English:
lemma smul_pos_iff_of_pos_right
  given: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  proof: by
  simpa only [zero_smul] using smul_lt_smul_iff_of_pos_right hb (a₁ := 0) (a₂ := a)

中文:
引理 smul_pos_iff_of_pos_right
  条件: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  证明: by
  simpa only [zero_smul] using smul_lt_smul_iff_of_pos_right hb (a₁ := 0) (a₂ := a)

Depends on / 依赖: smul_lt_smul_iff_of_pos_right, zero_smul
-/
lemma smul_pos_iff_of_pos_right [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    0 < a • b ↔ 0 < a := by
  simpa only [zero_smul] using smul_lt_smul_iff_of_pos_right hb (a₁ := 0) (a₂ := a)

/--
lemma `smul_nonneg'` / 引理 `smul_nonneg'`

English:
lemma smul_nonneg'
  given: [SMulPosMono α β] (ha : 0 <= a) (hb : 0 <= b₁)
  statement: 0 <= a • b₁
  proof: by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

中文:
引理 smul_nonneg'
  条件: [SMulPosMono α β] (ha : 0 <= a) (hb : 0 <= b₁)
  结论: 0 <= a • b₁
  证明: by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

Depends on / 依赖: smul_le_smul_of_nonneg_right, zero_smul
-/
lemma smul_nonneg' [SMulPosMono α β] (ha : 0 <= a) (hb : 0 <= b₁) : 0 <= a • b₁ := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

/--
lemma `smul_nonpos_of_nonpos_of_nonneg` / 引理 `smul_nonpos_of_nonpos_of_nonneg`

English:
lemma smul_nonpos_of_nonpos_of_nonneg
  given: [SMulPosMono α β] (ha : a <= 0) (hb : 0 <= b)
  statement: a • b <= 0
  proof: by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

中文:
引理 smul_nonpos_of_nonpos_of_nonneg
  条件: [SMulPosMono α β] (ha : a <= 0) (hb : 0 <= b)
  结论: a • b <= 0
  证明: by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

Depends on / 依赖: smul_le_smul_of_nonneg_right, zero_smul
-/
lemma smul_nonpos_of_nonpos_of_nonneg [SMulPosMono α β] (ha : a <= 0) (hb : 0 <= b) : a • b <= 0 := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

/--
lemma `pos_of_smul_pos_right` / 引理 `pos_of_smul_pos_right`

English:
lemma pos_of_smul_pos_right
  given: [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 <= b)
  statement: 0 < a
  proof: lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

中文:
引理 pos_of_smul_pos_right
  条件: [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 <= b)
  结论: 0 < a
  证明: lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

Depends on / 依赖: lt_of_smul_lt_smul_right, zero_smul
-/
lemma pos_of_smul_pos_right [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 <= b) : 0 < a :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

/--
lemma `neg_of_smul_neg_right` / 引理 `neg_of_smul_neg_right`

English:
lemma neg_of_smul_neg_right
  given: [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 <= b)
  statement: a < 0
  proof: lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

中文:
引理 neg_of_smul_neg_right
  条件: [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 <= b)
  结论: a < 0
  证明: lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

Depends on / 依赖: lt_of_smul_lt_smul_right, zero_smul
-/
lemma neg_of_smul_neg_right [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 <= b) : a < 0 :=
  lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

/--
lemma `pos_iff_pos_of_smul_pos` / 引理 `pos_iff_pos_of_smul_pos`

English:
lemma pos_iff_pos_of_smul_pos
  given: [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab : 0 < a • b)
  proof: ⟨pos_of_smul_pos_left hab ∘ le_of_lt, pos_of_smul_pos_right hab ∘ le_of_lt⟩

中文:
引理 pos_iff_pos_of_smul_pos
  条件: [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab : 0 < a • b)
  证明: ⟨pos_of_smul_pos_left hab ∘ le_of_lt, pos_of_smul_pos_right hab ∘ le_of_lt⟩

Depends on / 依赖: le_of_lt, pos_of_smul_pos_left, pos_of_smul_pos_right
-/
lemma pos_iff_pos_of_smul_pos [PosSMulReflectLT α β] [SMulPosReflectLT α β] (hab : 0 < a • b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_smul_pos_left hab ∘ le_of_lt, pos_of_smul_pos_right hab ∘ le_of_lt⟩

/--
lemma `nonneg_of_smul_nonneg_of_pos_right` / 引理 `nonneg_of_smul_nonneg_of_pos_right`

English:
lemma nonneg_of_smul_nonneg_of_pos_right
  given: [SMulPosReflectLE α β] (h : 0 <= a • b) (hb : 0 < b)
  proof: le_of_smul_le_smul_of_pos_right (by simpa) hb

中文:
引理 nonneg_of_smul_nonneg_of_pos_right
  条件: [SMulPosReflectLE α β] (h : 0 <= a • b) (hb : 0 < b)
  证明: le_of_smul_le_smul_of_pos_right (by simpa) hb

Depends on / 依赖: le_of_smul_le_smul_of_pos_right, npowRec
-/
lemma nonneg_of_smul_nonneg_of_pos_right [SMulPosReflectLE α β] (h : 0 <= a • b) (hb : 0 < b) :
    0 <= a :=
  le_of_smul_le_smul_of_pos_right (by simpa) hb

/--
lemma `nonpos_of_smul_nonpos_of_pos_right` / 引理 `nonpos_of_smul_nonpos_of_pos_right`

English:
lemma nonpos_of_smul_nonpos_of_pos_right
  given: [SMulPosReflectLE α β] (h : a • b <= 0) (hb : 0 < b)
  proof: le_of_smul_le_smul_of_pos_right (by simpa) hb

中文:
引理 nonpos_of_smul_nonpos_of_pos_right
  条件: [SMulPosReflectLE α β] (h : a • b <= 0) (hb : 0 < b)
  证明: le_of_smul_le_smul_of_pos_right (by simpa) hb

Depends on / 依赖: le_of_smul_le_smul_of_pos_right
-/
lemma nonpos_of_smul_nonpos_of_pos_right [SMulPosReflectLE α β] (h : a • b <= 0) (hb : 0 < b) :
    a <= 0 :=
  le_of_smul_le_smul_of_pos_right (by simpa) hb

/--
lemma `smul_nonneg_iff_nonneg_of_pos_right` / 引理 `smul_nonneg_iff_nonneg_of_pos_right`

English:
lemma smul_nonneg_iff_nonneg_of_pos_right
  given: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  proof: ⟨(nonneg_of_smul_nonneg_of_pos_right · hb), (smul_nonneg' · hb.le)⟩

中文:
引理 smul_nonneg_iff_nonneg_of_pos_right
  条件: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  证明: ⟨(nonneg_of_smul_nonneg_of_pos_right · hb), (smul_nonneg' · hb.le)⟩

Depends on / 依赖: hb.le, nonneg_of_smul_nonneg_of_pos_right, smul_nonneg
-/
lemma smul_nonneg_iff_nonneg_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    0 <= a • b ↔ 0 <= a :=
  ⟨(nonneg_of_smul_nonneg_of_pos_right · hb), (smul_nonneg' · hb.le)⟩

/--
lemma `smul_nonpos_iff_nonpos_of_pos_right` / 引理 `smul_nonpos_iff_nonpos_of_pos_right`

English:
lemma smul_nonpos_iff_nonpos_of_pos_right
  given: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  proof: ⟨(nonpos_of_smul_nonpos_of_pos_right · hb), (smul_nonpos_of_nonpos_of_nonneg · hb.le)⟩

中文:
引理 smul_nonpos_iff_nonpos_of_pos_right
  条件: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  证明: ⟨(nonpos_of_smul_nonpos_of_pos_right · hb), (smul_nonpos_of_nonpos_of_nonneg · hb.le)⟩

Depends on / 依赖: hb.le, nonpos_of_smul_nonpos_of_pos_right, smul_nonpos_of_nonpos_of_nonneg
-/
lemma smul_nonpos_iff_nonpos_of_pos_right [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a • b <= 0 ↔ a <= 0 :=
  ⟨(nonpos_of_smul_nonpos_of_pos_right · hb), (smul_nonpos_of_nonpos_of_nonneg · hb.le)⟩

/--
lemma `IsOrderedModule.of_smul_one_mono` / 引理 `IsOrderedModule.of_smul_one_mono`

English:
lemma IsOrderedModule.of_smul_one_mono
  proof: by
    have := mul_le_mul_of_nonneg_left hb (by simpa using h ha)
    simpa
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa using mul_le_mul_of_nonneg_right (h hb) ha

中文:
引理 IsOrderedModule.of_smul_one_mono
  证明: by
    have := mul_le_mul_of_nonneg_left hb (by simpa using h ha)
    simpa
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa using mul_le_mul_of_nonneg_right (h hb) ha

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, smul_le_smul_of_nonneg_right
-/
lemma IsOrderedModule.of_smul_one_mono
    [MulOneClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β]
    (h : Monotone (fun x : α => x • (1 : β))) : IsOrderedModule α β where
  smul_le_smul_of_nonneg_left _ ha _ _ hb := by
    have := mul_le_mul_of_nonneg_left hb (by simpa using h ha)
    simpa
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa using mul_le_mul_of_nonneg_right (h hb) ha

/--
theorem `isOrderedModule_iff_smul_one_mono` / 定理 `isOrderedModule_iff_smul_one_mono`

English:
theorem isOrderedModule_iff_smul_one_mono
  proof: smul_one_mono _
  mpr := IsOrderedModule.of_smul_one_mono

中文:
定理 isOrderedModule_iff_smul_one_mono
  证明: smul_one_mono _
  mpr := IsOrderedModule.of_smul_one_mono

Depends on / 依赖: smul_one_mono
-/
theorem isOrderedModule_iff_smul_one_mono
    [MulOneClass β] [ZeroLEOneClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β] :
    IsOrderedModule α β ↔ Monotone (fun x : α => x • (1 : β)) where
  mp _ := smul_one_mono _
  mpr := IsOrderedModule.of_smul_one_mono

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β]

/--
lemma `PosSMulMono.of_pos` / 引理 `PosSMulMono.of_pos`

English:
lemma PosSMulMono.of_pos
  given: (h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, b₁ <= b₂ -> a • b₁ <= a • b₂)
  proof: by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha]
    · exact h₀ _ ha _ _ h

中文:
引理 PosSMulMono.of_pos
  条件: (h₀ : 对任意 a : α, 0 < a -> 对任意 b₁ b₂ : β, b₁ <= b₂ -> a • b₁ <= a • b₂)
  证明: by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha]
    · exact h₀ _ ha _ _ h

Depends on / 依赖: eq_or_lt, ha.eq_or_lt
-/
lemma PosSMulMono.of_pos (h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, b₁ <= b₂ -> a • b₁ <= a • b₂) :
    PosSMulMono α β where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha]
    · exact h₀ _ ha _ _ h

/--
lemma `PosSMulReflectLT.of_pos` / 引理 `PosSMulReflectLT.of_pos`

English:
lemma PosSMulReflectLT.of_pos
  given: (h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, a • b₁ < a • b₂ -> b₁ < b₂)
  proof: by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha] at h
    · exact h₀ _ ha _ _ h

中文:
引理 PosSMulReflectLT.of_pos
  条件: (h₀ : 对任意 a : α, 0 < a -> 对任意 b₁ b₂ : β, a • b₁ < a • b₂ -> b₁ < b₂)
  证明: by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha] at h
    · exact h₀ _ ha _ _ h

Depends on / 依赖: eq_or_lt, ha.eq_or_lt
-/
lemma PosSMulReflectLT.of_pos (h₀ : forall a : α, 0 < a -> forall b₁ b₂ : β, a • b₁ < a • b₂ -> b₁ < b₂) :
    PosSMulReflectLT α β where
  lt_of_smul_lt_smul_left a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha] at h
    · exact h₀ _ ha _ _ h

end PartialOrder

section PartialOrder
variable [Preorder α] [PartialOrder β]

/--
lemma `SMulPosMono.of_pos` / 引理 `SMulPosMono.of_pos`

English:
lemma SMulPosMono.of_pos
  given: (h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ <= a₂ -> a₁ • b <= a₂ • b)
  proof: by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb]
    · exact h₀ _ hb _ _ h

中文:
引理 SMulPosMono.of_pos
  条件: (h₀ : 对任意 b : β, 0 < b -> 对任意 a₁ a₂ : α, a₁ <= a₂ -> a₁ • b <= a₂ • b)
  证明: by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb]
    · exact h₀ _ hb _ _ h

Depends on / 依赖: eq_or_lt, hb.eq_or_lt
-/
lemma SMulPosMono.of_pos (h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ <= a₂ -> a₁ • b <= a₂ • b) :
    SMulPosMono α β where
  smul_le_smul_of_nonneg_right b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb]
    · exact h₀ _ hb _ _ h

/--
lemma `SMulPosReflectLT.of_pos` / 引理 `SMulPosReflectLT.of_pos`

English:
lemma SMulPosReflectLT.of_pos
  given: (h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ • b < a₂ • b -> a₁ < a₂)
  proof: by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb] at h
    · exact h₀ _ hb _ _ h

中文:
引理 SMulPosReflectLT.of_pos
  条件: (h₀ : 对任意 b : β, 0 < b -> 对任意 a₁ a₂ : α, a₁ • b < a₂ • b -> a₁ < a₂)
  证明: by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb] at h
    · exact h₀ _ hb _ _ h

Depends on / 依赖: eq_or_lt, hb.eq_or_lt
-/
lemma SMulPosReflectLT.of_pos (h₀ : forall b : β, 0 < b -> forall a₁ a₂ : α, a₁ • b < a₂ • b -> a₁ < a₂) :
    SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb] at h
    · exact h₀ _ hb _ _ h

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

-- See note [lower instance priority]
instance (priority := 100) PosSMulStrictMono.toPosSMulMono [PosSMulStrictMono α β] :
    PosSMulMono α β :=
  PosSMulMono.of_pos fun _a ha => (strictMono_smul_left_of_pos ha).monotone

-- See note [lower instance priority]
instance (priority := 100) SMulPosStrictMono.toSMulPosMono [SMulPosStrictMono α β] :
    SMulPosMono α β :=
  SMulPosMono.of_pos fun _b hb => (strictMono_smul_right_of_pos hb).monotone

-- See note [lower instance priority]
instance (priority := 100) PosSMulReflectLE.toPosSMulReflectLT [PosSMulReflectLE α β] :
    PosSMulReflectLT α β :=
  PosSMulReflectLT.of_pos fun a ha b₁ b₂ h =>
(le_of_smul_le_smul_of_pos_left h.le ha).lt_of_ne by rintro rfl; simp at h

-- See note [lower instance priority]
instance (priority := 100) SMulPosReflectLE.toSMulPosReflectLT [SMulPosReflectLE α β] :
    SMulPosReflectLT α β :=
  SMulPosReflectLT.of_pos fun b hb a₁ a₂ h =>
(le_of_smul_le_smul_of_pos_right h.le hb).lt_of_ne by rintro rfl; simp at h

-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedModule.toIsOrderedModule [IsStrictOrderedModule α β] :
    IsOrderedModule α β where

/--
lemma `smul_eq_smul_iff_eq_and_eq_of_pos` / 引理 `smul_eq_smul_iff_eq_and_eq_of_pos`

English:
lemma smul_eq_smul_iff_eq_and_eq_of_pos
  statement: [PosSMulStrictMono α β] [SMulPosStrictMono α β]
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_lt ?_, fun hb => h.not_lt ?_⟩
  · exact (smul_le_smul_of_nonneg_left hb h₁.le).trans_lt (smul_lt_smul_of_pos_right ha h₂)
  · exact (smul_lt_smul_of_pos_left hb h₁).trans_l

中文:
引理 smul_eq_smul_iff_eq_and_eq_of_pos
  结论: [PosSMulStrictMono α β] [SMulPosStrictMono α β]
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_lt ?_, fun hb => h.not_lt ?_⟩
  · exact (smul_le_smul_of_nonneg_left hb h₁.le).trans_lt (smul_lt_smul_of_pos_right ha h₂)
  · exact (smul_lt_smul_of_pos_left hb h₁).trans_l

Depends on / 依赖: eq_iff_le_not_lt, h.not_lt, not_lt, smul_le_smul_of_nonneg_left, smul_le_smul_of_nonneg_right, smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_right, trans_le, trans_lt, true_and
-/
lemma smul_eq_smul_iff_eq_and_eq_of_pos [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₁ : 0 < a₁) (h₂ : 0 < b₂) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_lt ?_, fun hb => h.not_lt ?_⟩
  · exact (smul_le_smul_of_nonneg_left hb h₁.le).trans_lt (smul_lt_smul_of_pos_right ha h₂)
  · exact (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂.le)

/--
lemma `smul_eq_smul_iff_eq_and_eq_of_pos'` / 引理 `smul_eq_smul_iff_eq_and_eq_of_pos'`

English:
lemma smul_eq_smul_iff_eq_and_eq_of_pos'
  statement: [PosSMulStrictMono α β] [SMulPosStrictMono α β]
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_lt ?_, fun hb => h.not_lt ?_⟩
  · exact (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂.le)
  · exact (smul_le_smul_of_nonneg_right ha h₁.le).

中文:
引理 smul_eq_smul_iff_eq_and_eq_of_pos'
  结论: [PosSMulStrictMono α β] [SMulPosStrictMono α β]
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_lt ?_, fun hb => h.not_lt ?_⟩
  · exact (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂.le)
  · exact (smul_le_smul_of_nonneg_right ha h₁.le).

Depends on / 依赖: eq_iff_le_not_lt, h.not_lt, not_lt, smul_le_smul_of_nonneg_left, smul_le_smul_of_nonneg_right, smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_right, trans_le, trans_lt, true_and
-/
lemma smul_eq_smul_iff_eq_and_eq_of_pos' [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ <= a₂) (hb : b₁ <= b₂) (h₂ : 0 < a₂) (h₁ : 0 < b₁) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_lt ?_, fun hb => h.not_lt ?_⟩
  · exact (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂.le)
  · exact (smul_le_smul_of_nonneg_right ha h₁.le).trans_lt (smul_lt_smul_of_pos_left hb h₂)

end PartialOrder

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

/--
lemma `pos_and_pos_or_neg_and_neg_of_smul_pos` / 引理 `pos_and_pos_or_neg_and_neg_of_smul_pos`

English:
lemma pos_and_pos_or_neg_and_neg_of_smul_pos
  given: [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b)
  proof: by
  obtain ha | rfl | ha := lt_trichotomy a 0
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact smul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_smul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact smul_nonp

中文:
引理 pos_and_pos_or_neg_and_neg_of_smul_pos
  条件: [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b)
  证明: by
  obtain ha | rfl | ha := lt_trichotomy a 0
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact smul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_smul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact smul_nonp

Depends on / 依赖: Or.inl, Or.inr, ha.le, hab.false.elim, lt_imp_lt_of_le_imp_le, lt_trichotomy, smul_nonpos_of_nonneg_of_nonpos, smul_nonpos_of_nonpos_of_nonneg, zero_smul
-/
lemma pos_and_pos_or_neg_and_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  obtain ha | rfl | ha := lt_trichotomy a 0
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact smul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_smul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact smul_nonpos_of_nonneg_of_nonpos ha.le hb

/--
lemma `neg_of_smul_pos_right` / 引理 `neg_of_smul_pos_right`

English:
lemma neg_of_smul_pos_right
  given: [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : a <= 0)
  proof: ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h => h.1.not_ge ha).2

中文:
引理 neg_of_smul_pos_right
  条件: [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : a <= 0)
  证明: ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h => h.1.not_ge ha).2

Depends on / 依赖: not_ge, pos_and_pos_or_neg_and_neg_of_smul_pos, resolve_left
-/
lemma neg_of_smul_pos_right [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : a <= 0) :
    b < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h => h.1.not_ge ha).2

/--
lemma `neg_of_smul_pos_left` / 引理 `neg_of_smul_pos_left`

English:
lemma neg_of_smul_pos_left
  given: [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b <= 0)
  proof: ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h => h.2.not_ge ha).1

中文:
引理 neg_of_smul_pos_left
  条件: [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b <= 0)
  证明: ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h => h.2.not_ge ha).1

Depends on / 依赖: not_ge, pos_and_pos_or_neg_and_neg_of_smul_pos, resolve_left
-/
lemma neg_of_smul_pos_left [PosSMulMono α β] [SMulPosMono α β] (h : 0 < a • b) (ha : b <= 0) :
    a < 0 := ((pos_and_pos_or_neg_and_neg_of_smul_pos h).resolve_left fun h => h.2.not_ge ha).1

/--
lemma `neg_iff_neg_of_smul_pos` / 引理 `neg_iff_neg_of_smul_pos`

English:
lemma neg_iff_neg_of_smul_pos
  given: [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b)
  proof: ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩

中文:
引理 neg_iff_neg_of_smul_pos
  条件: [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b)
  证明: ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩

Depends on / 依赖: le_of_lt, neg_of_smul_pos_left, neg_of_smul_pos_right
-/
lemma neg_iff_neg_of_smul_pos [PosSMulMono α β] [SMulPosMono α β] (hab : 0 < a • b) :
    a < 0 ↔ b < 0 :=
  ⟨neg_of_smul_pos_right hab ∘ le_of_lt, neg_of_smul_pos_left hab ∘ le_of_lt⟩

/--
lemma `neg_of_smul_neg_left'` / 引理 `neg_of_smul_neg_left'`

English:
lemma neg_of_smul_neg_left'
  given: [SMulPosMono α β] (h : a • b < 0) (ha : 0 <= a)
  statement: b < 0
  proof: lt_of_not_ge fun hb => (smul_nonneg' ha hb).not_gt h

中文:
引理 neg_of_smul_neg_left'
  条件: [SMulPosMono α β] (h : a • b < 0) (ha : 0 <= a)
  结论: b < 0
  证明: lt_of_not_ge fun hb => (smul_nonneg' ha hb).not_gt h

Depends on / 依赖: lt_of_not_ge, not_gt, smul_nonneg
-/
lemma neg_of_smul_neg_left' [SMulPosMono α β] (h : a • b < 0) (ha : 0 <= a) : b < 0 :=
  lt_of_not_ge fun hb => (smul_nonneg' ha hb).not_gt h

/--
lemma `neg_of_smul_neg_right'` / 引理 `neg_of_smul_neg_right'`

English:
lemma neg_of_smul_neg_right'
  given: [PosSMulMono α β] (h : a • b < 0) (hb : 0 <= b)
  statement: a < 0
  proof: lt_of_not_ge fun ha => (smul_nonneg ha hb).not_gt h

中文:
引理 neg_of_smul_neg_right'
  条件: [PosSMulMono α β] (h : a • b < 0) (hb : 0 <= b)
  结论: a < 0
  证明: lt_of_not_ge fun ha => (smul_nonneg ha hb).not_gt h

Depends on / 依赖: lt_of_not_ge, not_gt, smul_nonneg
-/
lemma neg_of_smul_neg_right' [PosSMulMono α β] (h : a • b < 0) (hb : 0 <= b) : a < 0 :=
  lt_of_not_ge fun ha => (smul_nonneg ha hb).not_gt h

end LinearOrder
end SMulWithZero

section MulAction
variable [Monoid α] [Zero β] [MulAction α β]

section Preorder
variable [Preorder α] [Preorder β]

@[simp]
/--
lemma `le_smul_iff_one_le_left` / 引理 `le_smul_iff_one_le_left`

English:
lemma le_smul_iff_one_le_left
  given: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  proof: Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]

中文:
引理 le_smul_iff_one_le_left
  条件: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  证明: Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]

Depends on / 依赖: Iff.trans, one_smul, smul_le_smul_iff_of_pos_right
-/
lemma le_smul_iff_one_le_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    b <= a • b ↔ 1 <= a := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
/--
lemma `lt_smul_iff_one_lt_left` / 引理 `lt_smul_iff_one_lt_left`

English:
lemma lt_smul_iff_one_lt_left
  given: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  proof: Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

@[simp]

中文:
引理 lt_smul_iff_one_lt_left
  条件: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  证明: Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

@[simp]

Depends on / 依赖: Iff.trans, one_smul, smul_lt_smul_iff_of_pos_right
-/
lemma lt_smul_iff_one_lt_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    b < a • b ↔ 1 < a := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

@[simp]
/--
lemma `smul_le_iff_le_one_left` / 引理 `smul_le_iff_le_one_left`

English:
lemma smul_le_iff_le_one_left
  given: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  proof: Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]

中文:
引理 smul_le_iff_le_one_left
  条件: [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b)
  证明: Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]

Depends on / 依赖: Iff.trans, one_smul, smul_le_smul_iff_of_pos_right
-/
lemma smul_le_iff_le_one_left [SMulPosMono α β] [SMulPosReflectLE α β] (hb : 0 < b) :
    a • b <= b ↔ a <= 1 := Iff.trans (by rw [one_smul]) (smul_le_smul_iff_of_pos_right hb)

@[simp]
/--
lemma `smul_lt_iff_lt_one_left` / 引理 `smul_lt_iff_lt_one_left`

English:
lemma smul_lt_iff_lt_one_left
  given: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  proof: Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

中文:
引理 smul_lt_iff_lt_one_left
  条件: [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b)
  证明: Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

Depends on / 依赖: Iff.trans, one_smul, smul_lt_smul_iff_of_pos_right
-/
lemma smul_lt_iff_lt_one_left [SMulPosStrictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) :
    a • b < b ↔ a < 1 := Iff.trans (by rw [one_smul]) (smul_lt_smul_iff_of_pos_right hb)

/--
lemma `smul_le_of_le_one_left` / 引理 `smul_le_of_le_one_left`

English:
lemma smul_le_of_le_one_left
  given: [SMulPosMono α β] (hb : 0 <= b) (h : a <= 1)
  statement: a • b <= b
  proof: by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

中文:
引理 smul_le_of_le_one_left
  条件: [SMulPosMono α β] (hb : 0 <= b) (h : a <= 1)
  结论: a • b <= b
  证明: by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

Depends on / 依赖: one_smul, smul_le_smul_of_nonneg_right
-/
lemma smul_le_of_le_one_left [SMulPosMono α β] (hb : 0 <= b) (h : a <= 1) : a • b <= b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

/--
lemma `le_smul_of_one_le_left` / 引理 `le_smul_of_one_le_left`

English:
lemma le_smul_of_one_le_left
  given: [SMulPosMono α β] (hb : 0 <= b) (h : 1 <= a)
  statement: b <= a • b
  proof: by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

中文:
引理 le_smul_of_one_le_left
  条件: [SMulPosMono α β] (hb : 0 <= b) (h : 1 <= a)
  结论: b <= a • b
  证明: by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

Depends on / 依赖: one_smul, smul_le_smul_of_nonneg_right
-/
lemma le_smul_of_one_le_left [SMulPosMono α β] (hb : 0 <= b) (h : 1 <= a) : b <= a • b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

/--
lemma `smul_lt_of_lt_one_left` / 引理 `smul_lt_of_lt_one_left`

English:
lemma smul_lt_of_lt_one_left
  given: [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1)
  statement: a • b < b
  proof: by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

中文:
引理 smul_lt_of_lt_one_left
  条件: [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1)
  结论: a • b < b
  证明: by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

Depends on / 依赖: one_smul, smul_lt_smul_of_pos_right
-/
lemma smul_lt_of_lt_one_left [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1) : a • b < b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

/--
lemma `lt_smul_of_one_lt_left` / 引理 `lt_smul_of_one_lt_left`

English:
lemma lt_smul_of_one_lt_left
  given: [SMulPosStrictMono α β] (hb : 0 < b) (h : 1 < a)
  statement: b < a • b
  proof: by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

中文:
引理 lt_smul_of_one_lt_left
  条件: [SMulPosStrictMono α β] (hb : 0 < b) (h : 1 < a)
  结论: b < a • b
  证明: by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

Depends on / 依赖: one_smul, smul_lt_smul_of_pos_right
-/
lemma lt_smul_of_one_lt_left [SMulPosStrictMono α β] (hb : 0 < b) (h : 1 < a) : b < a • b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

end Preorder
end MulAction

section Semiring
variable [Semiring α] [AddCommGroup β] [Module α β]

/--
lemma `PosSMulMono.of_smul_nonneg` / 引理 `PosSMulMono.of_smul_nonneg`

English:
lemma PosSMulMono.of_smul_nonneg
  statement: [PartialOrder α] [PartialOrder β] [IsOrderedAddMonoid β]
  proof: by simpa [sub_nonneg, smul_sub] using h _ ha (b₂ - b₁)

中文:
引理 PosSMulMono.of_smul_nonneg
  结论: [PartialOrder α] [PartialOrder β] [IsOrderedAddMonoid β]
  证明: by simpa [sub_nonneg, smul_sub] using h _ ha (b₂ - b₁)

Depends on / 依赖: smul_sub, sub_nonneg
-/
lemma PosSMulMono.of_smul_nonneg [PartialOrder α] [PartialOrder β] [IsOrderedAddMonoid β]
    (h : forall a : α, 0 <= a -> forall b : β, 0 <= b -> 0 <= a • b) : PosSMulMono α β where
  smul_le_smul_of_nonneg_left _a ha b₁ b₂ := by simpa [sub_nonneg, smul_sub] using h _ ha (b₂ - b₁)

variable [IsDomain α] [Module.IsTorsionFree α β]

section PartialOrder
variable [Preorder α] [PartialOrder β]

/--
lemma `PosSMulMono.toPosSMulStrictMono` / 引理 `PosSMulMono.toPosSMulStrictMono`

English:
lemma PosSMulMono.toPosSMulStrictMono
  given: [PosSMulMono α β]
  statement: PosSMulStrictMono α β
  proof: ⟨fun _a ha _b₁ _b₂ hb => (smul_le_smul_of_nonneg_left hb.le ha.le).lt_of_ne
    (smul_right_injective _ ha.ne').ne hb.ne⟩

中文:
引理 PosSMulMono.toPosSMulStrictMono
  条件: [PosSMulMono α β]
  结论: PosSMulStrictMono α β
  证明: ⟨fun _a ha _b₁ _b₂ hb => (smul_le_smul_of_nonneg_left hb.le ha.le).lt_of_ne
    (smul_right_injective _ ha.ne').ne hb.ne⟩

Depends on / 依赖: ha.le, ha.ne, hb.le, hb.ne, lt_of_ne, smul_le_smul_of_nonneg_left, smul_right_injective
-/
lemma PosSMulMono.toPosSMulStrictMono [PosSMulMono α β] : PosSMulStrictMono α β :=
⟨fun _a ha _b₁ _b₂ hb => (smul_le_smul_of_nonneg_left hb.le ha.le).lt_of_ne
    (smul_right_injective _ ha.ne').ne hb.ne⟩

/--
Instance `PosSMulReflectLT.toPosSMulReflectLE` / 实例 `PosSMulReflectLT.toPosSMulReflectLE`

English:
instance PosSMulReflectLT.toPosSMulReflectLE
  signature: [PosSMulReflectLT α β]
  body: ⟨fun _a ha _b₁ _b₂ h => h.eq_or_lt.elim
    (fun h => (smul_right_injective _ ha.ne' h).le) fun h' =>
    (lt_of_smul_lt_smul_left h' ha.le).le⟩

中文:
实例 PosSMulReflectLT.toPosSMulReflectLE
  签名: [PosSMulReflectLT α β]
  定义体: ⟨fun _a ha _b₁ _b₂ h => h.eq_or_lt.elim
    (fun h => (smul_right_injective _ ha.ne' h).le) fun h' =>
    (lt_of_smul_lt_smul_left h' ha.le).le⟩

Depends on / 依赖: eq_or_lt, h.eq_or_lt.elim, ha.le, ha.ne, lt_of_smul_lt_smul_left, smul_right_injective
-/
instance PosSMulReflectLT.toPosSMulReflectLE [PosSMulReflectLT α β] : PosSMulReflectLE α β :=
  ⟨fun _a ha _b₁ _b₂ h => h.eq_or_lt.elim
    (fun h => (smul_right_injective _ ha.ne' h).le) fun h' =>
    (lt_of_smul_lt_smul_left h' ha.le).le⟩

end PartialOrder

section PartialOrder
variable [PartialOrder α] [PartialOrder β]

/--
lemma `posSMulMono_iff_posSMulStrictMono` / 引理 `posSMulMono_iff_posSMulStrictMono`

English:
lemma posSMulMono_iff_posSMulStrictMono
  statement: PosSMulMono α β ↔ PosSMulStrictMono α β
  proof: ⟨fun _ => PosSMulMono.toPosSMulStrictMono, fun _ => inferInstance⟩

中文:
引理 posSMulMono_iff_posSMulStrictMono
  结论: PosSMulMono α β ↔ PosSMulStrictMono α β
  证明: ⟨fun _ => PosSMulMono.toPosSMulStrictMono, fun _ => inferInstance⟩

Depends on / 依赖: PosSMulMono, PosSMulMono.toPosSMulStrictMono, toPosSMulStrictMono
-/
lemma posSMulMono_iff_posSMulStrictMono : PosSMulMono α β ↔ PosSMulStrictMono α β :=
  ⟨fun _ => PosSMulMono.toPosSMulStrictMono, fun _ => inferInstance⟩

/--
lemma `PosSMulReflectLE_iff_posSMulReflectLT` / 引理 `PosSMulReflectLE_iff_posSMulReflectLT`

English:
lemma PosSMulReflectLE_iff_posSMulReflectLT
  statement: PosSMulReflectLE α β ↔ PosSMulReflectLT α β
  proof: ⟨fun _ => inferInstance, fun _ => PosSMulReflectLT.toPosSMulReflectLE⟩

中文:
引理 PosSMulReflectLE_iff_posSMulReflectLT
  结论: PosSMulReflectLE α β ↔ PosSMulReflectLT α β
  证明: ⟨fun _ => inferInstance, fun _ => PosSMulReflectLT.toPosSMulReflectLE⟩

Depends on / 依赖: PosSMulReflectLT, PosSMulReflectLT.toPosSMulReflectLE, toPosSMulReflectLE
-/
lemma PosSMulReflectLE_iff_posSMulReflectLT : PosSMulReflectLE α β ↔ PosSMulReflectLT α β :=
  ⟨fun _ => inferInstance, fun _ => PosSMulReflectLT.toPosSMulReflectLE⟩

end PartialOrder
end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

/--
lemma `IsOrderedModule.of_smul_nonneg` / 引理 `IsOrderedModule.of_smul_nonneg`

English:
lemma IsOrderedModule.of_smul_nonneg
  statement: [IsOrderedAddMonoid α] [IsOrderedAddMonoid β]
  proof: .of_smul_nonneg h
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ := by
    simpa [sub_nonneg, sub_smul] using (h (a₂ - a₁) · _ hb)

中文:
引理 IsOrderedModule.of_smul_nonneg
  结论: [IsOrderedAddMonoid α] [IsOrderedAddMonoid β]
  证明: .of_smul_nonneg h
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ := by
    simpa [sub_nonneg, sub_smul] using (h (a₂ - a₁) · _ hb)

Depends on / 依赖: of_smul_nonneg
-/
lemma IsOrderedModule.of_smul_nonneg [IsOrderedAddMonoid α] [IsOrderedAddMonoid β]
    (h : forall a : α, 0 <= a -> forall b : β, 0 <= b -> 0 <= a • b) : IsOrderedModule α β where
  toPosSMulMono := .of_smul_nonneg h
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ := by
    simpa [sub_nonneg, sub_smul] using (h (a₂ - a₁) · _ hb)

variable [IsDomain α] [Module.IsTorsionFree α β]

/--
lemma `SMulPosMono.toSMulPosStrictMono` / 引理 `SMulPosMono.toSMulPosStrictMono`

English:
lemma SMulPosMono.toSMulPosStrictMono
  given: [SMulPosMono α β]
  statement: SMulPosStrictMono α β
  proof: ⟨fun _b hb _a₁ _a₂ ha => (smul_le_smul_of_nonneg_right ha.le hb.le).lt_of_ne
    (smul_left_injective _ hb.ne').ne ha.ne⟩

中文:
引理 SMulPosMono.toSMulPosStrictMono
  条件: [SMulPosMono α β]
  结论: SMulPosStrictMono α β
  证明: ⟨fun _b hb _a₁ _a₂ ha => (smul_le_smul_of_nonneg_right ha.le hb.le).lt_of_ne
    (smul_left_injective _ hb.ne').ne ha.ne⟩

Depends on / 依赖: ha.le, ha.ne, hb.le, hb.ne, lt_of_ne, smul_le_smul_of_nonneg_right, smul_left_injective
-/
lemma SMulPosMono.toSMulPosStrictMono [SMulPosMono α β] : SMulPosStrictMono α β :=
⟨fun _b hb _a₁ _a₂ ha => (smul_le_smul_of_nonneg_right ha.le hb.le).lt_of_ne
    (smul_left_injective _ hb.ne').ne ha.ne⟩

/--
lemma `smulPosMono_iff_smulPosStrictMono` / 引理 `smulPosMono_iff_smulPosStrictMono`

English:
lemma smulPosMono_iff_smulPosStrictMono
  statement: SMulPosMono α β ↔ SMulPosStrictMono α β
  proof: ⟨fun _ => SMulPosMono.toSMulPosStrictMono, fun _ => inferInstance⟩

中文:
引理 smulPosMono_iff_smulPosStrictMono
  结论: SMulPosMono α β ↔ SMulPosStrictMono α β
  证明: ⟨fun _ => SMulPosMono.toSMulPosStrictMono, fun _ => inferInstance⟩

Depends on / 依赖: SMulPosMono, SMulPosMono.toSMulPosStrictMono, toSMulPosStrictMono
-/
lemma smulPosMono_iff_smulPosStrictMono : SMulPosMono α β ↔ SMulPosStrictMono α β :=
  ⟨fun _ => SMulPosMono.toSMulPosStrictMono, fun _ => inferInstance⟩

/--
lemma `SMulPosReflectLT.toSMulPosReflectLE` / 引理 `SMulPosReflectLT.toSMulPosReflectLE`

English:
lemma SMulPosReflectLT.toSMulPosReflectLE
  given: [SMulPosReflectLT α β]
  statement: SMulPosReflectLE α β
  proof: ⟨fun _b hb _a₁ _a₂ h => h.eq_or_lt.elim (fun h => (smul_left_injective _ hb.ne' h).le) fun h' =>
    (lt_of_smul_lt_smul_right h' hb.le).le⟩

中文:
引理 SMulPosReflectLT.toSMulPosReflectLE
  条件: [SMulPosReflectLT α β]
  结论: SMulPosReflectLE α β
  证明: ⟨fun _b hb _a₁ _a₂ h => h.eq_or_lt.elim (fun h => (smul_left_injective _ hb.ne' h).le) fun h' =>
    (lt_of_smul_lt_smul_right h' hb.le).le⟩

Depends on / 依赖: eq_or_lt, h.eq_or_lt.elim, hb.le, hb.ne, lt_of_smul_lt_smul_right, smul_left_injective
-/
lemma SMulPosReflectLT.toSMulPosReflectLE [SMulPosReflectLT α β] : SMulPosReflectLE α β :=
  ⟨fun _b hb _a₁ _a₂ h => h.eq_or_lt.elim (fun h => (smul_left_injective _ hb.ne' h).le) fun h' =>
    (lt_of_smul_lt_smul_right h' hb.le).le⟩

/--
lemma `SMulPosReflectLE_iff_smulPosReflectLT` / 引理 `SMulPosReflectLE_iff_smulPosReflectLT`

English:
lemma SMulPosReflectLE_iff_smulPosReflectLT
  statement: SMulPosReflectLE α β ↔ SMulPosReflectLT α β
  proof: ⟨fun _ => inferInstance, fun _ => SMulPosReflectLT.toSMulPosReflectLE⟩

中文:
引理 SMulPosReflectLE_iff_smulPosReflectLT
  结论: SMulPosReflectLE α β ↔ SMulPosReflectLT α β
  证明: ⟨fun _ => inferInstance, fun _ => SMulPosReflectLT.toSMulPosReflectLE⟩

Depends on / 依赖: SMulPosReflectLT, SMulPosReflectLT.toSMulPosReflectLE, toSMulPosReflectLE
-/
lemma SMulPosReflectLE_iff_smulPosReflectLT : SMulPosReflectLE α β ↔ SMulPosReflectLT α β :=
  ⟨fun _ => inferInstance, fun _ => SMulPosReflectLT.toSMulPosReflectLE⟩

end Ring

section GroupWithZero
variable [GroupWithZero α] [Preorder α] [Preorder β] [MulAction α β]

/--
lemma `inv_smul_le_iff_of_pos` / 引理 `inv_smul_le_iff_of_pos`

English:
lemma inv_smul_le_iff_of_pos
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  proof: by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

中文:
引理 inv_smul_le_iff_of_pos
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  证明: by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

Depends on / 依赖: ha.ne, smul_le_smul_iff_of_pos_left
-/
lemma inv_smul_le_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    a⁻¹ • b₁ <= b₂ ↔ b₁ <= a • b₂ := by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

/--
lemma `le_inv_smul_iff_of_pos` / 引理 `le_inv_smul_iff_of_pos`

English:
lemma le_inv_smul_iff_of_pos
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  proof: by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

中文:
引理 le_inv_smul_iff_of_pos
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a)
  证明: by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

Depends on / 依赖: ha.ne, smul_le_smul_iff_of_pos_left
-/
lemma le_inv_smul_iff_of_pos [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) :
    b₁ <= a⁻¹ • b₂ ↔ a • b₁ <= b₂ := by rw [← smul_le_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

/--
lemma `inv_smul_lt_iff_of_pos` / 引理 `inv_smul_lt_iff_of_pos`

English:
lemma inv_smul_lt_iff_of_pos
  given: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  proof: by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

中文:
引理 inv_smul_lt_iff_of_pos
  条件: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  证明: by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

Depends on / 依赖: ha.ne, smul_lt_smul_iff_of_pos_left
-/
lemma inv_smul_lt_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    a⁻¹ • b₁ < b₂ ↔ b₁ < a • b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

/--
lemma `lt_inv_smul_iff_of_pos` / 引理 `lt_inv_smul_iff_of_pos`

English:
lemma lt_inv_smul_iff_of_pos
  given: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  proof: by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

中文:
引理 lt_inv_smul_iff_of_pos
  条件: [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a)
  证明: by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

Depends on / 依赖: ha.ne, smul_lt_smul_iff_of_pos_left
-/
lemma lt_inv_smul_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    b₁ < a⁻¹ • b₂ ↔ a • b₁ < b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

/-- Right scalar multiplication as an order isomorphism. -/
@[simps!]
/--
Definition of `OrderIso.smulRight` / `OrderIso.smulRight` 的定义

English:
definition OrderIso.smulRight
  signature: [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 0 < a)
  body: Equiv.smulRight ha.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos_left ha

中文:
定义 OrderIso.smulRight
  签名: [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 0 < a)
  定义体: Equiv.smulRight ha.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos_left ha

Depends on / 依赖: Equiv.smulRight, ha.ne, smulRight
-/
def OrderIso.smulRight [PosSMulMono α β] [PosSMulReflectLE α β] {a : α} (ha : 0 < a) : β ≃o β where
  toEquiv := Equiv.smulRight ha.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos_left ha

end GroupWithZero

namespace OrderDual

section Left
variable [Preorder α] [Preorder β] [SMul α β] [Zero α]

/--
Instance `instPosSMulMono` / 实例 `instPosSMulMono`

English:
instance instPosSMulMono
  signature: [PosSMulMono α β]
  body: smul_le_smul_of_nonneg_left (β := β) hb ha

中文:
实例 instPosSMulMono
  签名: [PosSMulMono α β]
  定义体: smul_le_smul_of_nonneg_left (β := β) hb ha

Depends on / 依赖: hs.isSMulRegular, isSMulRegular, smul_le_smul_of_nonneg_left, toFinsupp
-/
instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α βᵒᵈ where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb := smul_le_smul_of_nonneg_left (β := β) hb ha
/--
Instance `instPosSMulStrictMono` / 实例 `instPosSMulStrictMono`

English:
instance instPosSMulStrictMono
  signature: [PosSMulStrictMono α β]
  body: smul_lt_smul_of_pos_left (β := β) hb ha

中文:
实例 instPosSMulStrictMono
  签名: [PosSMulStrictMono α β]
  定义体: smul_lt_smul_of_pos_left (β := β) hb ha

Depends on / 依赖: smul_lt_smul_of_pos_left
-/
instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α βᵒᵈ where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb := smul_lt_smul_of_pos_left (β := β) hb ha
/--
Instance `instPosSMulReflectLT` / 实例 `instPosSMulReflectLT`

English:
instance instPosSMulReflectLT
  signature: [PosSMulReflectLT α β]
  body: lt_of_smul_lt_smul_of_nonneg_left (β := β) h ha

中文:
实例 instPosSMulReflectLT
  签名: [PosSMulReflectLT α β]
  定义体: lt_of_smul_lt_smul_of_nonneg_left (β := β) h ha

Depends on / 依赖: lt_of_smul_lt_smul_of_nonneg_left
-/
instance instPosSMulReflectLT [PosSMulReflectLT α β] : PosSMulReflectLT α βᵒᵈ where
  lt_of_smul_lt_smul_left _a ha _b₁ _b₂ h := lt_of_smul_lt_smul_of_nonneg_left (β := β) h ha
/--
Instance `instPosSMulReflectLE` / 实例 `instPosSMulReflectLE`

English:
instance instPosSMulReflectLE
  signature: [PosSMulReflectLE α β]
  body: le_of_smul_le_smul_of_pos_left (β := β) h ha

中文:
实例 instPosSMulReflectLE
  签名: [PosSMulReflectLE α β]
  定义体: le_of_smul_le_smul_of_pos_left (β := β) h ha

Depends on / 依赖: le_of_smul_le_smul_of_pos_left
-/
instance instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α βᵒᵈ where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h := le_of_smul_le_smul_of_pos_left (β := β) h ha

end Left

section Right
variable [Preorder α] [Monoid α] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [DistribMulAction α β]

/--
Instance `instSMulPosMono` / 实例 `instSMulPosMono`

English:
instance instSMulPosMono
  signature: [SMulPosMono α β]
  body: by
    rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
exact smul_le_smul_of_nonneg_right (β := β) ha neg_nonneg.2 hb

中文:
实例 instSMulPosMono
  签名: [SMulPosMono α β]
  定义体: by
    rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
exact smul_le_smul_of_nonneg_right (β := β) ha neg_nonneg.2 hb

Depends on / 依赖: neg_le_neg_iff, neg_nonneg, smul_le_smul_of_nonneg_right, smul_neg
-/
instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α βᵒᵈ where
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ ha := by
    rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
exact smul_le_smul_of_nonneg_right (β := β) ha neg_nonneg.2 hb

/--
Instance `instSMulPosStrictMono` / 实例 `instSMulPosStrictMono`

English:
instance instSMulPosStrictMono
  signature: [SMulPosStrictMono α β]
  body: by
    rw [← neg_lt_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
exact smul_lt_smul_of_pos_right (β := β) ha neg_pos.2 hb

中文:
实例 instSMulPosStrictMono
  签名: [SMulPosStrictMono α β]
  定义体: by
    rw [← neg_lt_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
exact smul_lt_smul_of_pos_right (β := β) ha neg_pos.2 hb

Depends on / 依赖: neg_lt_neg_iff, neg_pos, smul_lt_smul_of_pos_right, smul_neg
-/
instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α βᵒᵈ where
  smul_lt_smul_of_pos_right _b hb a₁ a₂ ha := by
    rw [← neg_lt_neg_iff]; rw [← smul_neg]; rw [← smul_neg]
exact smul_lt_smul_of_pos_right (β := β) ha neg_pos.2 hb

/--
Instance `instSMulPosReflectLT` / 实例 `instSMulPosReflectLT`

English:
instance instSMulPosReflectLT
  signature: [SMulPosReflectLT α β]
  body: by
    rw [← neg_lt_neg_iff]; rw [← smul_neg]; rw [← smul_neg] at h
exact lt_of_smul_lt_smul_right (β := β) h neg_nonneg.2 hb

中文:
实例 instSMulPosReflectLT
  签名: [SMulPosReflectLT α β]
  定义体: by
    rw [← neg_lt_neg_iff]; rw [← smul_neg]; rw [← smul_neg] at h
exact lt_of_smul_lt_smul_right (β := β) h neg_nonneg.2 hb

Depends on / 依赖: lt_of_smul_lt_smul_right, neg_lt_neg_iff, neg_nonneg, smul_neg
-/
instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α βᵒᵈ where
  lt_of_smul_lt_smul_right _b hb a₁ a₂ h := by
    rw [← neg_lt_neg_iff]; rw [← smul_neg]; rw [← smul_neg] at h
exact lt_of_smul_lt_smul_right (β := β) h neg_nonneg.2 hb

/--
Instance `instSMulPosReflectLE` / 实例 `instSMulPosReflectLE`

English:
instance instSMulPosReflectLE
  signature: [SMulPosReflectLE α β]
  body: by
    rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg] at h
exact le_of_smul_le_smul_right (β := β) h neg_pos.2 hb

中文:
实例 instSMulPosReflectLE
  签名: [SMulPosReflectLE α β]
  定义体: by
    rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg] at h
exact le_of_smul_le_smul_right (β := β) h neg_pos.2 hb

Depends on / 依赖: le_of_smul_le_smul_right, neg_le_neg_iff, neg_pos, smul_neg
-/
instance instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α βᵒᵈ where
  le_of_smul_le_smul_right _b hb a₁ a₂ h := by
    rw [← neg_le_neg_iff]; rw [← smul_neg]; rw [← smul_neg] at h
exact le_of_smul_le_smul_right (β := β) h neg_pos.2 hb

end Right

section LeftRight
variable [Preorder α] [MonoidWithZero α] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [DistribMulAction α β]

/--
Instance `instIsOrderedModule` / 实例 `instIsOrderedModule`

English:
instance instIsOrderedModule
  signature: [IsOrderedModule α β]

中文:
实例 instIsOrderedModule
  签名: [IsOrderedModule α β]
-/
instance instIsOrderedModule [IsOrderedModule α β] : IsOrderedModule α βᵒᵈ where
/--
Instance `instIsStrictOrderedModule` / 实例 `instIsStrictOrderedModule`

English:
instance instIsStrictOrderedModule
  signature: [IsStrictOrderedModule α β]

中文:
实例 instIsStrictOrderedModule
  签名: [IsStrictOrderedModule α β]
-/
instance instIsStrictOrderedModule [IsStrictOrderedModule α β] : IsStrictOrderedModule α βᵒᵈ where

end LeftRight
end OrderDual

section OrderedAddCommMonoid
variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

section PosSMulMono
variable [PosSMulMono α β] {a₁ a₂ : α} {b₁ b₂ : β}

/--
lemma `smul_add_smul_le_smul_add_smul` / 引理 `smul_add_smul_le_smul_add_smul`

English:
lemma smul_add_smul_le_smul_add_smul
  given: (ha : a₁ <= a₂) (hb : b₁ <= b₂)
  proof: by
  obtain ⟨a, ha₀, rfl⟩ := exists_nonneg_add_of_le ha
  rw [add_smul]; rw [add_smul]; rw [add_left_comm]
  gcongr

中文:
引理 smul_add_smul_le_smul_add_smul
  条件: (ha : a₁ <= a₂) (hb : b₁ <= b₂)
  证明: by
  obtain ⟨a, ha₀, rfl⟩ := exists_nonneg_add_of_le ha
  rw [add_smul]; rw [add_smul]; rw [add_left_comm]
  gcongr

Depends on / 依赖: add_left_comm, add_smul, exists_nonneg_add_of_le
-/
lemma smul_add_smul_le_smul_add_smul (ha : a₁ <= a₂) (hb : b₁ <= b₂) :
    a₁ • b₂ + a₂ • b₁ <= a₁ • b₁ + a₂ • b₂ := by
  obtain ⟨a, ha₀, rfl⟩ := exists_nonneg_add_of_le ha
  rw [add_smul]; rw [add_smul]; rw [add_left_comm]
  gcongr

/--
lemma `smul_add_smul_le_smul_add_smul'` / 引理 `smul_add_smul_le_smul_add_smul'`

English:
lemma smul_add_smul_le_smul_add_smul'
  given: (ha : a₂ <= a₁) (hb : b₂ <= b₁)
  proof: by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_le_smul_add_smul ha hb

中文:
引理 smul_add_smul_le_smul_add_smul'
  条件: (ha : a₂ <= a₁) (hb : b₂ <= b₁)
  证明: by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_le_smul_add_smul ha hb

Depends on / 依赖: add_comm, simp_rw, smul_add_smul_le_smul_add_smul
-/
lemma smul_add_smul_le_smul_add_smul' (ha : a₂ <= a₁) (hb : b₂ <= b₁) :
    a₁ • b₂ + a₂ • b₁ <= a₁ • b₁ + a₂ • b₂ := by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_le_smul_add_smul ha hb

end PosSMulMono

section PosSMulStrictMono
variable [PosSMulStrictMono α β] {a₁ a₂ : α} {b₁ b₂ : β}

/--
lemma `smul_add_smul_lt_smul_add_smul` / 引理 `smul_add_smul_lt_smul_add_smul`

English:
lemma smul_add_smul_lt_smul_add_smul
  given: (ha : a₁ < a₂) (hb : b₁ < b₂)
  proof: by
  obtain ⟨a, ha₀, rfl⟩ := lt_iff_exists_pos_add.1 ha
  rw [add_smul]; rw [add_smul]; rw [add_left_comm]
  gcongr

中文:
引理 smul_add_smul_lt_smul_add_smul
  条件: (ha : a₁ < a₂) (hb : b₁ < b₂)
  证明: by
  obtain ⟨a, ha₀, rfl⟩ := lt_iff_exists_pos_add.1 ha
  rw [add_smul]; rw [add_smul]; rw [add_left_comm]
  gcongr

Depends on / 依赖: add_left_comm, add_smul, lt_iff_exists_pos_add
-/
lemma smul_add_smul_lt_smul_add_smul (ha : a₁ < a₂) (hb : b₁ < b₂) :
    a₁ • b₂ + a₂ • b₁ < a₁ • b₁ + a₂ • b₂ := by
  obtain ⟨a, ha₀, rfl⟩ := lt_iff_exists_pos_add.1 ha
  rw [add_smul]; rw [add_smul]; rw [add_left_comm]
  gcongr

/--
lemma `smul_add_smul_lt_smul_add_smul'` / 引理 `smul_add_smul_lt_smul_add_smul'`

English:
lemma smul_add_smul_lt_smul_add_smul'
  given: (ha : a₂ < a₁) (hb : b₂ < b₁)
  proof: by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_lt_smul_add_smul ha hb

中文:
引理 smul_add_smul_lt_smul_add_smul'
  条件: (ha : a₂ < a₁) (hb : b₂ < b₁)
  证明: by
  simp_rw [add_comm (a₁ • _)]; exact smul_add_smul_lt_smul_add_smul ha hb

Depends on / 依赖: add_comm, simp_rw, smul_add_smul_lt_smul_add_smul
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

/--
lemma `smul_le_smul_of_nonpos_left` / 引理 `smul_le_smul_of_nonpos_left`

English:
lemma smul_le_smul_of_nonpos_left
  given: (h : b₁ <= b₂) (ha : a <= 0)
  statement: a • b₂ <= a • b₁
  proof: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff]
  exact smul_le_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

中文:
引理 smul_le_smul_of_nonpos_left
  条件: (h : b₁ <= b₂) (ha : a <= 0)
  结论: a • b₂ <= a • b₁
  证明: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff]
  exact smul_le_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

Depends on / 依赖: neg_le_neg_iff, neg_neg, neg_nonneg_of_nonpos, neg_smul, smul_le_smul_of_nonneg_left
-/
lemma smul_le_smul_of_nonpos_left (h : b₁ <= b₂) (ha : a <= 0) : a • b₂ <= a • b₁ := by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff]
  exact smul_le_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

/--
lemma `antitone_smul_left` / 引理 `antitone_smul_left`

English:
lemma antitone_smul_left
  given: (ha : a <= 0)
  statement: Antitone ((a • ·) : β -> β)
  proof: fun _ _ h => smul_le_smul_of_nonpos_left h ha

中文:
引理 antitone_smul_left
  条件: (ha : a <= 0)
  结论: Antitone ((a • ·) : β -> β)
  证明: fun _ _ h => smul_le_smul_of_nonpos_left h ha

Depends on / 依赖: smul_le_smul_of_nonpos_left
-/
lemma antitone_smul_left (ha : a <= 0) : Antitone ((a • ·) : β -> β) :=
  fun _ _ h => smul_le_smul_of_nonpos_left h ha

/--
Instance `PosSMulMono.toSMulPosMono` / 实例 `PosSMulMono.toSMulPosMono`

English:
instance PosSMulMono.toSMulPosMono
  signature: : SMulPosMono α β where
  body: by
    rw [← sub_nonneg]; rw [← sub_smul]; exact smul_nonneg (sub_nonneg.2 ha) hb

中文:
实例 PosSMulMono.toSMulPosMono
  签名: : SMulPosMono α β where
  定义体: by
    rw [← sub_nonneg]; rw [← sub_smul]; exact smul_nonneg (sub_nonneg.2 ha) hb

Depends on / 依赖: smul_nonneg, sub_nonneg, sub_smul
-/
instance PosSMulMono.toSMulPosMono : SMulPosMono α β where
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ ha := by
    rw [← sub_nonneg]; rw [← sub_smul]; exact smul_nonneg (sub_nonneg.2 ha) hb

end PosSMulMono

section PosSMulStrictMono
variable [PosSMulStrictMono α β]

/--
lemma `smul_lt_smul_of_neg_left` / 引理 `smul_lt_smul_of_neg_left`

English:
lemma smul_lt_smul_of_neg_left
  given: (hb : b₁ < b₂) (ha : a < 0)
  statement: a • b₂ < a • b₁
  proof: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff]
  exact smul_lt_smul_of_pos_left hb (neg_pos_of_neg ha)

中文:
引理 smul_lt_smul_of_neg_left
  条件: (hb : b₁ < b₂) (ha : a < 0)
  结论: a • b₂ < a • b₁
  证明: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff]
  exact smul_lt_smul_of_pos_left hb (neg_pos_of_neg ha)

Depends on / 依赖: neg_lt_neg_iff, neg_neg, neg_pos_of_neg, neg_smul, smul_lt_smul_of_pos_left
-/
lemma smul_lt_smul_of_neg_left (hb : b₁ < b₂) (ha : a < 0) : a • b₂ < a • b₁ := by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff]
  exact smul_lt_smul_of_pos_left hb (neg_pos_of_neg ha)

/--
lemma `strictAnti_smul_left` / 引理 `strictAnti_smul_left`

English:
lemma strictAnti_smul_left
  given: (ha : a < 0)
  statement: StrictAnti ((a • ·) : β -> β)
  proof: fun _ _ h => smul_lt_smul_of_neg_left h ha

中文:
引理 strictAnti_smul_left
  条件: (ha : a < 0)
  结论: StrictAnti ((a • ·) : β -> β)
  证明: fun _ _ h => smul_lt_smul_of_neg_left h ha

Depends on / 依赖: smul_lt_smul_of_neg_left
-/
lemma strictAnti_smul_left (ha : a < 0) : StrictAnti ((a • ·) : β -> β) :=
  fun _ _ h => smul_lt_smul_of_neg_left h ha

/--
Instance `PosSMulStrictMono.toSMulPosStrictMono` / 实例 `PosSMulStrictMono.toSMulPosStrictMono`

English:
instance PosSMulStrictMono.toSMulPosStrictMono
  signature: : SMulPosStrictMono α β where
  body: by
    rw [← sub_pos]; rw [← sub_smul]; exact smul_pos (sub_pos.2 ha) hb

中文:
实例 PosSMulStrictMono.toSMulPosStrictMono
  签名: : SMulPosStrictMono α β where
  定义体: by
    rw [← sub_pos]; rw [← sub_smul]; exact smul_pos (sub_pos.2 ha) hb

Depends on / 依赖: smul_pos, sub_pos, sub_smul
-/
instance PosSMulStrictMono.toSMulPosStrictMono : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right _b hb a₁ a₂ ha := by
    rw [← sub_pos]; rw [← sub_smul]; exact smul_pos (sub_pos.2 ha) hb

end PosSMulStrictMono

/--
lemma `le_of_smul_le_smul_of_neg` / 引理 `le_of_smul_le_smul_of_neg`

English:
lemma le_of_smul_le_smul_of_neg
  given: [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha : a < 0)
  proof: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff] at h
exact le_of_smul_le_smul_of_pos_left h neg_pos.2 ha

中文:
引理 le_of_smul_le_smul_of_neg
  条件: [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha : a < 0)
  证明: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff] at h
exact le_of_smul_le_smul_of_pos_left h neg_pos.2 ha

Depends on / 依赖: le_of_smul_le_smul_of_pos_left, neg_le_neg_iff, neg_neg, neg_pos, neg_smul
-/
lemma le_of_smul_le_smul_of_neg [PosSMulReflectLE α β] (h : a • b₁ <= a • b₂) (ha : a < 0) :
    b₂ <= b₁ := by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff] at h
exact le_of_smul_le_smul_of_pos_left h neg_pos.2 ha

/--
lemma `lt_of_smul_lt_smul_of_nonpos` / 引理 `lt_of_smul_lt_smul_of_nonpos`

English:
lemma lt_of_smul_lt_smul_of_nonpos
  given: [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : a <= 0)
  proof: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

omit [IsOrderedRing α] in

中文:
引理 lt_of_smul_lt_smul_of_nonpos
  条件: [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : a <= 0)
  证明: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

omit [IsOrderedRing α] in

Depends on / 依赖: lt_of_smul_lt_smul_of_nonneg_left, neg_lt_neg_iff, neg_neg, neg_nonneg_of_nonpos, neg_smul
-/
lemma lt_of_smul_lt_smul_of_nonpos [PosSMulReflectLT α β] (h : a • b₁ < a • b₂) (ha : a <= 0) :
    b₂ < b₁ := by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg_left h (neg_nonneg_of_nonpos ha)

omit [IsOrderedRing α] in
/--
lemma `smul_nonneg_of_nonpos_of_nonpos` / 引理 `smul_nonneg_of_nonpos_of_nonpos`

English:
lemma smul_nonneg_of_nonpos_of_nonpos
  given: [SMulPosMono α β] (ha : a <= 0) (hb : b <= 0)
  statement: 0 <= a • b
  proof: smul_nonpos_of_nonpos_of_nonneg (β := βᵒᵈ) ha hb

中文:
引理 smul_nonneg_of_nonpos_of_nonpos
  条件: [SMulPosMono α β] (ha : a <= 0) (hb : b <= 0)
  结论: 0 <= a • b
  证明: smul_nonpos_of_nonpos_of_nonneg (β := βᵒᵈ) ha hb

Depends on / 依赖: smul_nonpos_of_nonpos_of_nonneg
-/
lemma smul_nonneg_of_nonpos_of_nonpos [SMulPosMono α β] (ha : a <= 0) (hb : b <= 0) : 0 <= a • b :=
  smul_nonpos_of_nonpos_of_nonneg (β := βᵒᵈ) ha hb

/--
lemma `smul_le_smul_iff_of_neg_left` / 引理 `smul_le_smul_iff_of_neg_left`

English:
lemma smul_le_smul_iff_of_neg_left
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : a < 0)
  proof: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos_left (neg_pos_of_neg ha)

中文:
引理 smul_le_smul_iff_of_neg_left
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : a < 0)
  证明: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos_left (neg_pos_of_neg ha)

Depends on / 依赖: neg_le_neg_iff, neg_neg, neg_pos_of_neg, neg_smul, smul_le_smul_iff_of_pos_left
-/
lemma smul_le_smul_iff_of_neg_left [PosSMulMono α β] [PosSMulReflectLE α β] (ha : a < 0) :
    a • b₁ <= a • b₂ ↔ b₂ <= b₁ := by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos_left (neg_pos_of_neg ha)

section PosSMulStrictMono
variable [PosSMulStrictMono α β] [PosSMulReflectLT α β]

/--
lemma `smul_lt_smul_iff_of_neg_left` / 引理 `smul_lt_smul_iff_of_neg_left`

English:
lemma smul_lt_smul_iff_of_neg_left
  given: (ha : a < 0)
  statement: a • b₁ < a • b₂ ↔ b₂ < b₁
  proof: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos_left (neg_pos_of_neg ha)

中文:
引理 smul_lt_smul_iff_of_neg_left
  条件: (ha : a < 0)
  结论: a • b₁ < a • b₂ ↔ b₂ < b₁
  证明: by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos_left (neg_pos_of_neg ha)

Depends on / 依赖: neg_lt_neg_iff, neg_neg, neg_pos_of_neg, neg_smul, smul_lt_smul_iff_of_pos_left
-/
lemma smul_lt_smul_iff_of_neg_left (ha : a < 0) : a • b₁ < a • b₂ ↔ b₂ < b₁ := by
  rw [← neg_neg a]; rw [neg_smul]; rw [neg_smul (-a)]; rw [neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos_left (neg_pos_of_neg ha)

/--
lemma `smul_pos_iff_of_neg_left` / 引理 `smul_pos_iff_of_neg_left`

English:
lemma smul_pos_iff_of_neg_left
  given: (ha : a < 0)
  statement: 0 < a • b ↔ b < 0
  proof: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₁ := (0 : β))

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg_left

中文:
引理 smul_pos_iff_of_neg_left
  条件: (ha : a < 0)
  结论: 0 < a • b ↔ b < 0
  证明: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₁ := (0 : β))

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg_left

Depends on / 依赖: smul_lt_smul_iff_of_neg_left, smul_zero
-/
lemma smul_pos_iff_of_neg_left (ha : a < 0) : 0 < a • b ↔ b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₁ := (0 : β))

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg_left

/--
lemma `smul_neg_iff_of_neg_left` / 引理 `smul_neg_iff_of_neg_left`

English:
lemma smul_neg_iff_of_neg_left
  given: (ha : a < 0)
  statement: a • b < 0 ↔ 0 < b
  proof: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₂ := (0 : β))

中文:
引理 smul_neg_iff_of_neg_left
  条件: (ha : a < 0)
  结论: a • b < 0 ↔ 0 < b
  证明: by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₂ := (0 : β))

Depends on / 依赖: smul_lt_smul_iff_of_neg_left, smul_zero
-/
lemma smul_neg_iff_of_neg_left (ha : a < 0) : a • b < 0 ↔ 0 < b := by
  simpa only [smul_zero] using smul_lt_smul_iff_of_neg_left ha (b₂ := (0 : β))

end PosSMulStrictMono
end OrderedAddCommGroup

section LinearOrderedAddCommGroup
variable [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulMono α β]
  {a : α} {b b₁ b₂ : β}

/--
lemma `smul_max_of_nonpos` / 引理 `smul_max_of_nonpos`

English:
lemma smul_max_of_nonpos
  given: (ha : a <= 0) (b₁ b₂ : β)
  statement: a • max b₁ b₂ = min (a • b₁) (a • b₂)
  proof: (antitone_smul_left ha : Antitone (_ : β -> β)).map_max

中文:
引理 smul_max_of_nonpos
  条件: (ha : a <= 0) (b₁ b₂ : β)
  结论: a • max b₁ b₂ = min (a • b₁) (a • b₂)
  证明: (antitone_smul_left ha : Antitone (_ : β -> β)).map_max

Depends on / 依赖: Antitone, antitone_smul_left, map_max
-/
lemma smul_max_of_nonpos (ha : a <= 0) (b₁ b₂ : β) : a • max b₁ b₂ = min (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : β -> β)).map_max

/--
lemma `smul_min_of_nonpos` / 引理 `smul_min_of_nonpos`

English:
lemma smul_min_of_nonpos
  given: (ha : a <= 0) (b₁ b₂ : β)
  statement: a • min b₁ b₂ = max (a • b₁) (a • b₂)
  proof: (antitone_smul_left ha : Antitone (_ : β -> β)).map_min

中文:
引理 smul_min_of_nonpos
  条件: (ha : a <= 0) (b₁ b₂ : β)
  结论: a • min b₁ b₂ = max (a • b₁) (a • b₂)
  证明: (antitone_smul_left ha : Antitone (_ : β -> β)).map_min

Depends on / 依赖: Antitone, antitone_smul_left, map_min
-/
lemma smul_min_of_nonpos (ha : a <= 0) (b₁ b₂ : β) : a • min b₁ b₂ = max (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : β -> β)).map_min

end LinearOrderedAddCommGroup
end OrderedRing

section LinearOrderedRing
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulStrictMono α β]
  {a : α} {b : β}

/--
lemma `nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg` / 引理 `nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg`

English:
lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg
  given: (hab : 0 <= a • b)
  proof: by
  simp only [Decidable.or_iff_not_not_and_not, not_and, not_le]
  refine fun ab nab => hab.not_gt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

中文:
引理 nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg
  条件: (hab : 0 <= a • b)
  证明: by
  simp only [Decidable.or_iff_not_not_and_not, not_and, not_le]
  refine fun ab nab => hab.not_gt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

Depends on / 依赖: Decidable, Decidable.or_iff_not_not_and_not, exacts, ha.le, hab.not_gt, le_rfl, lt_trichotomy, not_and, not_gt, not_le, or_iff_not_not_and_not, smul_neg_of_neg_of_pos, smul_neg_of_pos_of_neg
-/
lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 <= a • b) :
    0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 := by
  simp only [Decidable.or_iff_not_not_and_not, not_and, not_le]
  refine fun ab nab => hab.not_gt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

/--
lemma `smul_nonneg_iff` / 引理 `smul_nonneg_iff`

English:
lemma smul_nonneg_iff
  statement: 0 <= a • b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  proof: ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h => h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

中文:
引理 smul_nonneg_iff
  结论: 0 <= a • b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  证明: ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h => h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

Depends on / 依赖: and_imp, h.elim, nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg, smul_nonneg, smul_nonneg_of_nonpos_of_nonpos
-/
lemma smul_nonneg_iff : 0 <= a • b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h => h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

/--
lemma `smul_nonpos_iff` / 引理 `smul_nonpos_iff`

English:
lemma smul_nonpos_iff
  statement: a • b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  proof: by
  rw [← neg_nonneg]; rw [← smul_neg]; rw [smul_nonneg_iff]; rw [neg_nonneg]; rw [neg_nonpos]

中文:
引理 smul_nonpos_iff
  结论: a • b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  证明: by
  rw [← neg_nonneg]; rw [← smul_neg]; rw [smul_nonneg_iff]; rw [neg_nonneg]; rw [neg_nonpos]

Depends on / 依赖: neg_nonneg, neg_nonpos, smul_neg, smul_nonneg_iff
-/
lemma smul_nonpos_iff : a • b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b := by
  rw [← neg_nonneg]; rw [← smul_neg]; rw [smul_nonneg_iff]; rw [neg_nonneg]; rw [neg_nonpos]

/--
lemma `smul_nonneg_iff_pos_imp_nonneg` / 引理 `smul_nonneg_iff_pos_imp_nonneg`

English:
lemma smul_nonneg_iff_pos_imp_nonneg
  statement: 0 <= a • b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a)
  proof: smul_nonneg_iff.trans by grind

中文:
引理 smul_nonneg_iff_pos_imp_nonneg
  结论: 0 <= a • b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a)
  证明: smul_nonneg_iff.trans by grind

Depends on / 依赖: smul_nonneg_iff, smul_nonneg_iff.trans
-/
lemma smul_nonneg_iff_pos_imp_nonneg : 0 <= a • b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a) :=
smul_nonneg_iff.trans by grind

/--
lemma `smul_nonneg_iff_neg_imp_nonpos` / 引理 `smul_nonneg_iff_neg_imp_nonpos`

English:
lemma smul_nonneg_iff_neg_imp_nonpos
  statement: 0 <= a • b ↔ (a < 0 -> b <= 0) ∧ (b < 0 -> a <= 0)
  proof: by
  rw [← neg_smul_neg]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

中文:
引理 smul_nonneg_iff_neg_imp_nonpos
  结论: 0 <= a • b ↔ (a < 0 -> b <= 0) ∧ (b < 0 -> a <= 0)
  证明: by
  rw [← neg_smul_neg]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

Depends on / 依赖: neg_nonneg, neg_pos, neg_smul_neg, smul_nonneg_iff_pos_imp_nonneg
-/
lemma smul_nonneg_iff_neg_imp_nonpos : 0 <= a • b ↔ (a < 0 -> b <= 0) ∧ (b < 0 -> a <= 0) := by
  rw [← neg_smul_neg]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

/--
lemma `smul_nonpos_iff_pos_imp_nonpos` / 引理 `smul_nonpos_iff_pos_imp_nonpos`

English:
lemma smul_nonpos_iff_pos_imp_nonpos
  statement: a • b <= 0 ↔ (0 < a -> b <= 0) ∧ (b < 0 -> 0 <= a)
  proof: by
  rw [← neg_nonneg]; rw [← smul_neg]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

中文:
引理 smul_nonpos_iff_pos_imp_nonpos
  结论: a • b <= 0 ↔ (0 < a -> b <= 0) ∧ (b < 0 -> 0 <= a)
  证明: by
  rw [← neg_nonneg]; rw [← smul_neg]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

Depends on / 依赖: neg_nonneg, neg_pos, smul_neg, smul_nonneg_iff_pos_imp_nonneg
-/
lemma smul_nonpos_iff_pos_imp_nonpos : a • b <= 0 ↔ (0 < a -> b <= 0) ∧ (b < 0 -> 0 <= a) := by
  rw [← neg_nonneg]; rw [← smul_neg]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

/--
lemma `smul_nonpos_iff_neg_imp_nonneg` / 引理 `smul_nonpos_iff_neg_imp_nonneg`

English:
lemma smul_nonpos_iff_neg_imp_nonneg
  statement: a • b <= 0 ↔ (a < 0 -> 0 <= b) ∧ (0 < b -> a <= 0)
  proof: by
  rw [← neg_nonneg]; rw [← neg_smul]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

中文:
引理 smul_nonpos_iff_neg_imp_nonneg
  结论: a • b <= 0 ↔ (a < 0 -> 0 <= b) ∧ (0 < b -> a <= 0)
  证明: by
  rw [← neg_nonneg]; rw [← neg_smul]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

Depends on / 依赖: neg_nonneg, neg_pos, neg_smul, smul_nonneg_iff_pos_imp_nonneg
-/
lemma smul_nonpos_iff_neg_imp_nonneg : a • b <= 0 ↔ (a < 0 -> 0 <= b) ∧ (0 < b -> a <= 0) := by
  rw [← neg_nonneg]; rw [← neg_smul]; rw [smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end LinearOrderedRing

namespace Prod
variable {γ : Type*} [Zero α]

section SMul
variable [Preorder α] [Preorder β] [Preorder γ] [SMul α β] [SMul α γ]

/--
Instance `instPosSMulMono` / 实例 `instPosSMulMono`

English:
instance instPosSMulMono
  signature: [PosSMulMono α β] [PosSMulMono α γ]
  body: ⟨smul_le_smul_of_nonneg_left hb.1 ha, smul_le_smul_of_nonneg_left hb.2 ha⟩

中文:
实例 instPosSMulMono
  签名: [PosSMulMono α β] [PosSMulMono α γ]
  定义体: ⟨smul_le_smul_of_nonneg_left hb.1 ha, smul_le_smul_of_nonneg_left hb.2 ha⟩

Depends on / 依赖: smul_le_smul_of_nonneg_left
-/
instance instPosSMulMono [PosSMulMono α β] [PosSMulMono α γ] : PosSMulMono α (β × γ) where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb :=
    ⟨smul_le_smul_of_nonneg_left hb.1 ha, smul_le_smul_of_nonneg_left hb.2 ha⟩

/--
Instance `instPosSMulReflectLE` / 实例 `instPosSMulReflectLE`

English:
instance instPosSMulReflectLE
  signature: [PosSMulReflectLE α β] [PosSMulReflectLE α γ]
  body: ⟨le_of_smul_le_smul_left h.1 ha, le_of_smul_le_smul_left h.2 ha⟩

中文:
实例 instPosSMulReflectLE
  签名: [PosSMulReflectLE α β] [PosSMulReflectLE α γ]
  定义体: ⟨le_of_smul_le_smul_left h.1 ha, le_of_smul_le_smul_left h.2 ha⟩

Depends on / 依赖: le_of_smul_le_smul_left
-/
instance instPosSMulReflectLE [PosSMulReflectLE α β] [PosSMulReflectLE α γ] :
    PosSMulReflectLE α (β × γ) where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h :=
    ⟨le_of_smul_le_smul_left h.1 ha, le_of_smul_le_smul_left h.2 ha⟩

variable [Zero β] [Zero γ]

/--
Instance `instSMulPosMono` / 实例 `instSMulPosMono`

English:
instance instSMulPosMono
  signature: [SMulPosMono α β] [SMulPosMono α γ]
  body: ⟨smul_le_smul_of_nonneg_right ha hb.1, smul_le_smul_of_nonneg_right ha hb.2⟩

中文:
实例 instSMulPosMono
  签名: [SMulPosMono α β] [SMulPosMono α γ]
  定义体: ⟨smul_le_smul_of_nonneg_right ha hb.1, smul_le_smul_of_nonneg_right ha hb.2⟩

Depends on / 依赖: smul_le_smul_of_nonneg_right
-/
instance instSMulPosMono [SMulPosMono α β] [SMulPosMono α γ] : SMulPosMono α (β × γ) where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha :=
    ⟨smul_le_smul_of_nonneg_right ha hb.1, smul_le_smul_of_nonneg_right ha hb.2⟩

/--
Instance `instSMulPosReflectLE` / 实例 `instSMulPosReflectLE`

English:
instance instSMulPosReflectLE
  signature: [SMulPosReflectLE α β] [SMulPosReflectLE α γ]
  body: by
    rcases lt_iff.mp hb with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · exact le_of_smul_le_smul_right h.1 h₁
    · exact le_of_smul_le_smul_right h.2 h₁

中文:
实例 instSMulPosReflectLE
  签名: [SMulPosReflectLE α β] [SMulPosReflectLE α γ]
  定义体: by
    rcases lt_iff.mp hb with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · exact le_of_smul_le_smul_right h.1 h₁
    · exact le_of_smul_le_smul_right h.2 h₁

Depends on / 依赖: le_of_smul_le_smul_right, lt_iff, lt_iff.mp
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

/--
Instance `instPosSMulStrictMono` / 实例 `instPosSMulStrictMono`

English:
instance instPosSMulStrictMono
  signature: [PosSMulStrictMono α β] [PosSMulStrictMono α γ]
  body: by
    simp_rw [lt_iff]
    rintro _a ha _b₁ _b₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact .inl ⟨smul_lt_smul_of_pos_left h₁ ha, smul_le_smul_of_nonneg_left h₂ ha.le⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_left h₁ ha.le, smul_lt_smul_of_pos_left h₂ ha⟩

中文:
实例 instPosSMulStrictMono
  签名: [PosSMulStrictMono α β] [PosSMulStrictMono α γ]
  定义体: by
    simp_rw [lt_iff]
    rintro _a ha _b₁ _b₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact .inl ⟨smul_lt_smul_of_pos_left h₁ ha, smul_le_smul_of_nonneg_left h₂ ha.le⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_left h₁ ha.le, smul_lt_smul_of_pos_left h₂ ha⟩

Depends on / 依赖: ha.le, lt_iff, simp_rw, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left
-/
instance instPosSMulStrictMono [PosSMulStrictMono α β] [PosSMulStrictMono α γ] :
    PosSMulStrictMono α (β × γ) where
  smul_lt_smul_of_pos_left := by
    simp_rw [lt_iff]
    rintro _a ha _b₁ _b₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact .inl ⟨smul_lt_smul_of_pos_left h₁ ha, smul_le_smul_of_nonneg_left h₂ ha.le⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_left h₁ ha.le, smul_lt_smul_of_pos_left h₂ ha⟩

/--
Instance `instSMulPosStrictMono` / 实例 `instSMulPosStrictMono`

English:
instance instSMulPosStrictMono
  signature: [SMulPosStrictMono α β] [SMulPosStrictMono α γ]
  body: by
    simp_rw [lt_iff]
    rintro a (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) _b₁ _b₂ hb
    · exact .inl ⟨smul_lt_smul_of_pos_right hb h₁, smul_le_smul_of_nonneg_right hb.le h₂⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_right hb.le h₁, smul_lt_smul_of_pos_right hb h₂⟩

中文:
实例 instSMulPosStrictMono
  签名: [SMulPosStrictMono α β] [SMulPosStrictMono α γ]
  定义体: by
    simp_rw [lt_iff]
    rintro a (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) _b₁ _b₂ hb
    · exact .inl ⟨smul_lt_smul_of_pos_right hb h₁, smul_le_smul_of_nonneg_right hb.le h₂⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_right hb.le h₁, smul_lt_smul_of_pos_right hb h₂⟩

Depends on / 依赖: hb.le, lt_iff, simp_rw, smul_le_smul_of_nonneg_right, smul_lt_smul_of_pos_right
-/
instance instSMulPosStrictMono [SMulPosStrictMono α β] [SMulPosStrictMono α γ] :
    SMulPosStrictMono α (β × γ) where
  smul_lt_smul_of_pos_right := by
    simp_rw [lt_iff]
    rintro a (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) _b₁ _b₂ hb
    · exact .inl ⟨smul_lt_smul_of_pos_right hb h₁, smul_le_smul_of_nonneg_right hb.le h₂⟩
    · exact .inr ⟨smul_le_smul_of_nonneg_right hb.le h₁, smul_lt_smul_of_pos_right hb h₂⟩

/--
Instance `instSMulPosReflectLT` / 实例 `instSMulPosReflectLT`

English:
instance instSMulPosReflectLT
  signature: [SMulPosReflectLT α β] [SMulPosReflectLT α γ]
  body: by
    simp_rw [lt_iff]
    rintro b hb _a₁ _a₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact lt_of_smul_lt_smul_right h₁ hb.1
    · exact lt_of_smul_lt_smul_right h₂ hb.2

中文:
实例 instSMulPosReflectLT
  签名: [SMulPosReflectLT α β] [SMulPosReflectLT α γ]
  定义体: by
    simp_rw [lt_iff]
    rintro b hb _a₁ _a₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact lt_of_smul_lt_smul_right h₁ hb.1
    · exact lt_of_smul_lt_smul_right h₂ hb.2

Depends on / 依赖: lt_iff, lt_of_smul_lt_smul_right, simp_rw
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
variable {ι : Type*} {β : ι -> Type*} [Zero α]

section SMul
variable [Preorder α] [forall i, Preorder (β i)] [forall i, SMul α (β i)]

/--
Instance `instPosSMulMono` / 实例 `instPosSMulMono`

English:
instance instPosSMulMono
  signature: [forall i, PosSMulMono α (β i)]
  body: smul_le_smul_of_nonneg_left (hb i) ha

中文:
实例 instPosSMulMono
  签名: [对任意 i, PosSMulMono α (β i)]
  定义体: smul_le_smul_of_nonneg_left (hb i) ha

Depends on / 依赖: smul_le_smul_of_nonneg_left
-/
instance instPosSMulMono [forall i, PosSMulMono α (β i)] : PosSMulMono α (forall i, β i) where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb i := smul_le_smul_of_nonneg_left (hb i) ha

/--
Instance `instPosSMulReflectLE` / 实例 `instPosSMulReflectLE`

English:
instance instPosSMulReflectLE
  signature: [forall i, PosSMulReflectLE α (β i)]
  body: le_of_smul_le_smul_left (h i) ha

中文:
实例 instPosSMulReflectLE
  签名: [对任意 i, PosSMulReflectLE α (β i)]
  定义体: le_of_smul_le_smul_left (h i) ha

Depends on / 依赖: le_of_smul_le_smul_left
-/
instance instPosSMulReflectLE [forall i, PosSMulReflectLE α (β i)] : PosSMulReflectLE α (forall i, β i) where
  le_of_smul_le_smul_left _a ha _b₁ _b₂ h i := le_of_smul_le_smul_left (h i) ha

variable [forall i, Zero (β i)]

/--
Instance `instSMulPosMono` / 实例 `instSMulPosMono`

English:
instance instSMulPosMono
  signature: [forall i, SMulPosMono α (β i)]
  body: smul_le_smul_of_nonneg_right ha (hb i)

中文:
实例 instSMulPosMono
  签名: [对任意 i, SMulPosMono α (β i)]
  定义体: smul_le_smul_of_nonneg_right ha (hb i)

Depends on / 依赖: smul_le_smul_of_nonneg_right
-/
instance instSMulPosMono [forall i, SMulPosMono α (β i)] : SMulPosMono α (forall i, β i) where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha i := smul_le_smul_of_nonneg_right ha (hb i)

/--
Instance `instSMulPosReflectLE` / 实例 `instSMulPosReflectLE`

English:
instance instSMulPosReflectLE
  signature: [forall i, SMulPosReflectLE α (β i)]
  body: by
    obtain ⟨-, i, hi⟩ := lt_def.1 hb; exact le_of_smul_le_smul_right (h _) hi

中文:
实例 instSMulPosReflectLE
  签名: [对任意 i, SMulPosReflectLE α (β i)]
  定义体: by
    obtain ⟨-, i, hi⟩ := lt_def.1 hb; exact le_of_smul_le_smul_right (h _) hi

Depends on / 依赖: le_of_smul_le_smul_right, lt_def
-/
instance instSMulPosReflectLE [forall i, SMulPosReflectLE α (β i)] : SMulPosReflectLE α (forall i, β i) where
  le_of_smul_le_smul_right _b hb _a₁ _a₂ h := by
    obtain ⟨-, i, hi⟩ := lt_def.1 hb; exact le_of_smul_le_smul_right (h _) hi

end SMul


section SMulWithZero
variable [forall i, Zero (β i)] [PartialOrder α] [forall i, PartialOrder (β i)] [forall i, SMulWithZero α (β i)]

/--
Instance `instPosSMulStrictMono` / 实例 `instPosSMulStrictMono`

English:
instance instPosSMulStrictMono
  signature: [forall i, PosSMulStrictMono α (β i)]
  body: by
    simp_rw [lt_def]
    rintro _a ha _b₁ _b₂ ⟨hb, i, hi⟩
    exact ⟨smul_le_smul_of_nonneg_left hb ha.le, i, smul_lt_smul_of_pos_left hi ha⟩

中文:
实例 instPosSMulStrictMono
  签名: [对任意 i, PosSMulStrictMono α (β i)]
  定义体: by
    simp_rw [lt_def]
    rintro _a ha _b₁ _b₂ ⟨hb, i, hi⟩
    exact ⟨smul_le_smul_of_nonneg_left hb ha.le, i, smul_lt_smul_of_pos_left hi ha⟩

Depends on / 依赖: ha.le, lt_def, simp_rw, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left
-/
instance instPosSMulStrictMono [forall i, PosSMulStrictMono α (β i)] :
    PosSMulStrictMono α (forall i, β i) where
  smul_lt_smul_of_pos_left := by
    simp_rw [lt_def]
    rintro _a ha _b₁ _b₂ ⟨hb, i, hi⟩
    exact ⟨smul_le_smul_of_nonneg_left hb ha.le, i, smul_lt_smul_of_pos_left hi ha⟩

/--
Instance `instSMulPosStrictMono` / 实例 `instSMulPosStrictMono`

English:
instance instSMulPosStrictMono
  signature: [forall i, SMulPosStrictMono α (β i)]
  body: by
    simp_rw [lt_def]
    rintro a ⟨ha, i, hi⟩ _b₁ _b₂ hb
    exact ⟨smul_le_smul_of_nonneg_right hb.le ha, i, smul_lt_smul_of_pos_right hb hi⟩

中文:
实例 instSMulPosStrictMono
  签名: [对任意 i, SMulPosStrictMono α (β i)]
  定义体: by
    simp_rw [lt_def]
    rintro a ⟨ha, i, hi⟩ _b₁ _b₂ hb
    exact ⟨smul_le_smul_of_nonneg_right hb.le ha, i, smul_lt_smul_of_pos_right hb hi⟩

Depends on / 依赖: hb.le, lt_def, simp_rw, smul_le_smul_of_nonneg_right, smul_lt_smul_of_pos_right
-/
instance instSMulPosStrictMono [forall i, SMulPosStrictMono α (β i)] :
    SMulPosStrictMono α (forall i, β i) where
  smul_lt_smul_of_pos_right := by
    simp_rw [lt_def]
    rintro a ⟨ha, i, hi⟩ _b₁ _b₂ hb
    exact ⟨smul_le_smul_of_nonneg_right hb.le ha, i, smul_lt_smul_of_pos_right hb hi⟩

-- Note: There is no interesting instance for `PosSMulReflectLT α (∀ i, β i)` that's not already
-- implied by the other instances

/--
Instance `instSMulPosReflectLT` / 实例 `instSMulPosReflectLT`

English:
instance instSMulPosReflectLT
  signature: [forall i, SMulPosReflectLT α (β i)]
  body: by
    simp_rw [lt_def]
    rintro b hb _a₁ _a₂ ⟨-, i, hi⟩
exact lt_of_smul_lt_smul_right hi hb _

中文:
实例 instSMulPosReflectLT
  签名: [对任意 i, SMulPosReflectLT α (β i)]
  定义体: by
    simp_rw [lt_def]
    rintro b hb _a₁ _a₂ ⟨-, i, hi⟩
exact lt_of_smul_lt_smul_right hi hb _

Depends on / 依赖: lt_def, lt_of_smul_lt_smul_right, simp_rw
-/
instance instSMulPosReflectLT [forall i, SMulPosReflectLT α (β i)] : SMulPosReflectLT α (forall i, β i) where
  lt_of_smul_lt_smul_right := by
    simp_rw [lt_def]
    rintro b hb _a₁ _a₂ ⟨-, i, hi⟩
exact lt_of_smul_lt_smul_right hi hb _

end SMulWithZero
end Pi

section Lift
variable {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
  [SMul α β] [SMul α γ] (f : β -> γ)

section
variable [Zero α]

/--
lemma `PosSMulMono.lift` / 引理 `PosSMulMono.lift`

English:
lemma PosSMulMono.lift
  statement: [PosSMulMono α γ]
  proof: by
    simp only [← hf, smul] at *; exact smul_le_smul_of_nonneg_left hb ha

中文:
引理 PosSMulMono.lift
  结论: [PosSMulMono α γ]
  证明: by
    simp only [← hf, smul] at *; exact smul_le_smul_of_nonneg_left hb ha

Depends on / 依赖: smul_le_smul_of_nonneg_left
-/
lemma PosSMulMono.lift [PosSMulMono α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulMono α β where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hb := by
    simp only [← hf, smul] at *; exact smul_le_smul_of_nonneg_left hb ha

/--
lemma `PosSMulStrictMono.lift` / 引理 `PosSMulStrictMono.lift`

English:
lemma PosSMulStrictMono.lift
  statement: [PosSMulStrictMono α γ]
  proof: by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact smul_lt_smul_of_pos_left hb ha

中文:
引理 PosSMulStrictMono.lift
  结论: [PosSMulStrictMono α γ]
  证明: by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact smul_lt_smul_of_pos_left hb ha

Depends on / 依赖: lt_iff_lt_of_le_iff_le, smul_lt_smul_of_pos_left
-/
lemma PosSMulStrictMono.lift [PosSMulStrictMono α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulStrictMono α β where
  smul_lt_smul_of_pos_left a ha b₁ b₂ hb := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact smul_lt_smul_of_pos_left hb ha

/--
lemma `PosSMulReflectLE.lift` / 引理 `PosSMulReflectLE.lift`

English:
lemma PosSMulReflectLE.lift
  statement: [PosSMulReflectLE α γ]
  proof: hf.1 le_of_smul_le_smul_left (by simpa only [smul] using hf.2 h) ha

中文:
引理 PosSMulReflectLE.lift
  结论: [PosSMulReflectLE α γ]
  证明: hf.1 le_of_smul_le_smul_left (by simpa only [smul] using hf.2 h) ha

Depends on / 依赖: le_of_smul_le_smul_left
-/
lemma PosSMulReflectLE.lift [PosSMulReflectLE α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulReflectLE α β where
  le_of_smul_le_smul_left a ha b₁ b₂ h :=
hf.1 le_of_smul_le_smul_left (by simpa only [smul] using hf.2 h) ha

/--
lemma `PosSMulReflectLT.lift` / 引理 `PosSMulReflectLT.lift`

English:
lemma PosSMulReflectLT.lift
  statement: [PosSMulReflectLT α γ]
  proof: by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact lt_of_smul_lt_smul_left h ha

中文:
引理 PosSMulReflectLT.lift
  结论: [PosSMulReflectLT α γ]
  证明: by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact lt_of_smul_lt_smul_left h ha

Depends on / 依赖: lt_iff_lt_of_le_iff_le, lt_of_smul_lt_smul_left
-/
lemma PosSMulReflectLT.lift [PosSMulReflectLT α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b) : PosSMulReflectLT α β where
  lt_of_smul_lt_smul_left a ha b₁ b₂ h := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, smul] at *; exact lt_of_smul_lt_smul_left h ha

end

section
variable [Zero β] [Zero γ]

/--
lemma `SMulPosMono.lift` / 引理 `SMulPosMono.lift`

English:
lemma SMulPosMono.lift
  statement: [SMulPosMono α γ]
  proof: by
    simp only [← hf, zero, smul] at *; exact smul_le_smul_of_nonneg_right ha hb

中文:
引理 SMulPosMono.lift
  结论: [SMulPosMono α γ]
  证明: by
    simp only [← hf, zero, smul] at *; exact smul_le_smul_of_nonneg_right ha hb

Depends on / 依赖: smul_le_smul_of_nonneg_right
-/
lemma SMulPosMono.lift [SMulPosMono α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosMono α β where
  smul_le_smul_of_nonneg_right b hb a₁ a₂ ha := by
    simp only [← hf, zero, smul] at *; exact smul_le_smul_of_nonneg_right ha hb

/--
lemma `SMulPosStrictMono.lift` / 引理 `SMulPosStrictMono.lift`

English:
lemma SMulPosStrictMono.lift
  statement: [SMulPosStrictMono α γ]
  proof: by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact smul_lt_smul_of_pos_right ha hb

中文:
引理 SMulPosStrictMono.lift
  结论: [SMulPosStrictMono α γ]
  证明: by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact smul_lt_smul_of_pos_right ha hb

Depends on / 依赖: lt_iff_lt_of_le_iff_le, smul_lt_smul_of_pos_right
-/
lemma SMulPosStrictMono.lift [SMulPosStrictMono α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right b hb a₁ a₂ ha := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact smul_lt_smul_of_pos_right ha hb

/--
lemma `SMulPosReflectLE.lift` / 引理 `SMulPosReflectLE.lift`

English:
lemma SMulPosReflectLE.lift
  statement: [SMulPosReflectLE α γ]
  proof: by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact le_of_smul_le_smul_right h hb

中文:
引理 SMulPosReflectLE.lift
  结论: [SMulPosReflectLE α γ]
  证明: by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact le_of_smul_le_smul_right h hb

Depends on / 依赖: le_of_smul_le_smul_right, lt_iff_lt_of_le_iff_le
-/
lemma SMulPosReflectLE.lift [SMulPosReflectLE α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosReflectLE α β where
  le_of_smul_le_smul_right b hb a₁ a₂ h := by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact le_of_smul_le_smul_right h hb

/--
lemma `SMulPosReflectLT.lift` / 引理 `SMulPosReflectLT.lift`

English:
lemma SMulPosReflectLT.lift
  statement: [SMulPosReflectLT α γ]
  proof: by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact lt_of_smul_lt_smul_right h hb

中文:
引理 SMulPosReflectLT.lift
  结论: [SMulPosReflectLT α γ]
  证明: by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact lt_of_smul_lt_smul_right h hb

Depends on / 依赖: lt_iff_lt_of_le_iff_le, lt_of_smul_lt_smul_right
-/
lemma SMulPosReflectLT.lift [SMulPosReflectLT α γ]
    (hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂)
    (smul : forall (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right b hb a₁ a₂ h := by
    simp only [← hf, ← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact lt_of_smul_lt_smul_right h hb

end

end Lift

section Nat

/--
Instance `OrderedSemiring.toPosSMulMonoNat` / 实例 `OrderedSemiring.toPosSMulMonoNat`

English:
instance OrderedSemiring.toPosSMulMonoNat
  signature: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  body: nsmul_le_nsmul_right hab _

中文:
实例 OrderedSemiring.toPosSMulMonoNat
  签名: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  定义体: nsmul_le_nsmul_right hab _

Depends on / 依赖: nsmul_le_nsmul_right
-/
instance OrderedSemiring.toPosSMulMonoNat [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    PosSMulMono Nat α where
  smul_le_smul_of_nonneg_left _n _ _a _b hab := nsmul_le_nsmul_right hab _

/--
Instance `OrderedSemiring.toSMulPosMonoNat` / 实例 `OrderedSemiring.toSMulPosMonoNat`

English:
instance OrderedSemiring.toSMulPosMonoNat
  signature: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  body: nsmul_le_nsmul_left ha hmn

中文:
实例 OrderedSemiring.toSMulPosMonoNat
  签名: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  定义体: nsmul_le_nsmul_left ha hmn

Depends on / 依赖: nsmul_le_nsmul_left
-/
instance OrderedSemiring.toSMulPosMonoNat [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    SMulPosMono Nat α where
  smul_le_smul_of_nonneg_right _a ha _m _n hmn := nsmul_le_nsmul_left ha hmn

/--
Instance `StrictOrderedSemiring.toPosSMulStrictMonoNat` / 实例 `StrictOrderedSemiring.toPosSMulStrictMonoNat`

English:
instance StrictOrderedSemiring.toPosSMulStrictMonoNat
  body: nsmul_right_strictMono hn.ne' hab

中文:
实例 StrictOrderedSemiring.toPosSMulStrictMonoNat
  定义体: nsmul_right_strictMono hn.ne' hab

Depends on / 依赖: hn.ne, nsmul_right_strictMono
-/
instance StrictOrderedSemiring.toPosSMulStrictMonoNat
    [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    PosSMulStrictMono Nat α where
  smul_lt_smul_of_pos_left _n hn _a _b hab := nsmul_right_strictMono hn.ne' hab

/--
Instance `StrictOrderedSemiring.toSMulPosStrictMonoNat` / 实例 `StrictOrderedSemiring.toSMulPosStrictMonoNat`

English:
instance StrictOrderedSemiring.toSMulPosStrictMonoNat
  body: nsmul_lt_nsmul_left ha hmn

中文:
实例 StrictOrderedSemiring.toSMulPosStrictMonoNat
  定义体: nsmul_lt_nsmul_left ha hmn

Depends on / 依赖: nsmul_lt_nsmul_left
-/
instance StrictOrderedSemiring.toSMulPosStrictMonoNat
    [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    SMulPosStrictMono Nat α where
  smul_lt_smul_of_pos_right _a ha _m _n hmn := nsmul_lt_nsmul_left ha hmn

end Nat

-- TODO: Instances for `Int` and `Rat`
