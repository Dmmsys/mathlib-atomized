/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.PropInstances
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Heyting algebras

This file defines Heyting, co-Heyting and bi-Heyting algebras.

A Heyting algebra is a bounded distributive lattice with an implication operation `⇨` such that
`a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. It also comes with a pseudo-complement `ᶜ`, such that `aᶜ = a ⇨ ⊥`.

Co-Heyting algebras are dual to Heyting algebras. They have a difference `\` and a negation `￢`
such that `a \ b ≤ c ↔ a ≤ b ⊔ c` and `￢a = ⊤ \ a`.

Bi-Heyting algebras are Heyting algebras that are also co-Heyting algebras.

From a logic standpoint, Heyting algebras precisely model intuitionistic logic, whereas Boolean
algebras model classical logic.

Heyting algebras are the order-theoretic equivalent of Cartesian closed categories.

## Main declarations

* `GeneralizedHeytingAlgebra`: Heyting algebra without a top element (nor negation).
* `GeneralizedCoheytingAlgebra`: Co-Heyting algebra without a bottom element (nor complement).
* `HeytingAlgebra`: Heyting algebra.
* `CoheytingAlgebra`: Co-Heyting algebra.
* `BiheytingAlgebra`: Bi-Heyting algebra.

## Implementation notes

Aligning the `Heyting` and `Coheyting` API with `to_dual` is kind of awkward, because they are
unfortunately quite different. One reason is that the arguments of sup/inf are often swapped
in the dual version, which is not compatible with `to_dual`. We work around this with extensive
use of `to_dual none`.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]

## Tags

Heyting, Brouwer, algebra, implication, negation, intuitionistic
-/

@[expose] public section

assert_not_exists RelIso

open Function OrderDual

to_dual_name_hint Compl HNot
to_dual_name_hint SDiff HImp

universe u

variable {ι α β : Type*}

/-! ### Notation -/

@[to_dual]
/-
**Prod.instHImp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instHImp [HImp α] [HImp β] : HImp (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Notation
-/
instance Prod.instHImp [HImp α] [HImp β] : HImp (α × β) :=
  ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

@[to_dual]
/-
**Prod.instHNot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instHNot [HNot α] [HNot β] : HNot (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instHNot [HNot α] [HNot β] : HNot (α × β) :=
  ⟨fun a => (￢a.1, ￢a.2)⟩

@[to_dual (attr := simp)]
/-
**fst_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fst_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 :=
  rfl

@[to_dual (attr := simp)]
/-
**snd_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：snd_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 :=
  rfl

@[to_dual (attr := simp)]
/-
**fst_hnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fst_hnot [HNot α] [HNot β] (a : α × β) : (￢a).1 = ￢a.1
参数：a : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_hnot [HNot α] [HNot β] (a : α × β) : (￢a).1 = ￢a.1 :=
  rfl

@[to_dual (attr := simp)]
/-
**snd_hnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：snd_hnot [HNot α] [HNot β] (a : α × β) : (￢a).2 = ￢a.2
参数：a : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_hnot [HNot α] [HNot β] (a : α × β) : (￢a).2 = ￢a.2 :=
  rfl

/-- A generalized Heyting algebra is a lattice with an additional binary operation `⇨` called
Heyting implication such that `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)`.

This generalizes `HeytingAlgebra` by not requiring a bottom element. -/
/-
**GeneralizedHeytingAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalized Heyting algebra is a lattice with an additional binary operation `
⇨` called
Heyting implication such that `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)`.

This generalizes `HeytingAlgebra` by not requiring a bottom element.
-/
class GeneralizedHeytingAlgebra (α : Type*) extends Lattice α, OrderTop α, HImp α where
  /-- `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)` -/
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

set_option linter.translate.warnInvalid false in
/-- A generalized co-Heyting algebra is a lattice with an additional binary
difference operation `\` such that `(· \ a)` is left adjoint to `(· ⊔ a)`.

This generalizes `CoheytingAlgebra` by not requiring a top element. -/
@[to_dual]
/-
**GeneralizedCoheytingAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalized co-Heyting algebra is a lattice with an additional binary
difference operation `\` such that `(· \ a)` is left adjoint to `(· ⊔ a)`.

This generalizes `CoheytingAlgebra` by not requiring a top element.
-/
class GeneralizedCoheytingAlgebra (α : Type*) extends Lattice α, OrderBot α, SDiff α where
  /-- `(· \ a)` is left adjoint to `(· ⊔ a)` -/
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c

/-- A Heyting algebra is a bounded lattice with an additional binary operation `⇨` called Heyting
implication such that `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)`. -/
/-
**HeytingAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Heyting algebra is a bounded lattice with an additional binary operation `⇨` c
alled Heyting
implication such that `(a ⇨ ·)` is right adjoint to `(a ⊓ ·)`.
-/
class HeytingAlgebra (α : Type*) extends GeneralizedHeytingAlgebra α, OrderBot α, Compl α where
  /-- `aᶜ` is defined as `a ⇨ ⊥` -/
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ

set_option linter.translate.warnInvalid false in
/-- A co-Heyting algebra is a bounded lattice with an additional binary difference operation `\`
such that `(· \ a)` is left adjoint to `(· ⊔ a)`. -/
@[to_dual]
/-
**CoheytingAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A co-Heyting algebra is a bounded lattice with an additional binary difference o
peration `\`
such that `(· \ a)` is left adjoint to `(· ⊔ a)`.
-/
class CoheytingAlgebra (α : Type*) extends GeneralizedCoheytingAlgebra α, OrderTop α, HNot α where
  /-- `⊤ \ a` is `￢a` -/
  top_sdiff (a : α) : ⊤ \ a = ￢a

/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
/-
**BiheytingAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra.
-/
class BiheytingAlgebra (α : Type*) extends HeytingAlgebra α, CoheytingAlgebra α where

attribute [to_dual existing] BiheytingAlgebra.toHeytingAlgebra

-- See note [lower instance priority]
attribute [instance 100] GeneralizedHeytingAlgebra.toOrderTop
attribute [instance 100] GeneralizedCoheytingAlgebra.toOrderBot

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HeytingAlgebra.toBoundedOrder [HeytingAlgebra α] : BoundedOrder α where

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and Heyting implication alone. -/
/-
**HeytingAlgebra.ofHImp** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HeytingAlgebra.ofHImp [DistribLattice α] [BoundedOrder α] (himp : α -> α -
> α) (le_himp_iff : forall a b c, a <= himp b c ↔ a ⊓ b <= c) : HeytingAlgebra α
参数：himp : α -> α -> α；le_himp_iff : forall a b c, a <= himp b c ↔ a ⊓ b <= c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a Heyting algebra from the lattice structure and Heyting implication a
lone.
-/
abbrev HeytingAlgebra.ofHImp [DistribLattice α] [BoundedOrder α] (himp : α → α → α)
    (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp,
    compl := fun a => himp a ⊥,
    le_himp_iff,
    himp_bot := fun _ => rfl }

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and complement operator alone. -/
/-
**HeytingAlgebra.ofCompl** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α -> α
) (le_himp_iff : forall a b c, a <= compl b ⊔ c ↔ a ⊓ b <= c) : HeytingAlgebra α
 where himp
参数：compl : α -> α；le_himp_iff : forall a b c, a <= compl b ⊔ c ↔ a ⊓ b <= c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a Heyting algebra from the lattice structure and complement operator a
lone.
-/
abbrev HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α → α)
    (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : HeytingAlgebra α where
  himp := (compl · ⊔ ·)
  compl := compl
  le_himp_iff := le_himp_iff
  himp_bot _ := sup_bot_eq _

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the lattice structure and the difference alone. -/
/-
**CoheytingAlgebra.ofSDiff** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CoheytingAlgebra.ofSDiff [DistribLattice α] [BoundedOrder α] (sdiff : α ->
 α -> α) (sdiff_le_iff : forall a b c, sdiff a b <= c ↔ a <= b ⊔ c) : CoheytingA
lgebra α
参数：sdiff : α -> α -> α；sdiff_le_iff : forall a b c, sdiff a b <= c ↔ a <= b ⊔ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a co-Heyting algebra from the lattice structure and the difference alo
ne.
-/
abbrev CoheytingAlgebra.ofSDiff [DistribLattice α] [BoundedOrder α] (sdiff : α → α → α)
    (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff,
    hnot := fun a => sdiff ⊤ a,
    sdiff_le_iff,
    top_sdiff := fun _ => rfl }

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the difference and Heyting negation alone. -/
/-
**CoheytingAlgebra.ofHNot** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CoheytingAlgebra.ofHNot [DistribLattice α] [BoundedOrder α] (hnot : α -> α
) (sdiff_le_iff : forall a b c, a ⊓ hnot b <= c ↔ a <= b ⊔ c) : CoheytingAlgebra
 α where sdiff a b
参数：hnot : α -> α；sdiff_le_iff : forall a b c, a ⊓ hnot b <= c ↔ a <= b ⊔ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a co-Heyting algebra from the difference and Heyting negation alone.
-/
abbrev CoheytingAlgebra.ofHNot [DistribLattice α] [BoundedOrder α] (hnot : α → α)
    (sdiff_le_iff : ∀ a b c, a ⊓ hnot b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α where
  sdiff a b := a ⊓ hnot b
  hnot := hnot
  sdiff_le_iff := sdiff_le_iff
  top_sdiff _ := top_inf_eq _

/-! In this section, we'll give interpretations of these results in the Heyting algebra model of
intuitionistic logic,- where `≤` can be interpreted as "validates", `⇨` as "implies", `⊓` as "and",
`⊔` as "or", `⊥` as "false" and `⊤` as "true". Note that we confuse `→` and `⊢` because those are
the same in this logic.

See also `Prop.heytingAlgebra`. -/
section GeneralizedHeytingAlgebra

@[simp low] -- low priority so that it doesn't overwrite user-provided simp lemmas
/-
**sdiff_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b <= c ↔ a 
<= b ⊔ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GeneralizedCoheytingAlgebra.sdiff_le_iff`：∀ {α : Type u_4} [self : Gener
alizedCoheytingAlgebra α] (a b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
-/
theorem sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b ≤ c ↔ a ≤ b ⊔ c :=
  GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _
/-
**sdiff_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_le_iff' [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b <= c ↔ a
 <= c ⊔ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_le_iff`：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} :
 a \ b <= c ↔ a <= b ⊔ c
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sdiff_le_iff' [GeneralizedCoheytingAlgebra α] {a b c : α} : a \ b ≤ c ↔ a ≤ c ⊔ b := by
  rw [sdiff_le_iff, sup_comm]

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

/-- `p → q → r ↔ p ∧ q → r` -/
@[to_dual existing sdiff_le_iff', simp]
/-
**le_himp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GeneralizedHeytingAlgebra.le_himp_iff`：∀ {α : Type u_4} [self : Generali
zedHeytingAlgebra α] (a b c : α), a ≤ b ⇨ c ↔ a ⊓ b ≤ c

--- 原说明 ---
`p → q → r ↔ p ∧ q → r`
-/
theorem le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  GeneralizedHeytingAlgebra.le_himp_iff _ _ _

/-- `p → q → r ↔ q ∧ p → r` -/
@[to_dual existing sdiff_le_iff]
/-
**le_himp_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_himp_iff' : a <= b ⇨ c ↔ b ⊓ a <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`p → q → r ↔ q ∧ p → r`
-/
theorem le_himp_iff' : a ≤ b ⇨ c ↔ b ⊓ a ≤ c := by rw [le_himp_iff, inf_comm]

/-- `p → q → r ↔ q → p → r` -/
@[to_dual sdiff_le_comm]
/-
**le_himp_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_himp_comm : a <= b ⇨ c ↔ b <= a ⇨ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `le_himp_iff'`：le_himp_iff' : a <= b ⇨ c ↔ b ⊓ a <= c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`p → q → r ↔ q → p → r`
-/
theorem le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff']

/-- `p → q → p` -/
@[to_dual sdiff_le]
/-
**le_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_himp : a <= b ⇨ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
`p → q → p`
-/
theorem le_himp : a ≤ b ⇨ a :=
  le_himp_iff.2 inf_le_left

/-- `p → p → q ↔ p → q` -/
@[to_dual sdiff_le_iff_left]
/-
**le_himp_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_himp_iff_left : a <= a ⇨ b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`p → p → q ↔ p → q`
-/
theorem le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]

/-- `p → p` -/
@[to_dual (attr := simp)]
/-
**himp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_self : a ⇨ a = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
`p → p`
-/
theorem himp_self : a ⇨ a = ⊤ :=
  top_le_iff.1 <| le_himp_iff.2 inf_le_right

/-- `(p → q) ∧ p → q` -/
@[to_dual le_sdiff_sup]
/-
**himp_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_inf_le : (a ⇨ b) ⊓ a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
`(p → q) ∧ p → q`
-/
theorem himp_inf_le : (a ⇨ b) ⊓ a ≤ b :=
  le_himp_iff.1 le_rfl

/-- `p ∧ (p → q) → q` -/
@[to_dual le_sup_sdiff]
/-
**inf_himp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_himp_le : a ⊓ (a ⇨ b) <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
`p ∧ (p → q) → q`
-/
theorem inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ← le_himp_iff]

/-- `p ∧ (p → q) ↔ p ∧ q` -/
@[to_dual (attr := simp) sup_sdiff_self]
-- TODO: Should this be renamed to `inf_himp_self`?
/-
**inf_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `le_himp`：le_himp : a <= b ⇨ a
-/
theorem inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
  le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) <| inf_le_inf_left _ le_himp

/-- `(p → q) ∧ p ↔ q ∧ p` -/
@[to_dual (attr := simp)]
/-
**himp_inf_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_himp`：inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b

--- 原说明 ---
`(p → q) ∧ p ↔ q ∧ p`
-/
theorem himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]

/-- The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis. -/
@[to_dual (attr := simp)]
/-
**himp_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_eq_top_iff : a ⇨ b = ⊤ ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis.
-/
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by rw [← top_le_iff, le_himp_iff, top_inf_eq]

/-- `p → true` -/
@[to_dual (attr := simp) bot_sdiff]
/-
**himp_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_top : a ⇨ ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `himp_eq_top_iff`：himp_eq_top_iff : a ⇨ b = ⊤ ↔ a <= b
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
`p → true`
-/
theorem himp_top : a ⇨ ⊤ = ⊤ :=
  himp_eq_top_iff.2 le_top

/-- `true → p ↔ p` -/
@[to_dual (attr := simp) sdiff_bot]
/-
**top_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_himp : ⊤ ⇨ a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`true → p ↔ p`
-/
theorem top_himp : ⊤ ⇨ a = a :=
  eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]

/-- `p → q → r ↔ p ∧ q → r` -/
@[to_dual none]
/-
**himp_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`p → q → r ↔ p ∧ q → r`
-/
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]

/-- `(q → r) → (p → q) → q → r` -/
@[to_dual none]
/-
**himp_le_himp_himp_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_le_himp_himp_himp : b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `himp_inf_self`：himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
`(q → r) → (p → q) → q → r`
-/
theorem himp_le_himp_himp_himp : b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c := by
  rw [le_himp_iff, le_himp_iff, inf_assoc, himp_inf_self, ← inf_assoc, himp_inf_self, inf_assoc]
  exact inf_le_left

@[simp, to_dual none]
/-
**himp_inf_himp_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_inf_himp_inf_le : (b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `himp_le_himp_himp_himp`：himp_le_himp_himp_himp : b ⇨ c <= (a ⇨ b) ⇨ a ⇨ 
c
-/
theorem himp_inf_himp_inf_le : (b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := by
  simpa using @himp_le_himp_himp_himp

/-- `p → q → r ↔ q → p → r` -/
@[to_dual (reorder := a c) sdiff_right_comm]
/-
**himp_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_himp`：himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`p → q → r ↔ q → p → r`
-/
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]

@[to_dual (attr := simp)]
/-
**himp_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_idem : b ⇨ b ⇨ a = b ⇨ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_himp`：himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem himp_idem : b ⇨ b ⇨ a = b ⇨ a := by rw [himp_himp, inf_idem]

@[to_dual (reorder := a c b) sup_sdiff_distrib]
/-
**himp_inf_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

@[to_dual (reorder := a c b) sdiff_inf_distrib]
/-
**sup_himp_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `le_himp_comm`：le_himp_comm : a <= b ⇨ c ↔ b <= a ⇨ c
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
  eq_of_forall_le_iff fun d => by
    rw [le_inf_iff, le_himp_comm, sup_le_iff]
    simp_rw [le_himp_comm]

@[to_dual sdiff_le_sdiff_right]
/-
**himp_le_himp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_le_himp_left (h : a <= b) : c ⇨ a <= c ⇨ b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `himp_inf_le`：himp_inf_le : (a ⇨ b) ⊓ a <= b
-/
theorem himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b :=
  le_himp_iff.2 <| himp_inf_le.trans h

@[to_dual sdiff_le_sdiff_left]
/-
**himp_le_himp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_le_himp_right (h : a <= b) : b ⇨ c <= a ⇨ c
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `himp_inf_le`：himp_inf_le : (a ⇨ b) ⊓ a <= b
-/
theorem himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
  le_himp_iff.2 <| (inf_le_inf_left _ h).trans himp_inf_le

@[to_dual (reorder := hab hcd) (attr := gcongr)]
/-
**himp_le_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_le_himp (hab : a <= b) (hcd : c <= d) : b ⇨ c <= a ⇨ d
参数：hab : a <= b；hcd : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `himp_le_himp_right`：himp_le_himp_right (h : a <= b) : b ⇨ c <= a ⇨ c
· 使用定理 `himp_le_himp_left`：himp_le_himp_left (h : a <= b) : c ⇨ a <= c ⇨ b
-/
theorem himp_le_himp (hab : a ≤ b) (hcd : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
  (himp_le_himp_right hab).trans <| himp_le_himp_left hcd

@[to_dual (attr := simp) sdiff_inf_self_left]
/-
**sup_himp_self_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_himp_distrib`：sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (
b ⇨ c)
· 使用定理 `himp_self`：himp_self : a ⇨ a = ⊤
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
-/
theorem sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a := by
  rw [sup_himp_distrib, himp_self, top_inf_eq]

@[to_dual (attr := simp) sdiff_inf_self_right]
/-
**sup_himp_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_himp_self_right (a b : α) : a ⊔ b ⇨ b = a ⇨ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_himp_distrib`：sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (
b ⇨ c)
· 使用定理 `himp_self`：himp_self : a ⇨ a = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
theorem sup_himp_self_right (a b : α) : a ⊔ b ⇨ b = a ⇨ b := by
  rw [sup_himp_distrib, himp_self, inf_top_eq]

@[to_dual sdiff_eq_left]
/-
**Codisjoint.himp_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.himp_eq_right (h : Codisjoint a b) : b ⇨ a = a
参数：h : Codisjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_himp`：top_himp : ⊤ ⇨ a = a
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `sup_himp_self_left`：sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a
-/
theorem Codisjoint.himp_eq_right (h : Codisjoint a b) : b ⇨ a = a := by
  conv_rhs => rw [← @top_himp _ _ a]
  rw [← h.eq_top, sup_himp_self_left]

@[to_dual sdiff_eq_right]
/-
**Codisjoint.himp_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.himp_eq_left (h : Codisjoint a b) : a ⇨ b = b
参数：h : Codisjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Codisjoint.himp_eq_right`：Codisjoint.himp_eq_right (h : Codisjoint a b) 
: b ⇨ a = a
· 使用定理 `Codisjoint.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] ⦃a b : α⦄, Codisjoint a b → Codisjoint b a
-/
theorem Codisjoint.himp_eq_left (h : Codisjoint a b) : a ⇨ b = b :=
  h.symm.himp_eq_right

@[to_dual sup_sdiff_cancel_left]
/-
**Codisjoint.himp_inf_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.himp_inf_cancel_left (h : Codisjoint a b) : a ⇨ a ⊓ b = b
参数：h : Codisjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_inf_distrib`：himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (
a ⇨ c)
· 使用定理 `himp_self`：himp_self : a ⇨ a = ⊤
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `Codisjoint.himp_eq_left`：Codisjoint.himp_eq_left (h : Codisjoint a b) : 
a ⇨ b = b
-/
theorem Codisjoint.himp_inf_cancel_left (h : Codisjoint a b) : a ⇨ a ⊓ b = b := by
  rw [himp_inf_distrib, himp_self, top_inf_eq, h.himp_eq_left]

@[to_dual sup_sdiff_cancel_right]
/-
**Codisjoint.himp_inf_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.himp_inf_cancel_right (h : Codisjoint a b) : b ⇨ a ⊓ b = a
参数：h : Codisjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_inf_distrib`：himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (
a ⇨ c)
· 使用定理 `himp_self`：himp_self : a ⇨ a = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Codisjoint.himp_eq_right`：Codisjoint.himp_eq_right (h : Codisjoint a b) 
: b ⇨ a = a
-/
theorem Codisjoint.himp_inf_cancel_right (h : Codisjoint a b) : b ⇨ a ⊓ b = a := by
  rw [himp_inf_distrib, himp_self, inf_top_eq, h.himp_eq_right]

/-- See `himp_le` for a stronger version in Boolean algebras. -/
@[to_dual le_sdiff_of_le_left
/-- See `le_sdiff` for a stronger version in generalised Boolean algebras. -/]
/-
**Codisjoint.himp_le_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.himp_le_of_right_le (hac : Codisjoint a c) (hba : b <= a) : c ⇨
 b <= a
参数：hac : Codisjoint a c；hba : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `himp_le_himp_left`：himp_le_himp_left (h : a <= b) : c ⇨ a <= c ⇨ b
· 使用定理 `Codisjoint.himp_eq_right`：Codisjoint.himp_eq_right (h : Codisjoint a b) 
: b ⇨ a = a
-/
theorem Codisjoint.himp_le_of_right_le (hac : Codisjoint a c) (hba : b ≤ a) : c ⇨ b ≤ a :=
  (himp_le_himp_left hba).trans_eq hac.himp_eq_right

@[to_dual sdiff_sdiff_le]
/-
**le_himp_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_himp_himp : a <= (a ⇨ b) ⇨ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_himp_le`：inf_himp_le : a ⊓ (a ⇨ b) <= b
-/
theorem le_himp_himp : a ≤ (a ⇨ b) ⇨ b :=
  le_himp_iff.2 inf_himp_le

@[to_dual (attr := simp)]
/-
**himp_eq_himp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：himp_eq_himp_iff : b ⇨ a = a ⇨ b ↔ a = b
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
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma himp_eq_himp_iff : b ⇨ a = a ⇨ b ↔ a = b := by simp [le_antisymm_iff]

@[to_dual]
/-
**himp_ne_himp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：himp_ne_himp_iff : b ⇨ a != a ⇨ b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `himp_eq_himp_iff`：himp_eq_himp_iff : b ⇨ a = a ⇨ b ↔ a = b
-/
lemma himp_ne_himp_iff : b ⇨ a ≠ a ⇨ b ↔ a ≠ b := himp_eq_himp_iff.not

@[to_dual none]
/-
**himp_triangle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) <= a ⇨ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `himp_inf_le`：himp_inf_le : (a ⇨ b) ⊓ a <= b
· 使用定理 `le_himp_himp`：le_himp_himp : a <= (a ⇨ b) ⇨ b
-/
theorem himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c := by
  rw [le_himp_iff, inf_right_comm, ← le_himp_iff]
  exact himp_inf_le.trans le_himp_himp

@[to_dual none]
/-
**himp_inf_himp_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_inf_himp_cancel (hba : b <= a) (hcb : c <= b) : (a ⇨ b) ⊓ (b ⇨ c) = a
 ⇨ c
参数：hba : b <= a；hcb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `himp_triangle`：himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) <= a ⇨ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `himp_le_himp_left`：himp_le_himp_left (h : a <= b) : c ⇨ a <= c ⇨ b
· 使用定理 `himp_le_himp_right`：himp_le_himp_right (h : a <= b) : b ⇨ c <= a ⇨ c
-/
theorem himp_inf_himp_cancel (hba : b ≤ a) (hcb : c ≤ b) : (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c :=
  (himp_triangle _ _ _).antisymm <| le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)

@[to_dual gc_sdiff_sup]
/-
**gc_inf_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_inf_himp : GaloisConnection (a ⊓ ·) (a ⇨ ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_himp_iff'`：le_himp_iff' : a <= b ⇨ c ↔ b ⊓ a <= c
-/
theorem gc_inf_himp : GaloisConnection (a ⊓ ·) (a ⇨ ·) :=
  fun _ _ ↦ Iff.symm le_himp_iff'

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [inf_comm a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]; rfl
/-
**OrderDual.instGeneralizedCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra αᵒ
ᵈ where sdiff a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra αᵒᵈ where
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff
/-
**Prod.instGeneralizedHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instGeneralizedHeytingAlgebra [GeneralizedHeytingAlgebra β] : General
izedHeytingAlgebra (α × β) where le_himp_iff _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instGeneralizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra (α × β) where
  le_himp_iff _ _ _ := and_congr le_himp_iff le_himp_iff
/-
**Pi.instGeneralizedHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instGeneralizedHeytingAlgebra {α : ι -> Type*} [forall i, GeneralizedHe
ytingAlgebra (α i)] : GeneralizedHeytingAlgebra (forall i, α i) where le_himp_if
f i
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instGeneralizedHeytingAlgebra {α : ι → Type*} [∀ i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (∀ i, α i) where
  le_himp_iff i := by simp [le_def]

end GeneralizedHeytingAlgebra

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] {a b c d : α}

@[to_dual none]
/-
**Disjoint.disjoint_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b
参数：h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b :=
  h.mono_left sdiff_le

@[to_dual none]
/-
**Disjoint.disjoint_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c)
参数：h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c) :=
  h.mono_right sdiff_le

@[to_dual none]
/-
**sup_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_left : a ⊔ a \ b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sup_sdiff_left : a ⊔ a \ b = a :=
  sup_of_le_left sdiff_le

@[to_dual none]
/-
**sup_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_right : a \ b ⊔ a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sup_sdiff_right : a \ b ⊔ a = a :=
  sup_of_le_right sdiff_le

@[to_dual none]
/-
**inf_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_left : a \ b ⊓ a = a \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem inf_sdiff_left : a \ b ⊓ a = a \ b :=
  inf_of_le_left sdiff_le

@[to_dual none]
/-
**inf_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_right : a ⊓ a \ b = a \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem inf_sdiff_right : a ⊓ a \ b = a \ b :=
  inf_of_le_right sdiff_le

@[to_dual none]
alias sup_sdiff_self_left := sdiff_sup_self

@[to_dual none]
alias sup_sdiff_self_right := sup_sdiff_self

@[to_dual none]
/-
**sup_sdiff_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_eq_sup (h : c <= a) : a ⊔ b \ c = a ⊔ b
参数：h : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_congr_left`：sup_congr_left (hb : b <= a ⊔ c) (hc : c <= a ⊔ b) : a ⊔
 b = a ⊔ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `le_sup_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a
 b : α}, b ≤ a ⊔ b \ a
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
-/
theorem sup_sdiff_eq_sup (h : c ≤ a) : a ⊔ b \ c = a ⊔ b :=
  sup_congr_left (sdiff_le.trans le_sup_right) <| le_sup_sdiff.trans <| sup_le_sup_right h _

-- cf. `Set.union_sdiff_cancel'`
@[to_dual none]
/-
**sup_sdiff_cancel'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_cancel' (hab : a <= b) (hbc : b <= c) : b ⊔ c \ a = c
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sdiff_eq_sup`：sup_sdiff_eq_sup (h : c <= a) : a ⊔ b \ c = a ⊔ b
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
-/
theorem sup_sdiff_cancel' (hab : a ≤ b) (hbc : b ≤ c) : b ⊔ c \ a = c := by
  rw [sup_sdiff_eq_sup hab, sup_of_le_right hbc]

@[to_dual none]
/-
**sup_sdiff_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a = b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_cancel'`：sup_sdiff_cancel' (hab : a <= b) (hbc : b <= c) : b ⊔
 c \ a = c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sup_sdiff_cancel_right (h : a ≤ b) : a ⊔ b \ a = b :=
  sup_sdiff_cancel' le_rfl h

@[to_dual none]
/-
**sdiff_sup_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_sdiff_cancel_right`：sup_sdiff_cancel_right (h : a <= b) : a ⊔ b \ a 
= b
-/
theorem sdiff_sup_cancel (h : b ≤ a) : a \ b ⊔ b = a := by rw [sup_comm, sup_sdiff_cancel_right h]

@[to_dual none]
/-
**sdiff_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_left_inj (hac : c <= a) (hbc : c <= b) : a \ c = b \ c ↔ a = b
参数：hac : c <= a；hbc : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_sup_cancel`：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
-/
theorem sdiff_left_inj (hac : c ≤ a) (hbc : c ≤ b) : a \ c = b \ c ↔ a = b :=
  ⟨fun h => by rw [← sdiff_sup_cancel hac, h, sdiff_sup_cancel hbc], congrArg (· \ c)⟩

@[to_dual none]
/-
**sup_le_of_le_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_of_le_sdiff_left (h : b <= c \ a) (hac : a <= c) : a ⊔ b <= c
参数：h : b <= c \ a；hac : a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sup_le_of_le_sdiff_left (h : b ≤ c \ a) (hac : a ≤ c) : a ⊔ b ≤ c :=
  sup_le hac <| h.trans sdiff_le

@[to_dual none]
/-
**sup_le_of_le_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_of_le_sdiff_right (h : a <= c \ b) (hbc : b <= c) : a ⊔ b <= c
参数：h : a <= c \ b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem sup_le_of_le_sdiff_right (h : a ≤ c \ b) (hbc : b ≤ c) : a ⊔ b ≤ c :=
  sup_le (h.trans sdiff_le) hbc

@[to_dual none]
/-
**sdiff_sdiff_sdiff_le_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) <= c \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_le_iff`：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} :
 a \ b <= c ↔ a <= b ⊔ c
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `sdiff_sup_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), b \ a ⊔ a = b ⊔ a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) ≤ c \ b := by
  rw [sdiff_le_iff, sdiff_le_iff, sup_left_comm, sup_sdiff_self, sup_left_comm, sdiff_sup_self,
    sup_left_comm]
  exact le_sup_left

@[simp, to_dual none]
/-
**le_sup_sdiff_sup_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_sdiff_sup_sdiff : a <= b ⊔ (a \ c ⊔ c \ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sdiff_sdiff_sdiff_le_sdiff`：sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ 
c) <= c \ b
-/
theorem le_sup_sdiff_sup_sdiff : a ≤ b ⊔ (a \ c ⊔ c \ b) := by
  simpa using @sdiff_sdiff_sdiff_le_sdiff

@[to_dual none]
/-
**sdiff_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c) :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]

@[to_dual none]
/-
**sdiff_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff`：sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c)
-/
theorem sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c) :=
  sdiff_sdiff _ _ _

@[to_dual none]
/-
**sdiff_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_right_comm`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] (c b a : α), (c \ b) \ a = (c \ a) \ b
-/
theorem sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b :=
  sdiff_right_comm _ _ _

@[simp, to_dual none]
/-
**sdiff_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sdiff_self : (a \ b) \ a = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_comm`：sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `bot_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, ⊥ \ a = ⊥
-/
theorem sdiff_sdiff_self : (a \ b) \ a = ⊥ := by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

@[to_dual none]
/-
**sup_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_distrib`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra 
α] (b c a : α), (b ⊔ c) \ a = b \ a ⊔ c \ a
-/
theorem sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  sup_sdiff_distrib _ _ _

@[simp, to_dual none]
/-
**sup_sdiff_right_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem sup_sdiff_right_self : (a ⊔ b) \ b = a \ b := by rw [sup_sdiff, sdiff_self, sup_bot_eq]

@[simp, to_dual none]
/-
**sup_sdiff_left_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_left_self : (a ⊔ b) \ a = b \ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_sdiff_right_self`：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
-/
theorem sup_sdiff_left_self : (a ⊔ b) \ a = b \ a := by rw [sup_comm, sup_sdiff_right_self]

-- cf. `IsCompl.inf_sup`
@[to_dual none]
/-
**sdiff_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_inf_distrib`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra 
α] (b c a : α), c \ (a ⊓ b) = c \ a ⊔ c \ b
-/
theorem sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  sdiff_inf_distrib _ _ _

@[to_dual none]
/-
**sdiff_triangle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_triangle (a b c : α) : a \ c <= a \ b ⊔ b \ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_le_iff`：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} :
 a \ b <= c ↔ a <= b ⊔ c
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b : α}, b \ (b \ a) ≤ a
· 使用定理 `le_sup_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a
 b : α}, b ≤ a ⊔ b \ a
-/
theorem sdiff_triangle (a b c : α) : a \ c ≤ a \ b ⊔ b \ c := by
  rw [sdiff_le_iff, sup_left_comm, ← sdiff_le_iff]
  exact sdiff_sdiff_le.trans le_sup_sdiff

@[to_dual none]
/-
**sdiff_sup_sdiff_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sup_sdiff_cancel (hba : b <= a) (hcb : c <= b) : a \ b ⊔ b \ c = a \
 c
参数：hba : b <= a；hcb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `sdiff_triangle`：sdiff_triangle (a b c : α) : a \ c <= a \ b ⊔ b \ c
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `sdiff_le_sdiff_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] {a b c : α}, b ≤ a → c \ a ≤ c \ b
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
-/
theorem sdiff_sup_sdiff_cancel (hba : b ≤ a) (hcb : c ≤ b) : a \ b ⊔ b \ c = a \ c :=
  (sdiff_triangle _ _ _).antisymm' <| sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)

/-- a version of `sdiff_sup_sdiff_cancel` with more general hypotheses. -/
@[to_dual none]
/-
**sdiff_sup_sdiff_cancel'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_sup_sdiff_cancel' (hinf : a ⊓ c <= b) (hsup : b <= a ⊔ c) : a \ b ⊔ 
b \ c = a \ c
参数：hinf : a ⊓ c <= b；hsup : b <= a ⊔ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `sdiff_triangle`：sdiff_triangle (a b c : α) : a \ c <= a \ b ⊔ b \ c
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiff_inf_self_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] (a b : α), a \ (a ⊓ b) = a \ b
· 使用定理 `sdiff_le_sdiff_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] {a b c : α}, b ≤ a → c \ a ≤ c \ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a

--- 原说明 ---
a version of `sdiff_sup_sdiff_cancel` with more general hypotheses.
-/
theorem sdiff_sup_sdiff_cancel' (hinf : a ⊓ c ≤ b) (hsup : b ≤ a ⊔ c) :
    a \ b ⊔ b \ c = a \ c := by
  refine (sdiff_triangle ..).antisymm' <| sup_le ?_ <| by simpa [sup_comm]
  rw [← sdiff_inf_self_left (b := c)]
  exact sdiff_le_sdiff_left hinf

@[to_dual none]
/-
**sdiff_le_sdiff_of_sup_le_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_le_sdiff_of_sup_le_sup_left (h : c ⊔ a <= c ⊔ b) : a \ c <= b \ c
参数：h : c ⊔ a <= c ⊔ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_sdiff_left_self`：sup_sdiff_left_self : (a ⊔ b) \ a = b \ a
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
-/
theorem sdiff_le_sdiff_of_sup_le_sup_left (h : c ⊔ a ≤ c ⊔ b) : a \ c ≤ b \ c := by
  rw [← sup_sdiff_left_self, ← @sup_sdiff_left_self _ _ _ b]
  exact sdiff_le_sdiff_right h

@[to_dual none]
/-
**sdiff_le_sdiff_of_sup_le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiff_le_sdiff_of_sup_le_sup_right (h : a ⊔ c <= b ⊔ c) : a \ c <= b \ c
参数：h : a ⊔ c <= b ⊔ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_sdiff_right_self`：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
-/
theorem sdiff_le_sdiff_of_sup_le_sup_right (h : a ⊔ c ≤ b ⊔ c) : a \ c ≤ b \ c := by
  rw [← sup_sdiff_right_self, ← @sup_sdiff_right_self _ _ b]
  exact sdiff_le_sdiff_right h

@[simp, to_dual none]
/-
**inf_sdiff_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_sup_left : a \ c ⊓ (a ⊔ b) = a \ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem inf_sdiff_sup_left : a \ c ⊓ (a ⊔ b) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_left

@[simp, to_dual none]
/-
**inf_sdiff_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_right

-- See note [lower instance priority]
@[to_dual existing]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GeneralizedCoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹GeneralizedCoheytingAlgebra α› with
    le_sup_inf :=
      fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff]; rfl }

@[to_dual existing]
/-
**OrderDual.instGeneralizedHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instGeneralizedHeytingAlgebra : GeneralizedHeytingAlgebra αᵒᵈ wh
ere himp
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instGeneralizedHeytingAlgebra : GeneralizedHeytingAlgebra αᵒᵈ where
  himp := fun a b => toDual (ofDual b \ ofDual a)
  le_himp_iff := fun a b c => by rw [inf_comm]; exact sdiff_le_iff

@[to_dual existing]
/-
**Prod.instGeneralizedCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instGeneralizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] : Gen
eralizedCoheytingAlgebra (α × β) where sdiff_le_iff _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instGeneralizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra (α × β) where
  sdiff_le_iff _ _ _ := and_congr sdiff_le_iff sdiff_le_iff

@[to_dual existing]
/-
**Pi.instGeneralizedCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instGeneralizedCoheytingAlgebra {α : ι -> Type*} [forall i, Generalized
CoheytingAlgebra (α i)] : GeneralizedCoheytingAlgebra (forall i, α i) where sdif
f_le_iff i
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instGeneralizedCoheytingAlgebra {α : ι → Type*}
    [∀ i, GeneralizedCoheytingAlgebra (α i)] : GeneralizedCoheytingAlgebra (∀ i, α i) where
  sdiff_le_iff i := by simp [le_def]

end GeneralizedCoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

@[to_dual (attr := simp) top_sdiff']
/-
**himp_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingAlgebra.himp_bot`：∀ {α : Type u_4} [self : HeytingAlgebra α] (a :
 α), a ⇨ ⊥ = aᶜ
-/
theorem himp_bot (a : α) : a ⇨ ⊥ = aᶜ :=
  HeytingAlgebra.himp_bot _

@[to_dual (attr := simp) sdiff_top]
/-
**bot_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_himp (a : α) : ⊥ ⇨ a = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `himp_eq_top_iff`：himp_eq_top_iff : a ⇨ b = ⊤ ↔ a <= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem bot_himp (a : α) : ⊥ ⇨ a = ⊤ :=
  himp_eq_top_iff.2 bot_le

@[to_dual]
/-
**compl_sup_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_himp_distrib`：sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (
b ⇨ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  simp_rw [← himp_bot, sup_himp_distrib]

@[to_dual (attr := simp)]
/-
**compl_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_sup_distrib`：compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
-/
theorem compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  compl_sup_distrib _ _

@[to_dual sdiff_le_hnot]
/-
**compl_le_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le_himp : aᶜ <= a ⇨ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
· 使用定理 `himp_le_himp_left`：himp_le_himp_left (h : a <= b) : c ⇨ a <= c ⇨ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem compl_le_himp : aᶜ ≤ a ⇨ b :=
  (himp_bot _).ge.trans <| himp_le_himp_left bot_le

@[to_dual none]
/-
**compl_sup_le_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sup_le_himp : aᶜ ⊔ b <= a ⇨ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `compl_le_himp`：compl_le_himp : aᶜ <= a ⇨ b
· 使用定理 `le_himp`：le_himp : a <= b ⇨ a
-/
theorem compl_sup_le_himp : aᶜ ⊔ b ≤ a ⇨ b :=
  sup_le compl_le_himp le_himp

@[to_dual sdiff_le_inf_hnot]
/-
**sup_compl_le_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_compl_le_himp : b ⊔ aᶜ <= a ⇨ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_himp`：le_himp : a <= b ⇨ a
· 使用定理 `compl_le_himp`：compl_le_himp : aᶜ <= a ⇨ b
-/
theorem sup_compl_le_himp : b ⊔ aᶜ ≤ a ⇨ b :=
  sup_le le_himp compl_le_himp

-- `p → ¬ p ↔ ¬ p`
@[to_dual (attr := simp) hnot_sdiff]
/-
**himp_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_compl (a : α) : a ⇨ aᶜ = aᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
· 使用定理 `himp_himp`：himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [← himp_bot, himp_himp, inf_idem]

-- `p → ¬ q ↔ q → ¬ p`
@[to_dual (reorder := a b) hnot_sdiff_comm]
/-
**himp_compl_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `himp_left_comm`：himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [← himp_bot, himp_left_comm]

@[to_dual hnot_le_iff_codisjoint_left]
/-
**le_compl_iff_disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_compl_iff_disjoint_right : a <= bᶜ ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_compl_iff_disjoint_right : a ≤ bᶜ ↔ Disjoint a b := by
  rw [← himp_bot, le_himp_iff, disjoint_iff_inf_le]

@[to_dual hnot_le_iff_codisjoint_right]
/-
**le_compl_iff_disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjoint b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
-/
theorem le_compl_iff_disjoint_left : a ≤ bᶜ ↔ Disjoint b a :=
  le_compl_iff_disjoint_right.trans disjoint_comm

@[to_dual hnot_le_comm]
/-
**le_compl_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_compl_comm : a <= bᶜ ↔ b <= aᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `le_compl_iff_disjoint_left`：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjo
int b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ := by
  rw [le_compl_iff_disjoint_right, le_compl_iff_disjoint_left]

@[to_dual hnot_le_left]
alias ⟨_, Disjoint.le_compl_right⟩ := le_compl_iff_disjoint_right

@[to_dual hnot_le_right]
alias ⟨_, Disjoint.le_compl_left⟩ := le_compl_iff_disjoint_left

@[to_dual hnot_le_iff_hnot_le]
alias le_compl_iff_le_compl := le_compl_comm

@[to_dual hnot_le_of_hnot_le]
alias ⟨le_compl_of_le_compl, _⟩ := le_compl_comm

@[to_dual]
/-
**disjoint_compl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_compl_left : Disjoint aᶜ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
-/
theorem disjoint_compl_left : Disjoint aᶜ a :=
  disjoint_iff_inf_le.mpr <| le_himp_iff.1 (himp_bot _).ge

@[to_dual]
/-
**disjoint_compl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_compl_right : Disjoint a aᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
-/
theorem disjoint_compl_right : Disjoint a aᶜ :=
  disjoint_compl_left.symm

@[to_dual]
/-
**LE.le.disjoint_compl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LE.le.disjoint_compl_left (h : b <= a) : Disjoint aᶜ b
参数：h : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
-/
theorem LE.le.disjoint_compl_left (h : b ≤ a) : Disjoint aᶜ b :=
  _root_.disjoint_compl_left.mono_right h

@[to_dual]
/-
**LE.le.disjoint_compl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LE.le.disjoint_compl_right (h : a <= b) : Disjoint a bᶜ
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem LE.le.disjoint_compl_right (h : a ≤ b) : Disjoint a bᶜ :=
  _root_.disjoint_compl_right.mono_left h

@[to_dual]
/-
**IsCompl.compl_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
参数：h : IsCompl a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Disjoint.le_compl_left`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b 
: α}, Disjoint b a → a ≤ bᶜ
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Disjoint.le_of_codisjoint`：Disjoint.le_of_codisjoint (hab : Disjoint a b
) (hbc : Codisjoint b c) : a <= c
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b :=
  h.1.le_compl_left.antisymm' <| Disjoint.le_of_codisjoint disjoint_compl_left h.2

@[to_dual]
/-
**IsCompl.eq_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ
参数：h : IsCompl a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Disjoint.le_compl_right`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b
 : α}, Disjoint a b → a ≤ bᶜ
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Disjoint.le_of_codisjoint`：Disjoint.le_of_codisjoint (hab : Disjoint a b
) (hbc : Codisjoint b c) : a <= c
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
· 使用定理 `Codisjoint.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] ⦃a b : α⦄, Codisjoint a b → Codisjoint b a
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ :=
  h.1.le_compl_right.antisymm <| Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm

@[to_dual none]
/-
**compl_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b
参数：h₀ : a ⊓ b = ⊥；h₁ : a ⊔ b = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
-/
theorem compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b :=
  (IsCompl.of_eq h₀ h₁).compl_eq

@[to_dual (attr := simp)]
/-
**inf_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_compl_self (a : α) : a ⊓ aᶜ = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ :=
  disjoint_compl_right.eq_bot

@[to_dual (attr := simp)]
/-
**compl_inf_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_inf_self (a : α) : aᶜ ⊓ a = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
-/
theorem compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ :=
  disjoint_compl_left.eq_bot

@[to_dual]
/-
**inf_compl_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_compl_eq_bot : a ⊓ aᶜ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_compl_self`：inf_compl_self (a : α) : a ⊓ aᶜ = ⊥
-/
theorem inf_compl_eq_bot : a ⊓ aᶜ = ⊥ :=
  inf_compl_self _

@[to_dual]
/-
**compl_inf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_inf_eq_bot : aᶜ ⊓ a = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_inf_self`：compl_inf_self (a : α) : aᶜ ⊓ a = ⊥
-/
theorem compl_inf_eq_bot : aᶜ ⊓ a = ⊥ :=
  compl_inf_self _

@[to_dual (attr := simp)]
/-
**compl_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_top : (⊤ : α)ᶜ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `disjoint_top`：disjoint_top : Disjoint a ⊤ ↔ a = ⊥
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[to_dual (attr := simp)]
/-
**compl_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_bot : (⊥ : α)ᶜ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
· 使用定理 `himp_self`：himp_self : a ⇨ a = ⊤
-/
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [← himp_bot, himp_self]

@[to_dual (attr := simp)]
/-
**le_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_compl_self : a <= aᶜ ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_compl_iff_disjoint_left`：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjo
int b a
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_compl_self : a ≤ aᶜ ↔ a = ⊥ := by
  rw [le_compl_iff_disjoint_left, disjoint_self]

@[to_dual (attr := simp)]
/-
**ne_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_compl_self [Nontrivial α] : a != aᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_compl_self`：le_compl_self : a <= aᶜ ↔ a = ⊥
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
-/
theorem ne_compl_self [Nontrivial α] : a ≠ aᶜ := by
  intro h
  cases le_compl_self.1 (le_of_eq h)
  simp at h

@[to_dual (attr := simp)]
/-
**compl_ne_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_ne_self [Nontrivial α] : aᶜ != a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `ne_compl_self`：ne_compl_self [Nontrivial α] : a != aᶜ
-/
theorem compl_ne_self [Nontrivial α] : aᶜ ≠ a :=
  ne_comm.1 ne_compl_self

@[to_dual (attr := simp)]
/-
**lt_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_compl_self [Nontrivial α] : a < aᶜ ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_compl_self [Nontrivial α] : a < aᶜ ↔ a = ⊥ := by
  rw [lt_iff_le_and_ne]; simp

@[to_dual hnot_hnot_le]
/-
**le_compl_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_compl_compl : a <= aᶜᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_compl_right`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b
 : α}, Disjoint a b → a ≤ bᶜ
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem le_compl_compl : a ≤ aᶜᶜ :=
  disjoint_compl_right.le_compl_right

@[to_dual]
/-
**compl_anti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_anti : Antitone (compl : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_compl_comm`：le_compl_comm : a <= bᶜ ↔ b <= aᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_compl_compl`：le_compl_compl : a <= aᶜᶜ
-/
theorem compl_anti : Antitone (compl : α → α) := fun _ _ h =>
  le_compl_comm.1 <| h.trans le_compl_compl

@[to_dual (attr := gcongr)]
/-
**compl_le_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_anti`：compl_anti : Antitone (compl : α -> α)
-/
theorem compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ :=
  compl_anti h

@[to_dual (attr := simp)]
/-
**compl_compl_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `compl_anti`：compl_anti : Antitone (compl : α -> α)
· 使用定理 `le_compl_compl`：le_compl_compl : a <= aᶜᶜ
-/
theorem compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
  (compl_anti le_compl_compl).antisymm le_compl_compl

@[to_dual (attr := simp)]
/-
**disjoint_compl_compl_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_compl_compl_left_iff : Disjoint aᶜᶜ b ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compl_compl_compl`：compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_compl_compl_left_iff : Disjoint aᶜᶜ b ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]

@[to_dual (attr := simp)]
/-
**disjoint_compl_compl_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_compl_compl_right_iff : Disjoint a bᶜᶜ ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compl_compl_compl`：compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_compl_compl_right_iff : Disjoint a bᶜᶜ ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]

@[to_dual le_hnot_inf_hnot]
/-
**compl_sup_compl_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_sup_compl_le : aᶜ ⊔ bᶜ <= (a ⊓ b)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `compl_anti`：compl_anti : Antitone (compl : α -> α)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem compl_sup_compl_le : aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ :=
  sup_le (compl_anti inf_le_left) <| compl_anti inf_le_right

@[to_dual]
/-
**compl_compl_inf_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `compl_anti`：compl_anti : Antitone (compl : α -> α)
· 使用定理 `compl_sup_compl_le`：compl_sup_compl_le : aᶜ ⊔ bᶜ <= (a ⊓ b)ᶜ
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `compl_sup_distrib`：compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `disjoint_assoc`：disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c)
· 使用定理 `disjoint_compl_compl_left_iff`：disjoint_compl_compl_left_iff : Disjoint 
aᶜᶜ b ↔ Disjoint a b
· 使用定理 `disjoint_left_comm`：disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b
 (a ⊓ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ := by
  refine ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm ?_
  rw [le_compl_iff_disjoint_right, disjoint_assoc, disjoint_compl_compl_left_iff,
    disjoint_left_comm, disjoint_compl_compl_left_iff, ← disjoint_assoc, inf_comm]
  exact disjoint_compl_right

@[to_dual]
/-
**compl_compl_himp_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_himp_iff`：le_himp_iff : a <= b ⇨ c ↔ a ⊓ b <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl_inf_distrib`：compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ =
 aᶜᶜ ⊓ bᶜᶜ
· 使用定理 `compl_anti`：compl_anti : Antitone (compl : α -> α)
· 使用定理 `himp_inf_le`：himp_inf_le : (a ⇨ b) ⊓ a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_compl_comm`：le_compl_comm : a <= bᶜ ↔ b <= aᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `compl_sup_le_himp`：compl_sup_le_himp : aᶜ ⊔ b <= a ⇨ b
· 使用定理 `compl_sup_distrib`：compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
· 使用定理 `disjoint_right_comm`：disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint
 (a ⊓ c) b
· 使用定理 `inf_himp_le`：inf_himp_le : a ⊓ (a ⇨ b) <= b
-/
theorem compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ := by
  apply le_antisymm
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
  · refine le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans ?_)
    rw [compl_sup_distrib, le_compl_iff_disjoint_right, disjoint_right_comm, ←
      le_compl_iff_disjoint_right]
    exact inf_himp_le
/-
**OrderDual.instCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instCoheytingAlgebra : CoheytingAlgebra αᵒᵈ where hnot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
-/
instance OrderDual.instCoheytingAlgebra : CoheytingAlgebra αᵒᵈ where
  hnot := toDual ∘ compl ∘ ofDual
  sdiff a b := toDual (ofDual b ⇨ ofDual a)
  sdiff_le_iff a b c := by rw [sup_comm]; exact le_himp_iff
  top_sdiff := @himp_bot α _

@[to_dual existing]
/-
**OrderDual.instHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instHeytingAlgebra {α : Type u_2} [CoheytingAlgebra α] : Heyting
Algebra αᵒᵈ where compl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a
-/
instance OrderDual.instHeytingAlgebra {α : Type u_2} [CoheytingAlgebra α] : HeytingAlgebra αᵒᵈ where
  compl := toDual ∘ hnot ∘ ofDual
  himp a b := toDual (ofDual b \ ofDual a)
  le_himp_iff a b c := by rw [inf_comm]; exact sdiff_le_iff
  himp_bot := @top_sdiff' α _

@[to_dual (attr := simp)]
/-
**ofDual_hnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_hnot (a : αᵒᵈ) : ofDual (￢a) = (ofDual a)ᶜ
参数：a : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_hnot (a : αᵒᵈ) : ofDual (￢a) = (ofDual a)ᶜ :=
  rfl

@[to_dual (attr := simp)]
/-
**ofDual_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_sdiff (a b : αᵒᵈ) : ofDual (a \ b) = ofDual b ⇨ ofDual a
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_sdiff (a b : αᵒᵈ) : ofDual (a \ b) = ofDual b ⇨ ofDual a :=
  rfl
@[to_dual (attr := simp)]
/-
**toDual_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_compl (a : α) : toDual aᶜ = ￢toDual a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_compl (a : α) : toDual aᶜ = ￢toDual a :=
  rfl

@[to_dual (attr := simp)]
/-
**toDual_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_himp (a b : α) : toDual (a ⇨ b) = toDual b \ toDual a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_himp (a b : α) : toDual (a ⇨ b) = toDual b \ toDual a :=
  rfl
/-
**Prod.instHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instHeytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) where 
himp_bot a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instHeytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) where
    himp_bot a := Prod.ext_iff.2 ⟨himp_bot a.1, himp_bot a.2⟩
/-
**Pi.instHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instHeytingAlgebra {α : ι -> Type*} [forall i, HeytingAlgebra (α i)] : 
HeytingAlgebra (forall i, α i) where himp_bot f
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instHeytingAlgebra {α : ι → Type*} [∀ i, HeytingAlgebra (α i)] :
    HeytingAlgebra (∀ i, α i) where
  himp_bot f := funext fun i ↦ himp_bot (f i)

end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] {a b : α}

@[to_dual existing]
/-
**Prod.instCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instCoheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) 
where sdiff_le_iff _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instCoheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) where
  sdiff_le_iff _ _ _ := and_congr sdiff_le_iff sdiff_le_iff
  top_sdiff a := Prod.ext_iff.2 ⟨top_sdiff' a.1, top_sdiff' a.2⟩

@[to_dual existing]
/-
**Pi.instCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instCoheytingAlgebra {α : ι -> Type*} [forall i, CoheytingAlgebra (α i)
] : CoheytingAlgebra (forall i, α i) where top_sdiff f
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCoheytingAlgebra {α : ι → Type*} [∀ i, CoheytingAlgebra (α i)] :
    CoheytingAlgebra (∀ i, α i) where
  top_sdiff f := funext fun i ↦ top_sdiff' (f i)

end CoheytingAlgebra

section BiheytingAlgebra

variable [BiheytingAlgebra α] {a : α}

/-
**compl_le_hnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_le_hnot : aᶜ <= ￢a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_of_codisjoint`：Disjoint.le_of_codisjoint (hab : Disjoint a b
) (hbc : Codisjoint b c) : a <= c
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
· 使用定理 `codisjoint_hnot_right`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a :
 α}, Codisjoint a (￢a)
-/
theorem compl_le_hnot : aᶜ ≤ ￢a :=
  (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right

end BiheytingAlgebra

/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
/-
**Prop.instHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instHeytingAlgebra : HeytingAlgebra Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Propositions form a Heyting algebra with implication as Heyting implication and 
negation as
complement.
-/
instance Prop.instHeytingAlgebra : HeytingAlgebra Prop :=
  { Prop.instDistribLattice, Prop.instBoundedOrder with
    himp := (· → ·),
    le_himp_iff := fun _ _ _ => and_imp.symm, himp_bot := fun _ => rfl }

@[simp]
/-
**himp_iff_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：himp_iff_imp (p q : Prop) : p ⇨ q ↔ p -> q
参数：p q : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem himp_iff_imp (p q : Prop) : p ⇨ q ↔ p → q :=
  Iff.rfl

@[simp]
/-
**compl_iff_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_iff_not (p : Prop) : pᶜ ↔ ¬p
参数：p : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_iff_not (p : Prop) : pᶜ ↔ ¬p :=
  Iff.rfl

variable (α) in
-- See note [reducible non-instances]
/-- A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise. -/
/-
**LinearOrder.toBiheytingAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.toBiheytingAlgebra [LinearOrder α] [BoundedOrder α] : Biheytin
gAlgebra α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise.
-/
abbrev LinearOrder.toBiheytingAlgebra [LinearOrder α] [BoundedOrder α] : BiheytingAlgebra α :=
  { LinearOrder.toLattice, ‹BoundedOrder α› with
    himp := fun a b => if a ≤ b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true le_top (inf_le_of_right_le h)
      · rw [inf_le_iff, or_iff_left h],
    himp_bot := fun _ => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a ≤ b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      split_ifs with h
      · exact iff_of_true bot_le (le_sup_of_le_left h)
      · rw [le_sup_iff, or_iff_right h],
    top_sdiff := fun _ => if_congr top_le_iff rfl rfl }
/-
**OrderDual.instBiheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instBiheytingAlgebra [BiheytingAlgebra α] : BiheytingAlgebra αᵒᵈ
 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instBiheytingAlgebra [BiheytingAlgebra α] : BiheytingAlgebra αᵒᵈ where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra
/-
**Prod.instBiheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instBiheytingAlgebra [BiheytingAlgebra α] [BiheytingAlgebra β] : Bihe
ytingAlgebra (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instBiheytingAlgebra [BiheytingAlgebra α] [BiheytingAlgebra β] :
    BiheytingAlgebra (α × β) where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra
/-
**Pi.instBiheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instBiheytingAlgebra {α : ι -> Type*} [forall i, BiheytingAlgebra (α i)
] : BiheytingAlgebra (forall i, α i) where __
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instBiheytingAlgebra {α : ι → Type*} [∀ i, BiheytingAlgebra (α i)] :
    BiheytingAlgebra (∀ i, α i) where
  __ := instHeytingAlgebra
  __ := instCoheytingAlgebra

section lift

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedHeytingAlgebra` along an injection. -/
/-
**Function.Injective.generalizedHeytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Functi
on.Injective`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Max α] →       [inst_1 : M
in α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_
4 : Top α] →               [inst_5 : HImp α] →                 [inst_6 : General
izedHeytingAlgebra β] →                   (f : α → β) →                     Func
tion.Injective f →                       (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →     
                    (∀ {x y : α}, f x < f y ↔ x < y) →                          
 (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                             (∀ (a b : α)
, f (a ⊓ b) = f a ⊓ f b) →                               f ⊤ = ⊤ → (∀ (a b : α),
 f (a ⇨ b) = f a ⇨ f b) → GeneralizedHeytingAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (a b : α), f 
(a ⇨ b) = f a ⇨ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `GeneralizedHeytingAlgebra` along an injection.
-/
protected abbrev Function.Injective.generalizedHeytingAlgebra [Max α] [Min α]
    [LE α] [LT α] [Top α] [HImp α] [GeneralizedHeytingAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) :
    GeneralizedHeytingAlgebra α where
  __ := hf.lattice f le lt map_sup map_inf
  le_top a := by
    rw [← le, map_top]
    exact le_top
  le_himp_iff a b c := by
    rw [← le, ← le, map_himp, map_inf, le_himp_iff]

-- See note [reducible non-instances]
/-- Pullback a `GeneralizedCoheytingAlgebra` along an injection. -/
@[to_dual existing (reorder := 3 4, le (x y), lt (x y), map_sup map_inf, map_sdiff (a b))]
/-
**Function.Injective.generalizedCoheytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Func
tion.Injective`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Max α] →       [inst_1 : M
in α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_
4 : Bot α] →               [inst_5 : SDiff α] →                 [inst_6 : Genera
lizedCoheytingAlgebra β] →                   (f : α → β) →                     F
unction.Injective f →                       (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →  
                       (∀ {x y : α}, f x < f y ↔ x < y) →                       
    (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                             (∀ (a b :
 α), f (a ⊓ b) = f a ⊓ f b) →                               f ⊥ = ⊥ → (∀ (a b : 
α), f (a \ b) = f a \ f b) → GeneralizedCoheytingAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (a b : α), f 
(a \ b) = f a \ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `GeneralizedCoheytingAlgebra` along an injection.
-/
protected abbrev Function.Injective.generalizedCoheytingAlgebra [Max α] [Min α]
    [LE α] [LT α] [Bot α] [SDiff α] [GeneralizedCoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedCoheytingAlgebra α where
  __ := hf.lattice f le lt map_sup map_inf
  bot_le a := by
    rw [← le, map_bot]
    exact bot_le
  sdiff_le_iff a b c := by
    rw [← le, ← le, map_sdiff, map_sup, sdiff_le_iff]

-- See note [reducible non-instances]
/-- Pullback a `HeytingAlgebra` along an injection. -/
@[to_dual (reorder := le (x y), lt (x y), map_sup map_inf, map_top map_bot, map_himp (a b))
/-- Pullback a `CoheytingAlgebra` along an injection. -/]
/-
**Function.Injective.heytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injectiv
e`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Max α] →       [inst_1 : M
in α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_
4 : Top α] →               [inst_5 : Bot α] →                 [inst_6 : Compl α]
 →                   [inst_7 : HImp α] →                     [inst_8 : HeytingAl
gebra β] →                       (f : α → β) →                         Function.
Injective f →                           (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →      
                       (∀ {x y : α}, f x < f y ↔ x < y) →                       
        (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                                 (
∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →                                   f ⊤ = ⊤ 
→                                     f ⊥ = ⊥ →                                 
      (∀ (a : α), f aᶜ = (f a)ᶜ) →                                         (∀ (a
 b : α), f (a ⇨ b) = f a ⇨ f b) → HeytingAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (a : α), f aᶜ
 = (f a)ᶜ；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Injective.heytingAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [HImp α] [HeytingAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : HeytingAlgebra α where
  __ := hf.generalizedHeytingAlgebra f le lt map_sup map_inf map_top map_himp
  bot_le a := by
    rw [← le, map_bot]
    exact bot_le
  himp_bot a := hf <| by rw [map_himp, map_compl, map_bot, himp_bot]

-- See note [reducible non-instances]
/-- Pullback a `BiheytingAlgebra` along an injection. -/
@[to_dual self (reorder := 3 4, 7 8, 9 10, 11 12, le (x y), lt (x y),
  map_sup map_inf, map_top map_bot, map_compl map_hnot, map_himp map_sdiff (a b))]
/-
**Function.Injective.biheytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Max α] →       [inst_1 : M
in α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_
4 : Top α] →               [inst_5 : Bot α] →                 [inst_6 : Compl α]
 →                   [inst_7 : HNot α] →                     [inst_8 : HImp α] →
                       [inst_9 : SDiff α] →                         [inst_10 : B
iheytingAlgebra β] →                           (f : α → β) →                    
         Function.Injective f →                               (∀ {x y : α}, f x 
≤ f y ↔ x ≤ y) →                                 (∀ {x y : α}, f x < f y ↔ x < y
) →                                   (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →    
                                 (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →         
                              f ⊤ = ⊤ →                                         
f ⊥ = ⊥ →                                           (∀ (a : α), f aᶜ = (f a)ᶜ) →
                                             (∀ (a : α), f (￢a) = ￢f a) →       
                                        (∀ (a b : α), f (a ⇨ b) = f a ⇨ f b) →  
                                               (∀ (a b : α), f (a \ b) = f a \ f
 b) → BiheytingAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (a : α), f aᶜ
 = (f a)ᶜ；∀ (a : α), f (￢a) = ￢f a；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b；∀ (a b : α
), f (a \ b) = f a \ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : CoheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a
-/
protected abbrev Function.Injective.biheytingAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [HNot α] [HImp α] [SDiff α] [BiheytingAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    BiheytingAlgebra α where
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `GeneralizedHeytingAlgebra` across an `Equiv`. -/
/-
**Equiv.generalizedHeytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [GeneralizedHeytingAlgebra β] → 
GeneralizedHeytingAlgebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `GeneralizedHeytingAlgebra` across an `Equiv`.
-/
protected abbrev generalizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra α := by
  let lattice := e.lattice
  let top := e.top
  let himp := e.himp
  apply e.injective.generalizedHeytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

/-- Transfer `GeneralizedCoheytingAlgebra` across an `Equiv`. -/
/-
**Equiv.generalizedCoheytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [GeneralizedCoheytingAlgebra β] 
→ GeneralizedCoheytingAlgebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `GeneralizedCoheytingAlgebra` across an `Equiv`.
-/
protected abbrev generalizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra α := by
  let lattice := e.lattice
  let bot := e.bot
  let sdiff := e.sdiff
  apply e.injective.generalizedCoheytingAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

/-- Transfer `HeytingAlgebra` across an `Equiv`. -/
/-
**Equiv.heytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [HeytingAlgebra β] → HeytingAlge
bra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `HeytingAlgebra` across an `Equiv`.
-/
protected abbrev heytingAlgebra [HeytingAlgebra β] : HeytingAlgebra α := by
  let generalizedHeytingAlgebra := e.generalizedHeytingAlgebra
  let bot := e.bot
  let compl := e.compl
  apply e.injective.heytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CoheytingAlgebra` across an `Equiv`. -/
/-
**Equiv.coheytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [CoheytingAlgebra β] → Coheyting
Algebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CoheytingAlgebra` across an `Equiv`.
-/
protected abbrev coheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra α := by
  let generalizedCoheytingAlgebra := e.generalizedCoheytingAlgebra
  let top := e.top
  let hnot := e.hnot
  apply e.injective.coheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `BiheytingAlgebra` across an `Equiv`. -/
/-
**Equiv.biheytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [BiheytingAlgebra β] → Biheyting
Algebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `BiheytingAlgebra` across an `Equiv`.
-/
protected abbrev biheytingAlgebra [BiheytingAlgebra β] : BiheytingAlgebra α := by
  let heytingAlgebra := e.heytingAlgebra
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.biheytingAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace PUnit

variable (a b : PUnit.{u + 1})

/-
**PUnit.instBiheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：instBiheytingAlgebra : BiheytingAlgebra PUnit.{u + 1}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance instBiheytingAlgebra : BiheytingAlgebra PUnit.{u + 1} :=
  { PUnit.instLinearOrder.{u} with
    top := unit,
    bot := unit,
    sup := fun _ _ => unit,
    inf := fun _ _ => unit,
    compl := fun _ => unit,
    sdiff := fun _ _ => unit,
    hnot := fun _ => unit,
    himp := fun _ _ => unit,
    le_top := fun _ => trivial,
    le_sup_left := fun _ _ => trivial,
    le_sup_right := fun _ _ => trivial,
    sup_le := fun _ _ _ _ _ => trivial,
    inf_le_left := fun _ _ => trivial,
    inf_le_right := fun _ _ => trivial,
    le_inf := fun _ _ _ _ _ => trivial,
    bot_le := fun _ => trivial,
    le_himp_iff := fun _ _ _ => Iff.rfl,
    himp_bot := fun _ => rfl,
    top_sdiff := fun _ => rfl,
    sdiff_le_iff := fun _ _ _ => Iff.rfl }

@[to_dual (attr := simp)]
/-
**PUnit.top_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：top_eq : (⊤ : PUnit) = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_eq : (⊤ : PUnit) = unit :=
  rfl

@[to_dual (attr := simp)]
/-
**PUnit.sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：sup_eq : a ⊔ b = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_eq : a ⊔ b = unit :=
  rfl

@[to_dual (attr := simp)]
/-
**PUnit.hnot_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：hnot_eq : ￢a = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hnot_eq : ￢a = unit :=
  rfl

@[to_dual (attr := simp)]
/-
**PUnit.himp_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：himp_eq : a ⇨ b = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem himp_eq : a ⇨ b = unit :=
  rfl

end PUnit

