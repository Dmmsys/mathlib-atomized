/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.DeriveFintype  -- shake: keep (deriving handlers not tracked yet)
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Sign type

This file defines the type of signs $\{-1, 0, 1\}$ and its basic arithmetic instances.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false in
-- Don't generate unnecessary `sizeOf_spec` lemmas which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of signs. -/
/-
**SignType** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of signs.
-/
inductive SignType
  | zero
  | neg
  | pos
  deriving DecidableEq, Inhabited, Fintype

namespace SignType

/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero SignType :=
  ⟨zero⟩
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One SignType :=
  ⟨pos⟩
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg SignType :=
  ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | pos => neg⟩

@[simp]
/-
**SignType.zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：zero_eq_zero : zero = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_eq_zero : zero = 0 :=
  rfl

@[simp]
/-
**SignType.neg_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_eq_neg_one : neg = -1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_eq_neg_one : neg = -1 :=
  rfl

@[simp]
/-
**SignType.pos_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：pos_eq_one : pos = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pos_eq_one : pos = 1 :=
  rfl
/-
**SignType.trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1
参数：a : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1 := by
  cases a <;> simp
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul SignType :=
  ⟨fun x y =>
    match x with
    | neg => -y
    | zero => zero
    | pos => y⟩

/-- The less-than-or-equal relation on signs. -/
/-
**SignType.LE** 是 Mathlib 中的一个归纳类型，位于命名空间 `SignType`。
形式化陈述：SignType → SignType → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The less-than-or-equal relation on signs.
-/
protected inductive LE : SignType → SignType → Prop
  | of_neg (a) : SignType.LE neg a
  | zero : SignType.LE zero zero
  | of_pos (a) : SignType.LE a pos
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE SignType :=
  ⟨SignType.LE⟩
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableLE SignType := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

/-- We can define a `Field` instance on `SignType`, but it's not mathematically sensible,
so we only define the `CommGroupWithZero`. -/
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can define a `Field` instance on `SignType`, but it's not mathematically sens
ible,
so we only define the `CommGroupWithZero`.
-/
instance : CommGroupWithZero SignType where
  inv := id
  mul_zero a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_inv_cancel a ha := by cases a <;> trivial
  mul_comm := by decide
  mul_assoc := by decide
  exists_pair_ne := ⟨0, 1, by rintro ⟨_⟩⟩
  inv_zero := rfl
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder SignType where
  le_refl a := by cases a <;> constructor
  le_total := by decide
  le_antisymm := by decide
  le_trans := by decide
  toDecidableLE := instDecidableLE
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder SignType where
  top := 1
  le_top := LE.of_pos
  bot := -1
  bot_le :=
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
    Added `by exact`, but don't understand why it was needed. -/
    by exact LE.of_neg
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg SignType where
  neg_neg := by rintro ⟨_⟩ <;> rfl
  neg_mul := by rintro ⟨_⟩ ⟨_⟩ <;> rfl
  mul_neg := by rintro ⟨_⟩ ⟨_⟩ <;> rfl

/-- `SignType` is equivalent to `Fin 3`. -/
/-
**SignType.fin3Equiv** 是 Mathlib 中的一个定义，位于命名空间 `SignType`。
形式化陈述：fin3Equiv : SignType ≃* Fin 3 where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SignType` is equivalent to `Fin 3`.
-/
def fin3Equiv : SignType ≃* Fin 3 where
  toFun a :=
    match a with
    | 0 => ⟨0, by simp⟩
    | 1 => ⟨1, by simp⟩
    | -1 => ⟨2, by simp⟩
  invFun a :=
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => -1
  left_inv a := by cases a <;> rfl
  right_inv a :=
    match a with
    | ⟨0, _⟩ => by simp
    | ⟨1, _⟩ => by simp
    | ⟨2, _⟩ => by simp
  map_mul' a b := by
    cases a <;> cases b <;> rfl

section CaseBashing

/-
**SignType.nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：nonneg_iff {a : SignType} : 0 <= a ↔ a = 0 ∨ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem nonneg_iff {a : SignType} : 0 ≤ a ↔ a = 0 ∨ a = 1 := by decide +revert
/-
**SignType.nonneg_iff_ne_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：nonneg_iff_ne_neg_one {a : SignType} : 0 <= a ↔ a != -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem nonneg_iff_ne_neg_one {a : SignType} : 0 ≤ a ↔ a ≠ -1 := by decide +revert
/-
**SignType.neg_one_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_one_lt_iff {a : SignType} : -1 < a ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem neg_one_lt_iff {a : SignType} : -1 < a ↔ 0 ≤ a := by decide +revert
/-
**SignType.nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：nonpos_iff {a : SignType} : a <= 0 ↔ a = -1 ∨ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem nonpos_iff {a : SignType} : a ≤ 0 ↔ a = -1 ∨ a = 0 := by decide +revert
/-
**SignType.nonpos_iff_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：nonpos_iff_ne_one {a : SignType} : a <= 0 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem nonpos_iff_ne_one {a : SignType} : a ≤ 0 ↔ a ≠ 1 := by decide +revert
/-
**SignType.lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：lt_one_iff {a : SignType} : a < 1 ↔ a <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem lt_one_iff {a : SignType} : a < 1 ↔ a ≤ 0 := by decide +revert

@[simp]
/-
**SignType.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_iff {a : SignType} : a < 0 ↔ a = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem neg_iff {a : SignType} : a < 0 ↔ a = -1 := by decide +revert

@[simp]
/-
**SignType.le_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：le_neg_one_iff {a : SignType} : a <= -1 ↔ a = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem le_neg_one_iff {a : SignType} : a ≤ -1 ↔ a = -1 :=
  le_bot_iff

@[simp]
/-
**SignType.pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：pos_iff {a : SignType} : 0 < a ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem pos_iff {a : SignType} : 0 < a ↔ a = 1 := by decide +revert

@[simp]
/-
**SignType.one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：one_le_iff {a : SignType} : 1 <= a ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
theorem one_le_iff {a : SignType} : 1 ≤ a ↔ a = 1 :=
  top_le_iff

@[simp]
/-
**SignType.neg_one_le** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_one_le (a : SignType) : -1 <= a
参数：a : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem neg_one_le (a : SignType) : -1 ≤ a :=
  bot_le

@[simp]
/-
**SignType.le_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：le_one (a : SignType) : a <= 1
参数：a : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem le_one (a : SignType) : a ≤ 1 :=
  le_top

@[simp]
/-
**SignType.not_lt_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：not_lt_neg_one (a : SignType) : ¬a < -1
参数：a : SignType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
-/
theorem not_lt_neg_one (a : SignType) : ¬a < -1 :=
  not_lt_bot

@[simp]
/-
**SignType.not_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：not_one_lt (a : SignType) : ¬1 < a
参数：a : SignType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
-/
theorem not_one_lt (a : SignType) : ¬1 < a :=
  not_top_lt

@[simp]
/-
**SignType.self_eq_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：self_eq_neg_iff {a : SignType} : a = -a ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem self_eq_neg_iff {a : SignType} : a = -a ↔ a = 0 := by decide +revert

@[simp]
/-
**SignType.neg_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_eq_self_iff {a : SignType} : -a = a ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem neg_eq_self_iff {a : SignType} : -a = a ↔ a = 0 := by decide +revert

@[simp]
/-
**SignType.neg_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_eq_zero_iff {a : SignType} : -a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem neg_eq_zero_iff {a : SignType} : -a = 0 ↔ a = 0 := by decide +revert

@[simp]
/-
**SignType.neg_one_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：neg_one_lt_one : (-1 : SignType) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_lt_top`：bot_lt_top : (⊥ : α) < ⊤
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem neg_one_lt_one : (-1 : SignType) < 1 :=
  bot_lt_top

@[simp]
/-
**SignType.neg_le_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：∀ {a b : SignType}, -a ≤ -b ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
protected theorem neg_le_neg_iff {a b : SignType} : -a ≤ -b ↔ b ≤ a := by decide +revert

@[simp]
/-
**SignType.neg_lt_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：∀ {a b : SignType}, -a < -b ↔ b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
protected theorem neg_lt_neg_iff {a b : SignType} : -a < -b ↔ b < a := by decide +revert

end CaseBashing

section cast

variable {α : Type*} [Zero α] [One α] [Neg α]

/-- Turn a `SignType` into zero, one, or minus one. This is a coercion instance. -/
@[coe]
/-
**SignType.cast** 是 Mathlib 中的一个定义，位于命名空间 `SignType`。
形式化陈述：{α : Type u_1} → [Zero α] → [One α] → [Neg α] → SignType → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a `SignType` into zero, one, or minus one. This is a coercion instance.
-/
def cast : SignType → α
  | zero => 0
  | pos => 1
  | neg => -1

/--
This can't be a `CoeTail` or `Coe` instance because we don't want it to fire when `SignType` isn't
involved in the coercion (or `CoeHead` or `CoeOut` because of `outParam`s). The only other
user-exposed option is `CoeDep` then, which allows us to match on both given and expected type.
-/
/-
**SignType.** 是 Mathlib 中的一个实例，位于命名空间 `SignType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can't be a `CoeTail` or `Coe` instance because we don't want it to fire whe
n `SignType` isn't
involved in the coercion (or `CoeHead` or `CoeOut` because of `outParam`s). The 
only other
user-exposed option is `CoeDep` then, which allows us to match on both given and
 expected type.
-/
instance (s : SignType) : CoeDep SignType s α :=
  ⟨cast s⟩

/-- Casting out of `SignType` respects composition with functions preserving `0, 1, -1`. -/
/-
**SignType.map_cast'** 是 Mathlib 中的一个引理，位于命名空间 `SignType`。
形式化陈述：map_cast' {β : Type*} [One β] [Neg β] [Zero β] (f : α -> β) (h₁ : f 1 = 1)
 (h₂ : f 0 = 0) (h₃ : f (-1) = -1) (s : SignType) : f s = s
参数：f : α -> β；h₁ : f 1 = 1；h₂ : f 0 = 0；h₃ : f (-1) = -1；s : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Casting out of `SignType` respects composition with functions preserving `0, 1, 
-1`.
-/
lemma map_cast' {β : Type*} [One β] [Neg β] [Zero β]
    (f : α → β) (h₁ : f 1 = 1) (h₂ : f 0 = 0) (h₃ : f (-1) = -1) (s : SignType) :
    f s = s := by
  cases s <;> simp only [SignType.cast, h₁, h₂, h₃]

/-- Casting out of `SignType` respects composition with suitable bundled homomorphism types. -/
/-
**SignType.map_cast** 是 Mathlib 中的一个引理，位于命名空间 `SignType`。
形式化陈述：map_cast {α β F : Type*} [AddGroupWithOne α] [One β] [SubtractionMonoid β]
 [FunLike F α β] [AddMonoidHomClass F α β] [OneHomClass F α β] (f : F) (s : Sign
Type) : f s = s
参数：f : F；s : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SignType.map_cast'`：map_cast' {β : Type*} [One β] [Neg β] [Zero β] (f : 
α -> β) (h₁ : f 1 = 1) (h₂ : f 0 = 0) (h₃ : f (-1) = -1) (s : SignType) : f s = 
s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…

--- 原说明 ---
Casting out of `SignType` respects composition with suitable bundled homomorphis
m types.
-/
lemma map_cast {α β F : Type*} [AddGroupWithOne α] [One β] [SubtractionMonoid β]
    [FunLike F α β] [AddMonoidHomClass F α β] [OneHomClass F α β] (f : F) (s : SignType) :
    f s = s := by
  apply map_cast' <;> simp

@[simp]
/-
**SignType.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：coe_zero : ↑(0 : SignType) = (0 : α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ↑(0 : SignType) = (0 : α) :=
  rfl

@[simp]
/-
**SignType.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：coe_one : ↑(1 : SignType) = (1 : α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : SignType) = (1 : α) :=
  rfl

@[simp]
/-
**SignType.coe_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `SignType`。
形式化陈述：coe_neg_one : ↑(-1 : SignType) = (-1 : α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg_one : ↑(-1 : SignType) = (-1 : α) :=
  rfl

@[simp, norm_cast]
/-
**SignType.coe_neg** 是 Mathlib 中的一个引理，位于命名空间 `SignType`。
形式化陈述：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s : SignType) : (↑(-s) 
: α) = -↑s
参数：s : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s : SignType) :
    (↑(-s) : α) = -↑s := by
  cases s <;> simp

end cast

end SignType

variable {α : Type*}

open SignType

section Preorder

variable [Zero α] [Preorder α] [DecidableLT α] {a : α}

/-- The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise. -/
/-
**SignType.sign** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SignType.sign : α ->o SignType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise.
-/
def SignType.sign : α →o SignType :=
  ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h => by
    dsimp
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;> try constructor
    · cases lt_irrefl 0 (h₁.trans <| h.trans_lt h₃)
    · cases h₂ (h₁.trans_le h)
    · cases h₄ (h.trans_lt h₃)⟩
/-
**sign_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) :=
  rfl

@[simp]
/-
**sign_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_zero : sign (0 : α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_zero : sign (0 : α) = 0 := by simp [sign_apply]

@[simp]
/-
**sign_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_pos (ha : 0 < a) : sign a = 1
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_apply`：sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sign_pos (ha : 0 < a) : sign a = 1 := by rwa [sign_apply, if_pos]

@[simp]
/-
**sign_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_neg (ha : a < 0) : sign a = -1
参数：ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_apply`：sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sign_neg (ha : a < 0) : sign a = -1 := by rwa [sign_apply, if_neg <| asymm ha, if_pos]
/-
**sign_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_eq_one_iff : sign a = 1 ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `sign_apply`：sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
-/
theorem sign_eq_one_iff : sign a = 1 ↔ 0 < a := by
  refine ⟨fun h => ?_, fun h => sign_pos h⟩
  by_contra hn
  rw [sign_apply, if_neg hn] at h
  split_ifs at h
/-
**sign_eq_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `sign_apply`：sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
-/
theorem sign_eq_neg_one_iff : sign a = -1 ↔ a < 0 := by
  refine ⟨fun h => ?_, fun h => sign_neg h⟩
  rw [sign_apply] at h
  split_ifs at h
  assumption

end Preorder

section LinearOrder

variable [Zero α] [LinearOrder α] {a : α}

/-- `SignType.sign` respects strictly monotone zero-preserving maps. -/
/-
**StrictMono.sign_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.sign_comp {β F : Type*} [Zero β] [Preorder β] [DecidableLT β] [
FunLike F α β] [ZeroHomClass F α β] {f : F} (hf : StrictMono f) (a : α) : sign (
f a) = sign a
参数：hf : StrictMono f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`SignType.sign` respects strictly monotone zero-preserving maps.
-/
lemma StrictMono.sign_comp {β F : Type*} [Zero β] [Preorder β] [DecidableLT β]
    [FunLike F α β] [ZeroHomClass F α β] {f : F} (hf : StrictMono f) (a : α) :
    sign (f a) = sign a := by
  simp only [sign_apply, ← map_zero f, hf.lt_iff_lt]

@[simp]
/-
**sign_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_eq_zero_iff : sign a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `sign_apply`：sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sign_eq_zero_iff : sign a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs at h with h_1 h_2
  cases h
  exact (le_of_not_gt h_1).eq_of_not_lt h_2
/-
**sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_ne_zero : sign a != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sign_eq_zero_iff`：sign_eq_zero_iff : sign a = 0 ↔ a = 0
-/
theorem sign_ne_zero : sign a ≠ 0 ↔ a ≠ 0 :=
  sign_eq_zero_iff.not

@[simp]
/-
**sign_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_nonneg_iff : 0 <= sign a ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem sign_nonneg_iff : 0 ≤ sign a ↔ 0 ≤ a := by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.le]
  · simp [← h]
  · simp [h, h.not_ge]

@[simp]
/-
**sign_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_nonpos_iff : sign a <= 0 ↔ a <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem sign_nonpos_iff : sign a ≤ 0 ↔ a ≤ 0 := by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.not_ge]
  · simp [← h]
  · simp [h, h.le]
/-
**sign_eq_sign_or_eq_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sign_eq_sign_or_eq_neg {b : α} (ha : a != 0) (hb : b != 0) : sign a = sign
 b ∨ sign a = -sign b
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SignType.trichotomy`：trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma sign_eq_sign_or_eq_neg {b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    sign a = sign b ∨ sign a = -sign b := by
  rcases trichotomy (sign a) with hsa | hsa | hsa <;>
    rcases trichotomy (sign b) with hsb | hsb | hsb <;>
    simp_all

end LinearOrder

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [DecidableLT α] [Nontrivial α]

/-
**sign_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_one : sign (1 : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
theorem sign_one : sign (1 : α) = 1 :=
  sign_pos zero_lt_one

end OrderedSemiring

section AddGroup

variable [AddGroup α] [Preorder α] [DecidableLT α]

/-
**Left.sign_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) = -sign a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) = -sign a := by
  simp_rw [sign_apply, Left.neg_pos_iff, Left.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp
/-
**Right.sign_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.sign_neg [AddRightStrictMono α] (a : α) : sign (-a) = -sign a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem Right.sign_neg [AddRightStrictMono α] (a : α) :
    sign (-a) = -sign a := by
  simp_rw [sign_apply, Right.neg_pos_iff, Right.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

end AddGroup

/-
**Int.sign_eq_sign** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.sign_eq_sign (n : Int) : Int.sign n = SignType.sign n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
-/
theorem Int.sign_eq_sign (n : ℤ) : Int.sign n = SignType.sign n := by
  obtain (n | _) | _ := n <;> simp [sign, negSucc_lt_zero]
