/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Typeclasses expressing `IsBot 1` and `IsBot 0`
-/

public section

/-- A typeclass expressing that the `0` of a type is a bottom element. In a partial `OrderBot`, this
is equivalent to `⊥ = 0`. -/
/-
**IsBotZeroClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [LE α] → [Zero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass expressing that the `0` of a type is a bottom element. In a partial 
`OrderBot`, this
is equivalent to `⊥ = 0`.
-/
class IsBotZeroClass (α : Type*) [LE α] [Zero α] : Prop where
  isBot_zero : IsBot (0 : α)

/-- A typeclass expressing that the `1` of a type is a bottom element. In a partial `OrderBot`, this
is equivalent to `⊥ = 1`. -/
@[to_additive existing]
/-
**IsBotOneClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [LE α] → [One α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass expressing that the `1` of a type is a bottom element. In a partial 
`OrderBot`, this
is equivalent to `⊥ = 1`.
-/
class IsBotOneClass (α : Type*) [LE α] [One α] : Prop where
  isBot_one : IsBot (1 : α)

variable {α : Type*} {a b : α}

section LE
variable [LE α] [One α] [IsBotOneClass α]

@[to_additive]
/-
**isBot_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBot_one : IsBot (1 : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBotOneClass.isBot_one`：∀ {α : Type u_1} {inst : LE α} {inst_1 : One α}
 [self : IsBotOneClass α], IsBot 1
-/
theorem isBot_one : IsBot (1 : α) :=
  IsBotOneClass.isBot_one

@[to_additive (attr := simp) zero_le]
/-
**one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le {a : α} : 1 <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_one`：isBot_one : IsBot (1 : α)
-/
theorem one_le {a : α} : 1 ≤ a :=
  isBot_one a

@[deprecated (since := "2026-05-27")]
alias zero_le' := zero_le

variable (α) in
/-- Create an `OrderBot` instance, setting `1` as the bottom element. -/
@[expose, to_additive (attr := instance_reducible)
/-- Create an `OrderBot` instance, setting `0` as the bottom element. -/]
/-
**IsBotOneClass.toOrderBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBotOneClass.toOrderBot : OrderBot α where bot
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
def IsBotOneClass.toOrderBot : OrderBot α where
  bot := 1
  bot_le _ := one_le

end LE

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [LE α] [Zero α] [One α] [IsBotZeroClass α] : ZeroLEOneClass α where
  zero_le_one := zero_le

section Preorder
variable [Preorder α] [One α] [IsBotOneClass α]

@[to_additive (attr := simp) not_lt_zero]
/-
**not_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_lt_one : ¬ a < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem not_lt_one : ¬ a < 1 := one_le.not_gt

@[deprecated (since := "2026-05-07")]
alias not_lt_zero' := not_lt_zero

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.
/-
**one_lt_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_of_gt (h : a < b) : 1 < b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem one_lt_of_gt (h : a < b) : 1 < b :=
  one_le.trans_lt h

@[to_additive] alias LT.lt.one_lt := one_lt_of_gt

@[to_additive]
/-
**ne_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_one_of_lt (h : a < b) : b != 1
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.one_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : O
ne α] [IsBotOneClass α], a < b → 1 < b
-/
theorem ne_one_of_lt (h : a < b) : b ≠ 1 :=
  h.one_lt.ne'

@[to_additive] alias LT.lt.ne_one := ne_one_of_lt

end Preorder

section PartialOrder
variable [PartialOrder α] [One α] [IsBotOneClass α]

-- Not `simp`, as different types might have a different preferred form.
@[to_additive]
/-
**bot_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_eq_one [OrderBot α] : (⊥ : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBot.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsBot a → a = ⊥
· 使用定理 `isBot_one`：isBot_one : IsBot (1 : α)
-/
theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 := isBot_one.eq_bot.symm

@[deprecated (since := "2026-05-07")]
alias bot_eq_zero'' := bot_eq_zero

@[to_additive (attr := simp)]
/-
**le_one_iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_one_iff_eq_one : a <= 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  one_le.ge_iff_eq'

-- TODO: deprecate
alias le_zero_iff := nonpos_iff_eq_zero

@[to_additive] alias ⟨eq_one_of_le_one, _⟩ := le_one_iff_eq_one
@[to_additive] alias LE.le.eq_one := eq_one_of_le_one

@[to_additive]
/-
**one_lt_iff_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_iff_ne_one : 1 < a ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
-/
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  one_le.lt_iff_ne.trans ne_comm

-- TODO: deprecate
alias zero_lt_iff := pos_iff_ne_zero

@[to_additive] alias ⟨_, one_lt_of_ne_one⟩ := one_lt_iff_ne_one
@[to_additive] alias Ne.one_lt := one_lt_of_ne_one

@[to_additive]
/-
**eq_one_or_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a := one_le.eq_or_lt'

@[to_additive]
/-
**one_notMem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_notMem_iff {s : Set α} : 1 ∉ s ↔ forall x in s, 1 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_notMem_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBo
t α] {s : Set α}, ⊥ ∉ s ↔ ∀ x ∈ s, ⊥ < x
-/
lemma one_notMem_iff {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, 1 < x :=
  let := IsBotOneClass.toOrderBot α
  bot_notMem_iff

@[deprecated (since := "2026-02-17")] alias NE.ne.pos := Ne.pos
@[deprecated (since := "2026-02-17")] alias NE.ne.one_lt := Ne.one_lt

end PartialOrder

section LinearOrder
variable [LinearOrder α] [One α] [IsBotOneClass α]

@[to_additive]
/-
**one_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_min (a : α) : min 1 a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_min (a : α) : min 1 a = 1 := by simp

@[to_additive]
/-
**min_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_one (a : α) : min a 1 = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem min_one (a : α) : min a 1 = 1 := by simp

@[to_additive]
/-
**one_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_max (a : α) : max 1 a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_max (a : α) : max 1 a = a := by simp

@[to_additive]
/-
**max_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_one (a : α) : max a 1 = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem max_one (a : α) : max a 1 = a := by simp

@[to_additive (attr := simp)]
/-
**max_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_eq_one {a b : α} : max a b = 1 ↔ a = 1 ∧ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_bot`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α
] {a b : α}, max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥
-/
theorem max_eq_one {a b : α} : max a b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsBotOneClass.toOrderBot α
  max_eq_bot

@[to_additive (attr := simp)]
/-
**min_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_eq_one {a b : α} : min a b = 1 ↔ a = 1 ∨ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `min_eq_bot`：min_eq_bot {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥
-/
theorem min_eq_one {a b : α} : min a b = 1 ↔ a = 1 ∨ b = 1 :=
  let := IsBotOneClass.toOrderBot α
  min_eq_bot

end LinearOrder

namespace NeZero
variable [Zero α]

/-
**NeZero.of_gt** 是 Mathlib 中的一个定理，位于命名空间 `NeZero`。
形式化陈述：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
-/
theorem of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero b :=
  ⟨h.ne_zero⟩
/-
**NeZero.pos** 是 Mathlib 中的一个定理，位于命名空间 `NeZero`。
形式化陈述：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] : 0 < a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
theorem pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] : 0 < a :=
  NeZero.out.pos

-- 1 < p is still an often-used `Fact`, due to `Nat.Prime` implying it, and it implying `Nontrivial`
-- on `ZMod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
/-
**NeZero.** 是 Mathlib 中的一个实例，位于命名空间 `NeZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) of_gt' [Preorder α] [IsBotZeroClass α] [One α]
    [Fact (1 < a)] : NeZero a := of_gt <| @Fact.out (1 < a) _
/-
**NeZero.of_ge** 是 Mathlib 中的一个定理，位于命名空间 `NeZero`。
形式化陈述：of_ge [PartialOrder α] [IsBotZeroClass α] [NeZero a] (h : a <= b) : NeZero
 b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
-/
theorem of_ge [PartialOrder α] [IsBotZeroClass α] [NeZero a] (h : a ≤ b) : NeZero b :=
  ⟨((pos a).trans_le h).ne_zero⟩

end NeZero

