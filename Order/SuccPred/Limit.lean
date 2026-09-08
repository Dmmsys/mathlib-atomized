/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Successor and predecessor limits

We define the predicate `Order.IsSuccPrelimit` for "successor pre-limits", values that don't cover
any others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsPredPrelimit` analogously, and prove basic results.

For some applications, it is desirable to exclude minimal elements from being successor limits, or
maximal elements from being predecessor limits. As such, we also provide `Order.IsSuccLimit` and
`Order.IsPredLimit`, which exclude these cases.
-/

@[expose] public section

variable {α : Type*} {a b : α}

namespace Order

open Function Set OrderDual

/-! ### Successor and predecessor limits -/

section LT

variable [LT α]

/-- A successor pre-limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor pre-limit can't be the successor of anything
smaller.

Use `IsSuccLimit` if you want to exclude the case of a minimal element. -/
@[to_dual
/-- A predecessor pre-limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor pre-limit can't be the predecessor of
anything smaller.

Use `IsPredLimit` to exclude the case of a maximal element. -/]
/-
**Order.IsSuccPrelimit** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：IsSuccPrelimit (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsSuccPrelimit (a : α) : Prop :=
  ∀ b, ¬b ⋖ a

@[to_dual]
/-
**Order.not_isSuccPrelimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_iff {a : α} : ¬IsSuccPrelimit a ↔ exists b, b ⋖ a
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isSuccPrelimit_iff {a : α} : ¬IsSuccPrelimit a ↔ ∃ b, b ⋖ a := by
  simp [IsSuccPrelimit]

/-- The lemma formerly named `not_isSuccPrelimit_iff` is now
`not_isSuccPrelimit_iff_succ_eq` -/
@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit_iff_exists_covBy := not_isSuccPrelimit_iff

/-- The lemma formerly named `not_isPredPrelimit_iff` is now
`not_isPredPrelimit_iff_pred_eq` -/
@[to_dual existing, deprecated (since := "2026-04-19")]
alias not_isPredPrelimit_iff_exists_covBy := not_isPredPrelimit_iff

@[to_dual (attr := simp)]
/-
**Order.IsSuccPrelimit.of_dense** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimit`
。
形式化陈述：∀ {α : Type u_1} [inst : LT α] [DenselyOrdered α] (a : α), Order.IsSuccPre
limit a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_covBy`：not_covBy [DenselyOrdered α] : ¬a ⋖ b
-/
theorem IsSuccPrelimit.of_dense [DenselyOrdered α] (a : α) : IsSuccPrelimit a := fun _ => not_covBy

@[to_dual (attr := simp)]
/-
**Order.isSuccPrelimit_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_toDual_iff : IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSuccPrelimit_toDual_iff : IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a := by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[to_dual]
alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff

end LT

section Preorder

variable [Preorder α]

/-- A successor limit is a value that isn't minimal and doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller.

Use `IsSuccPrelimit` if you want to include the case of a minimal element. -/
@[mk_iff]
/-
**Order.IsSuccLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：{α : Type u_1} → [Preorder α] → α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A successor limit is a value that isn't minimal and doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the succe
ssor of anything
smaller.

Use `IsSuccPrelimit` if you want to include the case of a minimal element.
-/
structure IsSuccLimit (a : α) : Prop where
  /-- Successor limits aren't minimal. -/
  protected not_isMin : ¬ IsMin a
  /-- Successor limits don't cover any other elements. -/
  protected isSuccPrelimit : IsSuccPrelimit a

/-- A predecessor limit is a value that isn't maximal and isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything larger.

Use `IsPredPrelimit` if you want to include the case of a maximal element. -/
@[mk_iff, to_dual existing]
/-
**Order.IsPredLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：{α : Type u_1} → [Preorder α] → α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predecessor limit is a value that isn't maximal and isn't covered by any other
.

It's so named because in a predecessor order, a predecessor limit can't be the p
redecessor of
anything larger.

Use `IsPredPrelimit` if you want to include the case of a maximal element.
-/
structure IsPredLimit (a : α) : Prop where
  /-- Predecessor limits aren't maximal. -/
  protected not_isMax : ¬ IsMax a
  /-- Predecessor limits aren't covered by any other elements. -/
  protected isPredPrelimit : IsPredPrelimit a

attribute [to_dual existing] isSuccLimit_iff
attribute [simp] IsSuccLimit.isSuccPrelimit IsPredLimit.isPredPrelimit

@[to_dual (attr := simp)]
/-
**Order.isSuccLimit_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [isSuccLimit_iff, isPredLimit_iff]

@[to_dual] alias ⟨_, IsPredLimit.dual⟩ := isSuccLimit_toDual_iff

@[to_dual]
/-
**Order.not_isSuccLimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_iff : ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccLimit_iff`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Ord
er.IsSuccLimit a ↔ ¬IsMin a ∧ Order.IsSuccPrelimit a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_isSuccLimit_iff : ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a := by
  rw [isSuccLimit_iff, not_and_or, not_not]

@[deprecated IsPredLimit.isPredPrelimit (since := "2026-02-22")]
/-
**Order.not_isPredLimit_of_not_isPredPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isPredLimit_of_not_isPredPrelimit : ¬ IsPredPrelimit a -> ¬ IsPredLimi
t a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
theorem not_isPredLimit_of_not_isPredPrelimit : ¬ IsPredPrelimit a → ¬ IsPredLimit a :=
  mt IsPredLimit.isPredPrelimit

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccLimit.mk (since := "2026-04-19")]
/-
**Order.IsSuccPrelimit.isSuccLimit_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order
.IsSuccPrelimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α], Order.IsSuccPrelimit a → ¬Is
Min a → Order.IsSuccLimit a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSuccPrelimit.isSuccLimit_of_not_isMin (h : IsSuccPrelimit a) (ha : ¬ IsMin a) :
    IsSuccLimit a :=
  ⟨ha, h⟩

attribute [deprecated IsPredLimit.mk (since := "2026-04-19")]
IsPredPrelimit.isPredLimit_of_not_isMax

@[to_dual]
/-
**Order.isSuccPrelimit_iff_isSuccLimit_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `O
rder`。
形式化陈述：isSuccPrelimit_iff_isSuccLimit_of_not_isMin (h : ¬ IsMin a) : IsSuccPrelim
it a ↔ IsSuccLimit a
参数：h : ¬ IsMin a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSuccPrelimit_iff_isSuccLimit_of_not_isMin (h : ¬ IsMin a) :
    IsSuccPrelimit a ↔ IsSuccLimit a := by
  simp [isSuccLimit_iff, h]

@[to_dual]
/-
**Order.isSuccPrelimit_iff_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_iff_isSuccLimit [NoMinOrder α] : IsSuccPrelimit a ↔ IsSuccL
imit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimit_iff_isSuccLimit_of_not_isMin`：isSuccPrelimit_iff_is
SuccLimit_of_not_isMin (h : ¬ IsMin a) : IsSuccPrelimit a ↔ IsSuccLimit a
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
theorem isSuccPrelimit_iff_isSuccLimit [NoMinOrder α] : IsSuccPrelimit a ↔ IsSuccLimit a :=
  isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin a)

@[to_dual] alias ⟨IsSuccPrelimit.isSuccLimit, _⟩ := isSuccPrelimit_iff_isSuccLimit

@[to_dual]
/-
**Order._root_.IsMin.not_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsMin.not_isSuccLimit (h : IsMin a) : ¬ IsSuccLimit a :=
  fun ha ↦ ha.not_isMin h

@[to_dual]
/-
**Order._root_.IsMin.isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsMin.isSuccPrelimit : IsMin a → IsSuccPrelimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[to_dual]
/-
**Order.IsSuccLimit.nonempty_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α], Order.IsSuccLimit a → (Set.I
io a).Nonempty
参数：Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
-/
theorem IsSuccLimit.nonempty_Iio (h : IsSuccLimit a) : (Set.Iio a).Nonempty :=
  not_isMin_iff.1 h.1

@[to_dual]
/-
**Order.IsSuccPrelimit.noMaxOrder_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPre
limit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α], Order.IsSuccPrelimit a → NoM
axOrder ↑(Set.Iio a)
参数：Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_covBy_iff`：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c 
< b
-/
theorem IsSuccPrelimit.noMaxOrder_Iio (h : IsSuccPrelimit a) : NoMaxOrder (Set.Iio a) := by
  refine ⟨fun ⟨b, hb⟩ ↦ ?_⟩
  obtain ⟨c, hbc, hca⟩ := (not_covBy_iff hb).1 (h b)
  exact ⟨⟨c, hca⟩, hbc⟩

@[to_dual (attr := simp)]
/-
**Order.isSuccPrelimit_bot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_bot [OrderBot α] : IsSuccPrelimit (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.isSuccPrelimit`：∀ {α : Type u_1} {a : α} [inst : Preorder α], IsMi
n a → Order.IsSuccPrelimit a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem isSuccPrelimit_bot [OrderBot α] : IsSuccPrelimit (⊥ : α) :=
  isMin_bot.isSuccPrelimit

@[to_dual (attr := simp)]
/-
**Order.not_isSuccLimit_bot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLimit (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_isSuccLimit`：∀ {α : Type u_1} {a : α} [inst : Preorder α], IsM
in a → ¬Order.IsSuccLimit a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLimit (⊥ : α) :=
  isMin_bot.not_isSuccLimit

@[to_dual]
/-
**Order.IsSuccLimit.bot_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : OrderBot α], Order.
IsSuccLimit a → ⊥ < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMin_iff_bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : Order
Bot α] {a : α}, ¬IsMin a ↔ ⊥ < a
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
-/
theorem IsSuccLimit.bot_lt [OrderBot α] (h : IsSuccLimit a) : ⊥ < a :=
  not_isMin_iff_bot_lt.1 h.not_isMin

@[to_dual]
/-
**Order.IsSuccLimit.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : OrderBot α], Order.
IsSuccLimit a → a ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
-/
theorem IsSuccLimit.ne_bot [OrderBot α] (h : IsSuccLimit a) : a ≠ ⊥ :=
  h.bot_lt.ne'
/-
**Order.IsSuccLimit.pos** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero α] [IsBotZeroC
lass α], Order.IsSuccLimit a → 0 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
-/
theorem IsSuccLimit.pos [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a) : 0 < a :=
  let := IsBotZeroClass.toOrderBot α
  h.bot_lt
/-
**Order.IsSuccLimit.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero α] [IsBotZeroC
lass α], Order.IsSuccLimit a → a ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Order.IsSuccLimit.pos`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [ins
t_1 : Zero α] [IsBotZeroClass α], Order.IsSuccLimit a → 0 < a
-/
theorem IsSuccLimit.ne_zero [Zero α] [IsBotZeroClass α] (h : IsSuccLimit a) : a ≠ 0 :=
  h.pos.ne'

@[to_dual]
/-
**Order.IsSuccPrelimit.subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimi
t`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},   IsLowerSet s → ∀ {a : 
↑s}, Order.IsSuccPrelimit a → Order.IsSuccPrelimit ↑a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_covBy_iff`：not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ exists c, a < c ∧ c 
< b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsSuccPrelimit.subtypeVal {s : Set α} (hs : IsLowerSet s) {a : s}
    (ha : IsSuccPrelimit a) : IsSuccPrelimit a.1 := by
  intro b hb
  have := ha ⟨b, hs hb.le a.2⟩
  rw [not_covBy_iff] at this
  · obtain ⟨c, hc, hc'⟩ := this
    exact hb.2 hc hc'
  · exact hb.lt

@[to_dual]
/-
**Order.IsSuccLimit.subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, IsLowerSet s → ∀ {a : ↑s
}, Order.IsSuccLimit a → Order.IsSuccLimit ↑a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `Order.IsSuccPrelimit.subtypeVal`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α},   IsLowerSet s → ∀ {a : ↑s}, Order.IsSuccPrelimit a → Order.IsSuccPre
limit ↑a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.subtypeVal {s : Set α} (hs : IsLowerSet s) {a : s}
    (ha : IsSuccLimit a) : IsSuccLimit a.1 := by
  refine ⟨?_, ha.isSuccPrelimit.subtypeVal hs⟩
  have := ha.1
  rw [not_isMin_iff] at ⊢ this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

/-- Given `j < i` with `i` a successor pre-limit, `IsSuccPrelimit.mid` picks an arbitrary element
strictly between `j` and `i`. -/
@[to_dual
/-- Given `i < j` with `i` a predecessor pre-limit, `IsSuccPrelimit.mid` picks an arbitrary element
strictly between `i` and `j`. -/]
/-
**Order.IsSuccPrelimit.mid** 是 Mathlib 中的一个定义，位于命名空间 `Order.IsSuccPrelimit`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → {i j : α} → Order.IsSuccPrelimit i 
→ j < i → ↑(Set.Ioo j i)
参数：Set.Ioo j i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def IsSuccPrelimit.mid {i j : α} (hi : IsSuccPrelimit i) (hj : j < i) : Ioo j i :=
  Classical.indefiniteDescription _ ((not_covBy_iff_nonempty_Ioo hj).mp <| hi j)

@[to_dual]
/-
**Order._root_.WithTop.isSuccPrelimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WithTop.isSuccPrelimit_iff [NoMaxOrder α] {x : WithTop α} :
    IsSuccPrelimit x ↔ x = ⊤ ∨ ∃ y : α, x = y ∧ IsSuccPrelimit y := by
  cases x with
  | coe x => simp [IsSuccPrelimit, WithTop.forall]
  | top => simp [IsSuccPrelimit]

@[to_dual]
/-
**Order.IsSuccPrelimit.withTopCoe** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimi
t`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Order.IsSuccPrelimit x → Ord
er.IsSuccPrelimit ↑x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem IsSuccPrelimit.withTopCoe {x : α} (h : IsSuccPrelimit x) :
    IsSuccPrelimit (x : WithTop α) := by
  simpa [IsSuccPrelimit, WithTop.forall]

@[to_dual (attr := simp)]
/-
**Order._root_.WithTop.isSuccPrelimit_top** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WithTop.isSuccPrelimit_top [NoMaxOrder α] : IsSuccPrelimit (⊤ : WithTop α) := by
  simp [WithTop.isSuccPrelimit_iff]

@[to_dual]
/-
**Order._root_.WithTop.isSuccLimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WithTop.isSuccLimit_iff [Nonempty α] [NoMaxOrder α] {x : WithTop α} :
    IsSuccLimit x ↔ x = ⊤ ∨ ∃ y : α, x = y ∧ IsSuccLimit y := by
  cases x with
  | coe x => simp [Order.isSuccLimit_iff, WithTop.isSuccPrelimit_iff, WithTop.exists]
  | top => simp [Order.isSuccLimit_iff, WithTop.exists]

@[to_dual]
/-
**Order.IsSuccLimit.withTopCoe** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Order.IsSuccLimit x → Order.
IsSuccLimit ↑x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Order.IsSuccPrelimit.withTopCoe`：∀ {α : Type u_1} [inst : Preorder α] {x
 : α}, Order.IsSuccPrelimit x → Order.IsSuccPrelimit ↑x
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
-/
theorem IsSuccLimit.withTopCoe {x : α} (h : IsSuccLimit x) :
    IsSuccLimit (x : WithTop α) := by
  simpa [isSuccLimit_iff, WithTop.exists, h.isSuccPrelimit.withTopCoe] using h.not_isMin

@[to_dual]
/-
**Order._root_.WithTop.isSuccLimit_top** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WithTop.isSuccLimit_top [Nonempty α] [NoMaxOrder α] :
    IsSuccLimit (⊤ : WithTop α) := by
  simp [WithTop.isSuccLimit_iff]

@[to_dual]
/-
**Order._root_.WithTop.isPredPrelimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.WithTop.isPredPrelimit_iff {x : WithTop α} :
    IsPredPrelimit x ↔ x = ⊤ ∨ ∃ y : α, x = y ∧ IsPredLimit y := by
  cases x with
  | coe x => simp [IsPredPrelimit, Order.isPredLimit_iff, WithTop.forall]
  | top => simp

@[to_dual]
/-
**Order.IsPredLimit.withTopCoe** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsPredLimit`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α}, Order.IsPredLimit x → Order.
IsPredLimit ↑x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem IsPredLimit.withTopCoe {x : α} (h : IsPredLimit x) : IsPredLimit (x : WithTop α) := by
  simpa [WithTop.isPredPrelimit_iff, isPredLimit_iff, WithTop.exists] using h

variable [SuccOrder α]

@[to_dual]
/-
**Order.IsSuccPrelimit.isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : SuccOrder α], Order
.IsSuccPrelimit (Order.succ a) → IsMax a
参数：Order.succ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Order.covBy_succ_of_not_isMax`：covBy_succ_of_not_isMax (h : ¬IsMax a) : 
a ⋖ succ a
-/
protected theorem IsSuccPrelimit.isMax (h : IsSuccPrelimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

@[to_dual]
/-
**Order.IsSuccLimit.isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : SuccOrder α], Order
.IsSuccLimit (Order.succ a) → IsMax a
参数：Order.succ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a :=
  h.isSuccPrelimit.isMax

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccPrelimit.isMax (since := "2026-03-31")]
/-
**Order.not_isSuccPrelimit_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccPrelimit (
succ a)
参数：ha : ¬ IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
-/
theorem not_isSuccPrelimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccPrelimit (succ a) :=
  mt IsSuccPrelimit.isMax ha

attribute [deprecated IsPredPrelimit.isMin (since := "2026-03-31")]
not_isPredPrelimit_pred_of_not_isMin

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccLimit.isMax (since := "2026-03-31")]
/-
**Order.not_isSuccLimit_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccLimit (succ a
)
参数：ha : ¬ IsMax a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccLimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [i
nst_1 : SuccOrder α], Order.IsSuccLimit (Order.succ a) → IsMax a
-/
theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccLimit (succ a) :=
  mt IsSuccLimit.isMax ha

attribute [deprecated IsPredLimit.isMin (since := "2026-03-31")]
not_isPredLimit_pred_of_not_isMin

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/-
**Order.IsSuccPrelimit.succ_ne** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : SuccOrder α] [NoMax
Order α],   Order.IsSuccPrelimit a → ∀ (b : α), Order.succ b ≠ a
参数：b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
-/
theorem IsSuccPrelimit.succ_ne (h : IsSuccPrelimit a) (b : α) : succ b ≠ a := by
  rintro rfl
  exact not_isMax _ h.isMax

@[to_dual]
/-
**Order.IsSuccLimit.succ_ne** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : SuccOrder α] [NoMax
Order α],   Order.IsSuccLimit a → ∀ (b : α), Order.succ b ≠ a
参数：b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.succ_ne`：∀ {α : Type u_1} {a : α} [inst : Preorder 
α] [inst_1 : SuccOrder α] [NoMaxOrder α],   Order.IsSuccPrelimit a → ∀ (b : α), 
Order.succ b ≠ a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a :=
  h.isSuccPrelimit.succ_ne b

@[to_dual (attr := simp)]
/-
**Order.not_isSuccPrelimit_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_succ (a : α) : ¬IsSuccPrelimit (succ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.succ_ne`：∀ {α : Type u_1} {a : α} [inst : Preorder 
α] [inst_1 : SuccOrder α] [NoMaxOrder α],   Order.IsSuccPrelimit a → ∀ (b : α), 
Order.succ b ≠ a
-/
theorem not_isSuccPrelimit_succ (a : α) : ¬IsSuccPrelimit (succ a) := fun h => h.succ_ne _ rfl

@[to_dual (attr := simp)]
/-
**Order.not_isSuccLimit_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.succ_ne`：∀ {α : Type u_1} {a : α} [inst : Preorder α] 
[inst_1 : SuccOrder α] [NoMaxOrder α],   Order.IsSuccLimit a → ∀ (b : α), Order.
succ b ≠ a
-/
theorem not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α] [NoMaxOrder α]

@[to_dual]
/-
**Order.IsSuccPrelimit.isMin_of_noMax** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPre
limit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : SuccOrder α] [IsSuc
cArchimedean α] [NoMaxOrder α],   Order.IsSuccPrelimit a → IsMin a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.exists_succ_iterate`：LE.le.exists_succ_iterate (h : a <= b) : exis
ts n, succ^[n] a = b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Order.not_isSuccPrelimit_succ`：not_isSuccPrelimit_succ (a : α) : ¬IsSucc
Prelimit (succ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem IsSuccPrelimit.isMin_of_noMax (h : IsSuccPrelimit a) : IsMin a := by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[to_dual (attr := simp)]
/-
**Order.isSuccPrelimit_iff_of_noMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_iff_of_noMax : IsSuccPrelimit a ↔ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.isMin_of_noMax`：∀ {α : Type u_1} {a : α} [inst : Pr
eorder α] [inst_1 : SuccOrder α] [IsSuccArchimedean α] [NoMaxOrder α],   Order.I
sSuccPrelimit a → IsMin a
· 使用定理 `IsMin.isSuccPrelimit`：∀ {α : Type u_1} {a : α} [inst : Preorder α], IsMi
n a → Order.IsSuccPrelimit a
-/
theorem isSuccPrelimit_iff_of_noMax : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[to_dual (attr := simp)]
/-
**Order.not_isSuccLimit_of_noMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_of_noMax : ¬ IsSuccLimit a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `Order.IsSuccPrelimit.isMin_of_noMax`：∀ {α : Type u_1} {a : α} [inst : Pr
eorder α] [inst_1 : SuccOrder α] [IsSuccArchimedean α] [NoMaxOrder α],   Order.I
sSuccPrelimit a → IsMin a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem not_isSuccLimit_of_noMax : ¬ IsSuccLimit a :=
  fun h ↦ h.not_isMin h.isSuccPrelimit.isMin_of_noMax

@[to_dual]
/-
**Order.not_isSuccPrelimit_of_noMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_of_noMax [NoMinOrder α] : ¬ IsSuccPrelimit a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isSuccPrelimit_of_noMax [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual]
/-
**Order.isSuccLimit_iff_of_orderBot** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccLimit_iff_of_orderBot [OrderBot α] : IsSuccLimit a ↔ a != ⊥ ∧ IsSucc
Prelimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccLimit_iff`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Ord
er.IsSuccLimit a ↔ ¬IsMin a ∧ Order.IsSuccPrelimit a
· 使用定理 `isMin_iff_eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Order
Bot α] {a : α}, IsMin a ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSuccLimit_iff_of_orderBot [OrderBot α] : IsSuccLimit a ↔ a ≠ ⊥ ∧ IsSuccPrelimit a := by
  rw [isSuccLimit_iff, isMin_iff_eq_bot]

variable [SuccOrder α]

@[to_dual]
/-
**Order.isSuccPrelimit_of_succ_ne** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_of_succ_ne (h : forall b, succ b != a) : IsSuccPrelimit a
参数：h : forall b, succ b != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
-/
theorem isSuccPrelimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccPrelimit a := fun b hba =>
  h b (CovBy.succ_eq hba)

@[to_dual]
/-
**Order.not_isSuccPrelimit_iff_succ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_iff_succ_eq : ¬ IsSuccPrelimit a ↔ exists b, ¬ IsMax b 
∧ succ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.not_isSuccPrelimit_iff`：not_isSuccPrelimit_iff {a : α} : ¬IsSuccPr
elimit a ↔ exists b, b ⋖ a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
· 使用定理 `Order.covBy_succ_of_not_isMax`：covBy_succ_of_not_isMax (h : ¬IsMax a) : 
a ⋖ succ a
-/
theorem not_isSuccPrelimit_iff_succ_eq : ¬ IsSuccPrelimit a ↔ ∃ b, ¬ IsMax b ∧ succ b = a := by
  rw [not_isSuccPrelimit_iff]
  refine exists_congr fun b ↦ ⟨fun hba ↦ ⟨hba.lt.not_isMax, hba.succ_eq⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

/-- See `not_isSuccPrelimit_iff_succ_eq` for a version that states that `a` is a successor of a
value other than itself. -/
@[to_dual
/-- See `not_isPredPrelimit_iff_pred_eq` for a version that states that `a` is a predecessor of a
value other than itself. -/]
/-
**Order.mem_range_succ_of_not_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：mem_range_succ_of_not_isSuccPrelimit (h : ¬ IsSuccPrelimit a) : a in range
 (succ : α -> α)
参数：h : ¬ IsSuccPrelimit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.not_isSuccPrelimit_iff_succ_eq`：not_isSuccPrelimit_iff_succ_eq : ¬
 IsSuccPrelimit a ↔ exists b, ¬ IsMax b ∧ succ b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_range_succ_of_not_isSuccPrelimit (h : ¬ IsSuccPrelimit a) :
    a ∈ range (succ : α → α) := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff_succ_eq.1 h
  exact ⟨b, hb.2⟩

@[to_dual]
/-
**Order.mem_range_succ_or_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：mem_range_succ_or_isSuccPrelimit (a) : a in range (succ : α -> α) ∨ IsSucc
Prelimit a
参数：a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Order.mem_range_succ_of_not_isSuccPrelimit`：mem_range_succ_of_not_isSucc
Prelimit (h : ¬ IsSuccPrelimit a) : a in range (succ : α -> α)
-/
theorem mem_range_succ_or_isSuccPrelimit (a) : a ∈ range (succ : α → α) ∨ IsSuccPrelimit a :=
  or_iff_not_imp_right.2 <| mem_range_succ_of_not_isSuccPrelimit

@[to_dual]
/-
**Order.isMin_or_mem_range_succ_or_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`
。
形式化陈述：isMin_or_mem_range_succ_or_isSuccLimit (a) : IsMin a ∨ a in range (succ : 
α -> α) ∨ IsSuccLimit a
参数：a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccLimit_iff`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Ord
er.IsSuccLimit a ↔ ¬IsMin a ∧ Order.IsSuccPrelimit a
· 使用定理 `Order.mem_range_succ_or_isSuccPrelimit`：mem_range_succ_or_isSuccPrelimit
 (a) : a in range (succ : α -> α) ∨ IsSuccPrelimit a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem isMin_or_mem_range_succ_or_isSuccLimit (a) :
    IsMin a ∨ a ∈ range (succ : α → α) ∨ IsSuccLimit a := by
  rw [isSuccLimit_iff]
  have := mem_range_succ_or_isSuccPrelimit a
  tauto

@[to_dual isPredPrelimit_of_lt_pred]
/-
**Order.isSuccPrelimit_of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_of_succ_lt (H : forall a < b, succ a < b) : IsSuccPrelimit 
b
参数：H : forall a < b, succ a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a b : α}, a ⋖ b → Order.succ a = b
-/
theorem isSuccPrelimit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccPrelimit b :=
  fun a hab ↦ (H a hab.lt).ne hab.succ_eq

@[to_dual lt_pred]
/-
**Order.IsSuccPrelimit.succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimit`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : PartialOrder α] [inst_1 : SuccOrder α],
   Order.IsSuccPrelimit b → a < b → Order.succ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMax.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a : α}, IsMax a → Order.succ a = a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
-/
theorem IsSuccPrelimit.succ_lt (hb : IsSuccPrelimit b) (ha : a < b) : succ a < b := by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

@[to_dual lt_pred]
/-
**Order.IsSuccLimit.succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : PartialOrder α] [inst_1 : SuccOrder α],
   Order.IsSuccLimit b → a < b → Order.succ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → a < b → Order.succ a
 < b
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  hb.isSuccPrelimit.succ_lt ha

@[to_dual lt_pred_iff]
/-
**Order.IsSuccPrelimit.succ_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelim
it`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : PartialOrder α] [inst_1 : SuccOrder α],
   Order.IsSuccPrelimit b → (Order.succ a < b ↔ a < b)
参数：Order.succ a < b ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Order.IsSuccPrelimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → a < b → Order.succ a
 < b
-/
theorem IsSuccPrelimit.succ_lt_iff (hb : IsSuccPrelimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

@[to_dual lt_pred_iff]
/-
**Order.IsSuccLimit.succ_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : PartialOrder α] [inst_1 : SuccOrder α],
   Order.IsSuccLimit b → (Order.succ a < b ↔ a < b)
参数：Order.succ a < b ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.succ_lt_iff`：∀ {α : Type u_1} {a b : α} [inst : Par
tialOrder α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → (Order.succ a < 
b ↔ a < b)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  hb.isSuccPrelimit.succ_lt_iff

@[to_dual isPredPrelimit_iff_lt_pred]
/-
**Order.isSuccPrelimit_iff_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_iff_succ_lt : IsSuccPrelimit b ↔ forall a < b, succ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → a < b → Order.succ a
 < b
· 使用定理 `Order.isSuccPrelimit_of_succ_lt`：isSuccPrelimit_of_succ_lt (H : forall a
 < b, succ a < b) : IsSuccPrelimit b
-/
theorem isSuccPrelimit_iff_succ_lt : IsSuccPrelimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, isSuccPrelimit_of_succ_lt⟩

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/-
**Order.isSuccPrelimit_iff_succ_ne** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_iff_succ_ne : IsSuccPrelimit a ↔ forall b, succ b != a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.succ_ne`：∀ {α : Type u_1} {a : α} [inst : Preorder 
α] [inst_1 : SuccOrder α] [NoMaxOrder α],   Order.IsSuccPrelimit a → ∀ (b : α), 
Order.succ b ≠ a
· 使用定理 `Order.isSuccPrelimit_of_succ_ne`：isSuccPrelimit_of_succ_ne (h : forall b
, succ b != a) : IsSuccPrelimit a
-/
theorem isSuccPrelimit_iff_succ_ne : IsSuccPrelimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne⟩

@[to_dual]
/-
**Order.not_isSuccPrelimit_iff_mem_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_iff_mem_range_succ : ¬ IsSuccPrelimit a ↔ a in range (s
ucc : α -> α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isSuccPrelimit_iff_mem_range_succ : ¬ IsSuccPrelimit a ↔ a ∈ range (succ : α → α) := by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff, mem_range]

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit_iff' := not_isSuccPrelimit_iff_mem_range_succ

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

@[to_dual]
/-
**Order.IsSuccPrelimit.isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : SuccOrder α] [I
sSuccArchimedean α],   Order.IsSuccPrelimit a → IsMin a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsMax.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a : α}, IsMax a → Order.succ a = a
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected theorem IsSuccPrelimit.isMin (h : IsSuccPrelimit a) : IsMin a := fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[to_dual (attr := simp)]
/-
**Order.isSuccPrelimit_iff_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimit_iff_isMin : IsSuccPrelimit a ↔ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.isMin`：∀ {α : Type u_1} {a : α} [inst : PartialOrde
r α] [inst_1 : SuccOrder α] [IsSuccArchimedean α],   Order.IsSuccPrelimit a → Is
Min a
· 使用定理 `IsMin.isSuccPrelimit`：∀ {α : Type u_1} {a : α} [inst : Preorder α], IsMi
n a → Order.IsSuccPrelimit a
-/
theorem isSuccPrelimit_iff_isMin : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[deprecated (since := "2026-04-19")]
alias isSuccPrelimit_iff := isSuccPrelimit_iff_isMin
@[deprecated (since := "2026-04-19")]
alias isPredPrelimit_iff := isPredPrelimit_iff_isMax

@[to_dual (attr := simp)]
/-
**Order.not_isSuccLimit_of_isSuccArchimedean** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `Order.IsSuccPrelimit.isMin`：∀ {α : Type u_1} {a : α} [inst : PartialOrde
r α] [inst_1 : SuccOrder α] [IsSuccArchimedean α],   Order.IsSuccPrelimit a → Is
Min a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a :=
  fun h ↦ h.not_isMin <| h.isSuccPrelimit.isMin

@[deprecated (since := "2026-04-19")]
alias not_isSuccLimit := not_isSuccLimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredLimit := not_isPredLimit_of_isPredArchimedean

@[to_dual]
/-
**Order.not_isSuccPrelimit_of_isSuccArchimedean** 是 Mathlib 中的一个定理，位于命名空间 `Order
`。
形式化陈述：not_isSuccPrelimit_of_isSuccArchimedean [NoMinOrder α] : ¬ IsSuccPrelimit 
a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isSuccPrelimit_of_isSuccArchimedean [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit := not_isSuccPrelimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredPrelimit := not_isPredPrelimit_of_isPredArchimedean

end IsSuccArchimedean

end PartialOrder

section LinearOrder

variable [LinearOrder α]

@[to_dual]
/-
**Order.IsSuccPrelimit.le_iff_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccP
relimit`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LinearOrder α], Order.IsSuccPrelimit a 
→ (a ≤ b ↔ ∀ c < a, c ≤ b)
参数：a ≤ b ↔ ∀ c < a, c ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem IsSuccPrelimit.le_iff_forall_le (h : IsSuccPrelimit a) : a ≤ b ↔ ∀ c < a, c ≤ b := by
  use fun ha c hc ↦ hc.le.trans ha
  intro H
  by_contra! ha
  exact h b ⟨ha, fun c hb hc ↦ (H c hc).not_gt hb⟩

@[to_dual]
/-
**Order.IsSuccLimit.le_iff_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimi
t`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LinearOrder α], Order.IsSuccLimit a → (
a ≤ b ↔ ∀ c < a, c ≤ b)
参数：a ≤ b ↔ ∀ c < a, c ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.le_iff_forall_le`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit a → (a ≤ b ↔ ∀ c < a, c ≤ b)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.le_iff_forall_le (h : IsSuccLimit a) : a ≤ b ↔ ∀ c < a, c ≤ b :=
  h.isSuccPrelimit.le_iff_forall_le

@[to_dual]
/-
**Order.IsSuccPrelimit.lt_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccP
relimit`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LinearOrder α], Order.IsSuccPrelimit b 
→ (a < b ↔ ∃ c < b, a < c)
参数：a < b ↔ ∃ c < b, a < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.IsSuccPrelimit.le_iff_forall_le`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit a → (a ≤ b ↔ ∀ c < a, c ≤ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsSuccPrelimit.lt_iff_exists_lt (h : IsSuccPrelimit b) : a < b ↔ ∃ c < b, a < c := by
  rw [← not_iff_not]
  simp [h.le_iff_forall_le]

@[to_dual]
/-
**Order.IsSuccLimit.lt_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimi
t`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LinearOrder α], Order.IsSuccLimit b → (
a < b ↔ ∃ c < b, a < c)
参数：a < b ↔ ∃ c < b, a < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.lt_iff_exists_lt`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit b → (a < b ↔ ∃ c < b, a < c)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.lt_iff_exists_lt (h : IsSuccLimit b) : a < b ↔ ∃ c < b, a < c :=
  h.isSuccPrelimit.lt_iff_exists_lt

@[to_dual]
/-
**Order._root_.IsLUB.isSuccPrelimit_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsLUB.isSuccPrelimit_of_notMem {s : Set α} (hs : IsLUB s a) (ha : a ∉ s) :
    IsSuccPrelimit a := by
  intro b hb
  obtain ⟨c, hc, hbc, hca⟩ := hs.exists_between hb.lt
  obtain rfl := (hb.ge_of_gt hbc).antisymm hca
  contradiction

@[to_dual]
/-
**Order._root_.IsLUB.mem_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 `Order`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsLUB.mem_of_not_isSuccPrelimit {s : Set α} (hs : IsLUB s a) (ha : ¬IsSuccPrelimit a) :
    a ∈ s :=
  ha.imp_symm hs.isSuccPrelimit_of_notMem

@[to_dual]
/-
**Order._root_.IsLUB.isSuccLimit_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsLUB.isSuccLimit_of_notMem {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
    (ha : a ∉ s) : IsSuccLimit a := by
  refine ⟨?_, hs.isSuccPrelimit_of_notMem ha⟩
  obtain ⟨b, hb⟩ := hs'
  obtain rfl | hb := (hs.1 hb).eq_or_lt
  · contradiction
  · exact hb.not_isMin

@[to_dual]
/-
**Order._root_.IsLUB.mem_of_not_isSuccLimit** 是 Mathlib 中的一个引理，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsLUB.mem_of_not_isSuccLimit {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
    (ha : ¬IsSuccLimit a) : a ∈ s :=
  ha.imp_symm <| hs.isSuccLimit_of_notMem hs'

@[to_dual]
/-
**Order.IsSuccPrelimit.isLUB_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimit
`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : LinearOrder α], Order.IsSuccPrelimit a → 
IsLUB (Set.Iio a) a
参数：Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.IsSuccPrelimit.lt_iff_exists_lt`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit b → (a < b ↔ ∃ c < b, a < c)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem IsSuccPrelimit.isLUB_Iio (ha : IsSuccPrelimit a) : IsLUB (Iio a) a := by
  refine ⟨fun _ ↦ le_of_lt, fun b hb ↦ le_of_forall_lt fun c hc ↦ ?_⟩
  obtain ⟨d, hd, hd'⟩ := ha.lt_iff_exists_lt.1 hc
  exact hd'.trans_le (hb hd)

@[to_dual]
/-
**Order.IsSuccLimit.isLUB_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : LinearOrder α], Order.IsSuccLimit a → IsL
UB (Set.Iio a) a
参数：Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.isLUB_Iio`：∀ {α : Type u_1} {a : α} [inst : LinearO
rder α], Order.IsSuccPrelimit a → IsLUB (Set.Iio a) a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.isLUB_Iio (ha : IsSuccLimit a) : IsLUB (Iio a) a :=
  ha.isSuccPrelimit.isLUB_Iio

@[to_dual]
/-
**Order.isLUB_Iio_iff_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isLUB_Iio_iff_isSuccPrelimit : IsLUB (Iio a) a ↔ IsSuccPrelimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_Iic`：isLUB_Iic : IsLUB (Iic a) a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CovBy.Iio_eq`：CovBy.Iio_eq (h : a ⋖ b) : Iio b = Iic a
· 使用定理 `Order.IsSuccPrelimit.isLUB_Iio`：∀ {α : Type u_1} {a : α} [inst : LinearO
rder α], Order.IsSuccPrelimit a → IsLUB (Set.Iio a) a
-/
theorem isLUB_Iio_iff_isSuccPrelimit : IsLUB (Iio a) a ↔ IsSuccPrelimit a := by
  refine ⟨fun ha b hb ↦ ?_, IsSuccPrelimit.isLUB_Iio⟩
  rw [hb.Iio_eq] at ha
  obtain rfl := isLUB_Iic.unique ha
  cases hb.lt.false

variable [SuccOrder α]

@[to_dual pred_le_iff]
/-
**Order.IsSuccPrelimit.le_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelim
it`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LinearOrder α] [inst_1 : SuccOrder α], 
  Order.IsSuccPrelimit b → (b ≤ Order.succ a ↔ b ≤ a)
参数：b ≤ Order.succ a ↔ b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Order.IsSuccPrelimit.succ_lt_iff`：∀ {α : Type u_1} {a b : α} [inst : Par
tialOrder α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → (Order.succ a < 
b ↔ a < b)
-/
theorem IsSuccPrelimit.le_succ_iff (hb : IsSuccPrelimit b) : b ≤ succ a ↔ b ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hb.succ_lt_iff

@[to_dual pred_le_iff]
/-
**Order.IsSuccLimit.le_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LinearOrder α] [inst_1 : SuccOrder α], 
  Order.IsSuccLimit b → (b ≤ Order.succ a ↔ b ≤ a)
参数：b ≤ Order.succ a ↔ b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.le_succ_iff`：∀ {α : Type u_1} {a b : α} [inst : Lin
earOrder α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → (b ≤ Order.succ a
 ↔ b ≤ a)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.le_succ_iff (hb : IsSuccLimit b) : b ≤ succ a ↔ b ≤ a :=
  hb.isSuccPrelimit.le_succ_iff

end LinearOrder

end Order

/-! ### Induction principles -/

variable {motive : α → Sort*}

namespace Order

section isSuccPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (succ : ∀ a, ¬IsMax a → motive (succ a)) (isSuccPrelimit : ∀ a, IsSuccPrelimit a → motive a)

variable (b) in
open scoped Classical in
/-- A value can be built by building it on successors and successor pre-limits. -/
@[to_dual (attr := elab_as_elim)
/-- A value can be built by building it on predecessors and predecessor pre-limits. -/]
/-
**Order.isSuccPrelimitRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：isSuccPrelimitRecOn : motive b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def isSuccPrelimitRecOn : motive b :=
  if hb : IsSuccPrelimit b then isSuccPrelimit b hb else
    haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb)
    cast (congr_arg motive H.2) (succ _ H.1)

@[to_dual]
/-
**Order.isSuccPrelimitRecOn_of_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) : isSuccPrel
imitRecOn b succ isSuccPrelimit = isSuccPrelimit b hb
参数：hb : IsSuccPrelimit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem isSuccPrelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) :
    isSuccPrelimitRecOn b succ isSuccPrelimit = isSuccPrelimit b hb :=
  dif_pos hb

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (succ : ∀ a, ¬IsMax a → motive (succ a)) (isSuccPrelimit : ∀ a, IsSuccPrelimit a → motive a)

@[to_dual]
/-
**Order.isSuccPrelimitRecOn_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) : isSuccPrelimitRecO
n (Order.succ b) succ isSuccPrelimit = succ b hb
参数：hb : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.not_isSuccPrelimit_iff_succ_eq`：not_isSuccPrelimit_iff_succ_eq : ¬
 IsSuccPrelimit a ↔ exists b, ¬ IsMax b ∧ succ b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccPrelimitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → S
ort u_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   (succ : (a : α) → ¬IsM
ax a → motive (Order…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Order.succ_eq_succ_iff_of_not_isMax`：succ_eq_succ_iff_of_not_isMax (ha :
 ¬IsMax a) (hb : ¬IsMax b) : succ a = succ b ↔ a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isSuccPrelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b hb := by
  have hb' := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 hb')
  rw [isSuccPrelimitRecOn, dif_neg hb', cast_eq_iff_heq]
  congr!
  exact (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]
/-
**Order.isSuccPrelimitRecOn_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccPrelimitRecOn_succ [NoMaxOrder α] (b : α) : isSuccPrelimitRecOn (Ord
er.succ b) succ isSuccPrelimit = succ b (not_isMax b)
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccPrelimitRecOn_succ_of_not_isMax`：isSuccPrelimitRecOn_succ_of
_not_isMax (hb : ¬IsMax b) : isSuccPrelimitRecOn (Order.succ b) succ isSuccPreli
mit = succ b hb
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem isSuccPrelimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b (not_isMax b) :=
  isSuccPrelimitRecOn_succ_of_not_isMax ..

end LinearOrder

end isSuccPrelimitRecOn

section isSuccLimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (isMin : ∀ a, IsMin a → motive a) (succ : ∀ a, ¬IsMax a → motive (succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → motive a)

variable (b) in
open scoped Classical in
/-- A value can be built by building it on minimal elements, successors,
and successor limits. -/
@[to_dual (attr := elab_as_elim)
/-- A value can be built by building it on maximal elements, predecessors,
and predecessor limits. -/]
/-
**Order.isSuccLimitRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：isSuccLimitRecOn : motive b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def isSuccLimitRecOn : motive b :=
  isSuccPrelimitRecOn b succ fun a ha ↦
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩

@[to_dual (attr := simp)]
/-
**Order.isSuccLimitRecOn_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccLimitRecOn_of_isSuccLimit (hb : IsSuccLimit b) : isSuccLimitRecOn b 
isMin succ isSuccLimit = isSuccLimit b hb
参数：hb : IsSuccLimit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccLimitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sort
 u_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   (isMin : (a : α) → IsMin 
a → motive a) (su…
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Order.isSuccPrelimitRecOn_of_isSuccPrelimit`：isSuccPrelimitRecOn_of_isSu
ccPrelimit (hb : IsSuccPrelimit b) : isSuccPrelimitRecOn b succ isSuccPrelimit =
 isSuccPrelimit b hb
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem isSuccLimitRecOn_of_isSuccLimit (hb : IsSuccLimit b) :
    isSuccLimitRecOn b isMin succ isSuccLimit = isSuccLimit b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit,
    dif_neg hb.not_isMin]

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (isMin : ∀ a, IsMin a → motive a) (succ : ∀ a, ¬IsMax a → motive (succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → motive a)

@[to_dual]
/-
**Order.isSuccLimitRecOn_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccLimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) : isSuccLimitRecOn (Ord
er.succ b) isMin succ isSuccLimit = succ b hb
参数：hb : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccLimitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sort
 u_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   (isMin : (a : α) → IsMin 
a → motive a) (su…
· 使用定理 `Order.isSuccPrelimitRecOn_succ_of_not_isMax`：isSuccPrelimitRecOn_succ_of
_not_isMax (hb : ¬IsMax b) : isSuccPrelimitRecOn (Order.succ b) succ isSuccPreli
mit = succ b hb
-/
theorem isSuccLimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = succ b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_succ_of_not_isMax]

@[to_dual (attr := simp)]
/-
**Order.isSuccLimitRecOn_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccLimitRecOn_succ [NoMaxOrder α] (b : α) : isSuccLimitRecOn (Order.suc
c b) isMin succ isSuccLimit = succ b (not_isMax b)
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isSuccLimitRecOn_succ_of_not_isMax`：isSuccLimitRecOn_succ_of_not_i
sMax (hb : ¬IsMax b) : isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = 
succ b hb
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem isSuccLimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = succ b (not_isMax b) :=
  isSuccLimitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

@[to_dual]
/-
**Order.isSuccLimitRecOn_of_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isSuccLimitRecOn_of_isMin (hb : IsMin b) : isSuccLimitRecOn b isMin succ i
sSuccLimit = isMin b hb
参数：hb : IsMin b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isSuccLimitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sort
 u_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   (isMin : (a : α) → IsMin 
a → motive a) (su…
· 使用定理 `IsMin.isSuccPrelimit`：∀ {α : Type u_1} {a : α} [inst : Preorder α], IsMi
n a → Order.IsSuccPrelimit a
· 使用定理 `Order.isSuccPrelimitRecOn_of_isSuccPrelimit`：isSuccPrelimitRecOn_of_isSu
ccPrelimit (hb : IsSuccPrelimit b) : isSuccPrelimitRecOn b succ isSuccPrelimit =
 isSuccPrelimit b hb
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem isSuccLimitRecOn_of_isMin (hb : IsMin b) :
    isSuccLimitRecOn b isMin succ isSuccLimit = isMin b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit, dif_pos hb]

end LinearOrder

end isSuccLimitRecOn

end Order

open Order

namespace SuccOrder

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α]
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccPrelimit : ∀ a, IsSuccPrelimit a → (∀ b < a, motive b) → motive a)

variable (b) in
open scoped Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`. -/
@[to_dual (attr := elab_as_elim)
/-- Recursion principle on a well-founded partial `PredOrder`. -/]
/-
**SuccOrder.prelimitRecOn** 是 Mathlib 中的一个定义，位于命名空间 `SuccOrder`。
形式化陈述：prelimitRecOn : motive b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def prelimitRecOn : motive b :=
  wellFounded_lt.fix
    (fun a IH ↦ if h : IsSuccPrelimit a then isSuccPrelimit a h IH else
      haveI H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
      cast (congr_arg motive H.2) (succ _ H.1 <| IH _ <| H.2.subst <| lt_succ_of_not_isMax H.1))
    b

@[to_dual (attr := simp)]
/-
**SuccOrder.prelimitRecOn_of_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder
`。
形式化陈述：prelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) : prelimitRecOn b 
succ isSuccPrelimit = isSuccPrelimit b hb fun x _ => SuccOrder.prelimitRecOn x s
ucc isSuccPrelimit
参数：hb : IsSuccPrelimit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.prelimitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sor
t u_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   [inst_2 : WellFoundedLT 
α] (succ : (a : α)…
· 使用定理 `WellFounded.fix_eq`：∀ {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (
hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)   (x : α), hw
f.fix F …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem prelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) :
    prelimitRecOn b succ isSuccPrelimit =
      isSuccPrelimit b hb fun x _ ↦ SuccOrder.prelimitRecOn x succ isSuccPrelimit := by
  rw [prelimitRecOn, WellFounded.fix_eq, dif_pos hb]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α]
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccPrelimit : ∀ a, IsSuccPrelimit a → (∀ b < a, motive b) → motive a)

@[to_dual]
/-
**SuccOrder.prelimitRecOn_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder
`。
形式化陈述：prelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) : prelimitRecOn (Order.suc
c b) succ isSuccPrelimit = succ b hb (prelimitRecOn b succ isSuccPrelimit)
参数：hb : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccPrelimit.isMax`：∀ {α : Type u_1} {a : α} [inst : Preorder α]
 [inst_1 : SuccOrder α], Order.IsSuccPrelimit (Order.succ a) → IsMax a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.not_isSuccPrelimit_iff_succ_eq`：not_isSuccPrelimit_iff_succ_eq : ¬
 IsSuccPrelimit a ↔ exists b, ¬ IsMax b ∧ succ b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.prelimitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sor
t u_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   [inst_2 : WellFoundedLT 
α] (succ : (a : α)…
· 使用定理 `WellFounded.fix_eq`：∀ {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (
hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)   (x : α), hw
f.fix F …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Order.succ_eq_succ_iff_of_not_isMax`：succ_eq_succ_iff_of_not_isMax (ha :
 ¬IsMax a) (hb : ¬IsMax b) : succ a = succ b ↔ a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    prelimitRecOn (Order.succ b) succ isSuccPrelimit =
      succ b hb (prelimitRecOn b succ isSuccPrelimit) := by
  have h := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff_succ_eq.1 h)
  rw [prelimitRecOn, WellFounded.fix_eq, dif_neg h]
  have {a c : α} {ha hc} {x : ∀ a, motive a} (h : a = c) :
    cast (congr_arg (motive ∘ Order.succ) h) (succ a ha (x a)) = succ c hc (x c) := by subst h; rfl
  exact this <| (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]
/-
**SuccOrder.prelimitRecOn_succ** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：prelimitRecOn_succ [NoMaxOrder α] (b : α) : prelimitRecOn (Order.succ b) s
ucc isSuccPrelimit = succ b (not_isMax b) (prelimitRecOn b succ isSuccPrelimit)
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.prelimitRecOn_succ_of_not_isMax`：prelimitRecOn_succ_of_not_isM
ax (hb : ¬IsMax b) : prelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b h
b (prelimitRecOn b succ isSuccP…
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem prelimitRecOn_succ [NoMaxOrder α] (b : α) :
    prelimitRecOn (Order.succ b) succ isSuccPrelimit =
      succ b (not_isMax b) (prelimitRecOn b succ isSuccPrelimit) :=
  prelimitRecOn_succ_of_not_isMax _ _ _

end LinearOrder

end prelimitRecOn

section limitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α] (isMin : ∀ a, IsMin a → motive a)
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → (∀ b < a, motive b) → motive a)

variable (b) in
open scoped Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`, separating out the case of a
minimal element. -/
@[to_dual (attr := elab_as_elim)
/-- Recursion principle on a well-founded partial `PredOrder`, separating out the case of a
minimal element. -/]
/-
**SuccOrder.limitRecOn** 是 Mathlib 中的一个定义，位于命名空间 `SuccOrder`。
形式化陈述：limitRecOn : motive b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def limitRecOn : motive b :=
  prelimitRecOn b succ fun a ha IH ↦
    if h : IsMin a then isMin a h else isSuccLimit a ⟨h, ha⟩ IH

@[to_dual (attr := simp)]
/-
**SuccOrder.limitRecOn_isMin** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：limitRecOn_isMin (hb : IsMin b) : limitRecOn b isMin succ isSuccLimit = is
Min b hb
参数：hb : IsMin b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.limitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sort u
_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   [inst_2 : WellFoundedLT α] 
(isMin : (a : α…
· 使用定理 `IsMin.isSuccPrelimit`：∀ {α : Type u_1} {a : α} [inst : Preorder α], IsMi
n a → Order.IsSuccPrelimit a
· 使用定理 `SuccOrder.prelimitRecOn_of_isSuccPrelimit`：prelimitRecOn_of_isSuccPrelim
it (hb : IsSuccPrelimit b) : prelimitRecOn b succ isSuccPrelimit = isSuccPrelimi
t b hb fun x _ => SuccOrder.pre…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem limitRecOn_isMin (hb : IsMin b) : limitRecOn b isMin succ isSuccLimit = isMin b hb := by
  rw [limitRecOn, prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit, dif_pos hb]

@[to_dual (attr := simp)]
/-
**SuccOrder.limitRecOn_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：limitRecOn_of_isSuccLimit (hb : IsSuccLimit b) : limitRecOn b isMin succ i
sSuccLimit = isSuccLimit b hb fun x _ => limitRecOn x isMin succ isSuccLimit
参数：hb : IsSuccLimit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.limitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sort u
_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   [inst_2 : WellFoundedLT α] 
(isMin : (a : α…
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `SuccOrder.prelimitRecOn_of_isSuccPrelimit`：prelimitRecOn_of_isSuccPrelim
it (hb : IsSuccPrelimit b) : prelimitRecOn b succ isSuccPrelimit = isSuccPrelimi
t b hb fun x _ => SuccOrder.pre…
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem limitRecOn_of_isSuccLimit (hb : IsSuccLimit b) :
    limitRecOn b isMin succ isSuccLimit =
      isSuccLimit b hb fun x _ ↦ limitRecOn x isMin succ isSuccLimit := by
  rw [limitRecOn, prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit, dif_neg hb.not_isMin]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α] (isMin : ∀ a, IsMin a → motive a)
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → (∀ b < a, motive b) → motive a)

@[to_dual]
/-
**SuccOrder.limitRecOn_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：limitRecOn_succ_of_not_isMax (hb : ¬IsMax b) : limitRecOn (Order.succ b) i
sMin succ isSuccLimit = succ b hb (limitRecOn b isMin succ isSuccLimit)
参数：hb : ¬IsMax b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.limitRecOn.eq_1`：∀ {α : Type u_1} (b : α) {motive : α → Sort u
_2} [inst : PartialOrder α] [inst_1 : SuccOrder α]   [inst_2 : WellFoundedLT α] 
(isMin : (a : α…
· 使用定理 `SuccOrder.prelimitRecOn_succ_of_not_isMax`：prelimitRecOn_succ_of_not_isM
ax (hb : ¬IsMax b) : prelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b h
b (prelimitRecOn b succ isSuccP…
-/
theorem limitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    limitRecOn (Order.succ b) isMin succ isSuccLimit =
      succ b hb (limitRecOn b isMin succ isSuccLimit) := by
  rw [limitRecOn, prelimitRecOn_succ_of_not_isMax]; rfl

@[to_dual (attr := simp)]
/-
**SuccOrder.limitRecOn_succ** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：limitRecOn_succ [NoMaxOrder α] (b : α) : limitRecOn (Order.succ b) isMin s
ucc isSuccLimit = succ b (not_isMax b) (limitRecOn b isMin succ isSuccLimit)
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.limitRecOn_succ_of_not_isMax`：limitRecOn_succ_of_not_isMax (hb
 : ¬IsMax b) : limitRecOn (Order.succ b) isMin succ isSuccLimit = succ b hb (lim
itRecOn b isMin succ isSuccL…
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem limitRecOn_succ [NoMaxOrder α] (b : α) :
    limitRecOn (Order.succ b) isMin succ isSuccLimit =
      succ b (not_isMax b) (limitRecOn b isMin succ isSuccLimit) :=
  limitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

end LinearOrder

end limitRecOn

end SuccOrder

