/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Tactic.Trans
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Tactic.ToDual

/-!
# Orders

Defines classes for preorders and partial orders
and proves some basic lemmas about them.

We also define covering relations on a preorder.
We say that `b` *covers* `a` if `a < b` and there is no element in between.
We say that `b` *weakly covers* `a` if `a ≤ b` and there is no element between `a` and `b`.
In a partial order this is equivalent to `a ⋖ b ∨ a = b`,
in a preorder this is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/

@[expose] public section

variable {α : Type*}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/--
A preorder is a reflexive, transitive relation `≤`.
In a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by default.
You can override this definition to set a better def-eq.
-/
/-
**Preorder** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：Preorder (α : Type*) extends LE α, LT α where protected le_refl : forall a
 : α, a <= a protected le_trans : forall a b c : α, a <= b -> b <= c -> a <= c l
t
参数：α : Type*。
继承自：LE α, LT α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preorder is a reflexive, transitive relation `≤`.
In a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by de
fault.
You can override this definition to set a better def-eq.
-/
class Preorder (α : Type*) extends LE α, LT α where
  protected le_refl : ∀ a : α, a ≤ a
  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

attribute [to_dual self (reorder := le_trans (a c, 4 5), lt_iff_le_not_ge (a b))] Preorder.mk
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Std.LawfulOrderLT α where
  lt_iff := Preorder.lt_iff_le_not_ge
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Std.IsPreorder α where
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
/-
**le_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.le_refl`：∀ {α : Type u_2} [self : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The relation `≤` on a preorder is reflexive.
-/
@[refl] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
/-
**le_rfl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_rfl : a <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A version of `le_refl` where the argument is implicit
-/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
/-
**le_trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_trans : a <= b -> b <= c -> a <= c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.le_trans`：∀ {α : Type u_2} [self : Preorder α] (a b c : α), a ≤
 b → b ≤ c → a ≤ c

--- 原说明 ---
The relation `≤` on a preorder is transitive.
-/
lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

@[to_dual existing le_trans]
/-
**ge_trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ge_trans : b <= a -> c <= b -> c <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
lemma ge_trans : b ≤ a → c ≤ b → c ≤ a := flip le_trans

@[to_dual self]
/-
**lt_iff_le_not_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.lt_iff_le_not_ge`：∀ {α : Type u_2} [self : Preorder α] (a b : α
), a < b ↔ a ≤ b ∧ ¬b ≤ a
-/
lemma lt_iff_le_not_ge : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_ge _ _

@[to_dual self]
/-
**lt_of_le_not_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
参数：hab : a <= b；hba : ¬ b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
-/
lemma lt_of_le_not_ge (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_ge.2 ⟨hab, hba⟩
/-
**le_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[to_dual ge_of_eq] lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
/-
**le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
-/
@[to_dual self] lemma le_of_lt (hab : a < b) : a ≤ b := (lt_iff_le_not_ge.1 hab).1
/-
**not_le_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
-/
@[to_dual self] lemma not_le_of_gt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_not_ge.1 hab).2
/-
**not_lt_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
@[to_dual self] lemma not_lt_of_ge (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_gt hab

@[to_dual self] alias LT.lt.not_ge := not_le_of_gt
@[to_dual self] alias LE.le.not_gt := not_lt_of_ge
/-
**lt_irrefl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_irrefl (a : α) : ¬a < a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma lt_irrefl (a : α) : ¬a < a := fun h ↦ not_le_of_gt h le_rfl

@[to_dual lt_of_lt_of_le']
/-
**lt_of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
参数：hab : a < b；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']
/-
**lt_of_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
参数：hab : a <= b；hbc : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_gt hbc (le_trans hca hab)

@[to_dual gt_trans]
/-
**lt_trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_trans : a < b -> b < c -> a < c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma lt_trans : a < b → b < c → a < c := fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]
/-
**ne_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_of_lt (h : a < b) : a != b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self]
/-
**lt_asymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_asymm (h : a < b) : ¬b < a
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self] alias not_lt_of_gt := lt_asymm

@[to_dual le_of_lt_or_eq']
/-
**le_of_lt_or_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_lt_or_eq (h : a < b ∨ a = b) : a <= b
参数：h : a < b ∨ a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a ≤ b := h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']
/-
**le_of_eq_or_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_of_eq_or_lt (h : a = b ∨ a < b) : a <= b
参数：h : a = b ∨ a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma le_of_eq_or_lt (h : a = b ∨ a < b) : a ≤ b := h.elim le_of_eq le_of_lt

@[to_dual self]
/-
**lt_iff_gt_iff_le_iff_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_gt_iff_le_iff_ge : (a < b ↔ b < a) ↔ (a <= b ↔ b <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_iff_gt_iff_le_iff_ge : (a < b ↔ b < a) ↔ (a ≤ b ↔ b ≤ a) := by
  grind [= lt_iff_le_not_ge]

@[to_dual self]
/-
**lt_iff_le_iff_gt_iff_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_le_iff_gt_iff_ge : (a < b ↔ a <= b) ↔ (b < a ↔ b <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_iff_le_iff_gt_iff_ge : (a < b ↔ a ≤ b) ↔ (b < a ↔ b ≤ a) := by
  grind [= lt_iff_le_not_ge]

@[to_dual self]
/-
**lt_iff_ge_iff_gt_iff_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_ge_iff_gt_iff_le : (a < b ↔ b <= a) ↔ (b < a ↔ a <= b)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_iff_ge_iff_gt_iff_le : (a < b ↔ b ≤ a) ↔ (b < a ↔ a ≤ b) := by
  grind [= lt_iff_le_not_ge]
/-
**instTransLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransLE : @Trans α α α LE.le LE.le LE.le
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
instance instTransLE : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
/-
**instTransLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransLT : @Trans α α α LT.lt LT.lt LT.lt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
instance instTransLT : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
/-
**instTransLTLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransLTLE : @Trans α α α LT.lt LE.le LT.lt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
instance instTransLTLE : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
/-
**instTransLELT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransLELT : @Trans α α α LE.le LT.lt LT.lt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
instance instTransLELT : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
-- we have to express the following 4 instances in terms of `≥` instead of flipping the arguments
-- to `≤`, because otherwise `calc` gets confused.
@[to_dual existing instTransLE]
/-
**instTransGE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransGE : @Trans α α α GE.ge GE.ge GE.ge
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ge_trans`：ge_trans : b <= a -> c <= b -> c <= a
-/
instance instTransGE : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
@[to_dual existing instTransLT]
/-
**instTransGT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransGT : @Trans α α α GT.gt GT.gt GT.gt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `gt_trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → c < 
b → c < a
-/
instance instTransGT : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
@[to_dual existing instTransLTLE]
/-
**instTransGTGE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransGTGE : @Trans α α α GT.gt GE.ge GT.gt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_lt_of_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
-/
instance instTransGTGE : @Trans α α α GT.gt GE.ge GT.gt := ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]
/-
**instTransGEGT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTransGEGT : @Trans α α α GE.ge GT.gt GT.gt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_le_of_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
-/
instance instTransGEGT : @Trans α α α GE.ge GT.gt GT.gt := ⟨lt_of_le_of_lt'⟩

/-- `<` is decidable if `≤` is. -/
@[instance_reducible]
/-
**decidableLTOfDecidableLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：decidableLTOfDecidableLE [DecidableLE α] : DecidableLT α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`<` is decidable if `≤` is.
-/
def decidableLTOfDecidableLE [DecidableLE α] : DecidableLT α :=
  fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

/-- `WCovBy a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between. This is denoted `a ⩿ b`.
-/
@[to_dual self (reorder := 3 4)]
/-
**WCovBy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WCovBy (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WCovBy a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between. This is denoted `a ⩿
 b`.
-/
def WCovBy (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b

to_dual_insert_cast WCovBy := by grind

@[inherit_doc]
infixl:50 " ⩿ " => WCovBy

/-- `CovBy a b` means that `b` covers `a`. This means that `a < b` and there is no element in
between. This is denoted `a ⋖ b`. -/
@[to_dual self (reorder := 3 4)]
/-
**CovBy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CovBy {α : Type*} [LT α] (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CovBy a b` means that `b` covers `a`. This means that `a < b` and there is no e
lement in
between. This is denoted `a ⋖ b`.
-/
def CovBy {α : Type*} [LT α] (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b

to_dual_insert_cast CovBy := by grind

@[inherit_doc]
infixl:50 " ⋖ " => CovBy

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
/-
**PartialOrder** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：PartialOrder (α : Type*) extends Preorder α where protected le_antisymm : 
forall a b : α, a <= b -> b <= a -> a = b  attribute [to_dual self (reorder
参数：α : Type*。
继承自：Preorder α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial order is a reflexive, transitive, antisymmetric relation `≤`.
-/
class PartialOrder (α : Type*) extends Preorder α where
  protected le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

attribute [to_dual self (reorder := le_antisymm (3 4))] PartialOrder.mk
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] : Std.IsPartialOrder α where
  le_antisymm := PartialOrder.le_antisymm

variable [PartialOrder α] {a b : α}
/-
**le_antisymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_antisymm : a <= b -> b <= a -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialOrder.le_antisymm`：∀ {α : Type u_2} [self : PartialOrder α] (a b 
: α), a ≤ b → b ≤ a → a = b
-/
lemma le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm _ _

@[to_dual existing le_antisymm]
/-
**ge_antisymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ge_antisymm : b <= a -> a <= b -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma ge_antisymm : b ≤ a → a ≤ b → a = b := flip le_antisymm

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[to_dual ge_antisymm_iff]
/-
**le_antisymm_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']
/-
**lt_of_le_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_le_of_ne : a <= b -> a != b -> a < b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma lt_of_le_of_ne : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_ge h₁ <| mt (le_antisymm h₁) h₂

@[to_dual lt_of_ne_of_le']
/-
**lt_of_ne_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_of_ne_of_le : a != b -> a <= b -> a < b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
lemma lt_of_ne_of_le : a ≠ b → a ≤ b → a < b := flip lt_of_le_of_ne

/-- Equality is decidable if `≤` is. -/
/-
**decidableEqOfDecidableLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [inst : PartialOrder α] → [DecidableLE α] → DecidableEq α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
Equality is decidable if `≤` is.
-/
def decidableEqOfDecidableLE [DecidableLE α] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

-- See Note [decidable namespace]
@[to_dual Decidable.lt_or_eq_of_le']
/-
**Decidable.lt_or_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α} [DecidableLE α], a ≤ b 
→ a < b ∨ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
-/
protected lemma Decidable.lt_or_eq_of_le [DecidableLE α] (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_ge hab hba)

@[to_dual Decidable.le_iff_lt_or_eq']
/-
**Decidable.le_iff_lt_or_eq** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α} [DecidableLE α], a ≤ b 
↔ a < b ∨ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.lt_or_eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b 
: α} [DecidableLE α], a ≤ b → a < b ∨ a = b
· 使用引理 `le_of_lt_or_eq`：le_of_lt_or_eq (h : a < b ∨ a = b) : a <= b
-/
protected lemma Decidable.le_iff_lt_or_eq [DecidableLE α] : a ≤ b ↔ a < b ∨ a = b :=
  ⟨Decidable.lt_or_eq_of_le, le_of_lt_or_eq⟩

@[to_dual lt_or_eq_of_le']
/-
**lt_or_eq_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.lt_or_eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b 
: α} [DecidableLE α], a ≤ b → a < b ∨ a = b
-/
lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eq']
/-
**le_iff_lt_or_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.le_iff_lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b
 : α} [DecidableLE α], a ≤ b ↔ a < b ∨ a = b
-/
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := open scoped Classical in Decidable.le_iff_lt_or_eq

end PartialOrder

