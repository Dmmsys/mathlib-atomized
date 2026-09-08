/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lex
public import Mathlib.Order.WithBot

/-!
# Orders on a sum type

This file defines the disjoint sum and the linear (aka lexicographic) sum of two orders and
provides relation instances for `Sum.LiftRel` and `Sum.Lex`.

We declare the disjoint sum of orders as the default set of instances. The linear order goes on a
type synonym.

## Main declarations

* `Sum.LE`, `Sum.LT`: Disjoint sum of orders.
* `Sum.Lex.LE`, `Sum.Lex.LT`: Lexicographic/linear sum of orders.

## Notation

* `α ⊕ₗ β`:  The linear sum of `α` and `β`.
-/

@[expose] public section


variable {α β γ : Type*}

namespace Sum

/-! ### Unbundled relation classes -/


section LiftRel

variable (r : α → α → Prop) (s : β → β → Prop)

@[refl]
/-
**Sum.LiftRel.refl** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) [Std
.Refl r] [Std.Refl s] (x : α ⊕ β),   Sum.LiftRel r s x x
参数：r : α → α → Prop；s : β → β → Prop；x : α ⊕ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem LiftRel.refl [Std.Refl r] [Std.Refl s] : ∀ x, LiftRel r s x x
  | inl a => LiftRel.inl (_root_.refl a)
  | inr a => LiftRel.inr (_root_.refl a)
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] [Std.Refl s] : Std.Refl (LiftRel r s) :=
  ⟨LiftRel.refl _ _⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] [Std.Irrefl s] : Std.Irrefl (LiftRel r s) :=
  ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

@[trans]
/-
**Sum.LiftRel.trans** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) [IsT
rans α r] [IsTrans β s] {a b c : α ⊕ β},   Sum.LiftRel r s a b → Sum.LiftRel r s
 b c → Sum.LiftRel r s a c
参数：r : α → α → Prop；s : β → β → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem LiftRel.trans [IsTrans α r] [IsTrans β s] :
    ∀ {a b c}, LiftRel r s a b → LiftRel r s b c → LiftRel r s a c
  | _, _, _, LiftRel.inl hab, LiftRel.inl hbc => LiftRel.inl <| _root_.trans hab hbc
  | _, _, _, LiftRel.inr hab, LiftRel.inr hbc => LiftRel.inr <| _root_.trans hab hbc
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans α r] [IsTrans β s] : IsTrans (α ⊕ β) (LiftRel r s) :=
  ⟨fun _ _ _ => LiftRel.trans _ _⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Antisymm r] [Std.Antisymm s] : Std.Antisymm (LiftRel r s) :=
  ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

end LiftRel

section Lex

variable (r : α → α → Prop) (s : β → β → Prop)

/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] [Std.Refl s] : Std.Refl (Lex r s) :=
  ⟨by
    rintro (a | a)
    exacts [Lex.inl (refl _), Lex.inr (refl _)]⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] [Std.Irrefl s] : Std.Irrefl (Lex r s) :=
  ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans α r] [IsTrans β s] : IsTrans (α ⊕ β) (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hbc⟩ | ⟨hbc⟩)
    exacts [.inl (_root_.trans hab hbc), .sep _ _, .inr (_root_.trans hab hbc), .sep _ _]⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Antisymm r] [Std.Antisymm s] : Std.Antisymm (Lex r s) :=
  ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Total r] [Std.Total s] : Std.Total (Lex r s) :=
  ⟨fun a b =>
    match a, b with
    | inl a, inl b => (total_of r a b).imp Lex.inl Lex.inl
    | inl _, inr _ => Or.inl (Lex.sep _ _)
    | inr _, inl _ => Or.inr (Lex.sep _ _)
    | inr a, inr b => (total_of s a b).imp Lex.inr Lex.inr⟩
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Trichotomous r] [Std.Trichotomous s] : Std.Trichotomous (Lex r s) := by
  grind [Std.Trichotomous, Lex]
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWellOrder α r] [IsWellOrder β s] :
    IsWellOrder (α ⊕ β) (Sum.Lex r s) where wf := Sum.lex_wf IsWellFounded.wf IsWellFounded.wf

end Lex

/-! ### Disjoint sum of two orders -/


section Disjoint

/-
**Sum.instLESum** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：instLESum [LE α] [LE β] : LE (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLESum [LE α] [LE β] : LE (α ⊕ β) :=
  ⟨LiftRel (· ≤ ·) (· ≤ ·)⟩
/-
**Sum.instLTSum** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：instLTSum [LT α] [LT β] : LT (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLTSum [LT α] [LT β] : LT (α ⊕ β) :=
  ⟨LiftRel (· < ·) (· < ·)⟩
/-
**Sum.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：le_def [LE α] [LE β] {a b : α oplus β} : a <= b ↔ LiftRel (· <= ·) (· <= ·
) a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def [LE α] [LE β] {a b : α ⊕ β} : a ≤ b ↔ LiftRel (· ≤ ·) (· ≤ ·) a b :=
  Iff.rfl
/-
**Sum.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：lt_def [LT α] [LT β] {a b : α oplus β} : a < b ↔ LiftRel (· < ·) (· < ·) a
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def [LT α] [LT β] {a b : α ⊕ β} : a < b ↔ LiftRel (· < ·) (· < ·) a b :=
  Iff.rfl

@[simp]
/-
**Sum.inl_le_inl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inl_le_inl_iff [LE α] [LE β] {a b : α} : (inl a : α oplus β) <= inl b ↔ a 
<= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.liftRel_inl_inl`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Prop} 
{β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {a : α} {c : γ},   Sum.LiftRel 
r s (Sum.…
-/
theorem inl_le_inl_iff [LE α] [LE β] {a b : α} : (inl a : α ⊕ β) ≤ inl b ↔ a ≤ b :=
  liftRel_inl_inl

@[simp]
/-
**Sum.inr_le_inr_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inr_le_inr_iff [LE α] [LE β] {a b : β} : (inr a : α oplus β) <= inr b ↔ a 
<= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.liftRel_inr_inr`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Prop} 
{β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {b : β} {d : δ},   Sum.LiftRel 
r s (Sum.…
-/
theorem inr_le_inr_iff [LE α] [LE β] {a b : β} : (inr a : α ⊕ β) ≤ inr b ↔ a ≤ b :=
  liftRel_inr_inr

@[simp]
/-
**Sum.inl_lt_inl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α oplus β) < inl b ↔ a <
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.liftRel_inl_inl`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Prop} 
{β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {a : α} {c : γ},   Sum.LiftRel 
r s (Sum.…
-/
theorem inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α ⊕ β) < inl b ↔ a < b :=
  liftRel_inl_inl

@[simp]
/-
**Sum.inr_lt_inr_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α oplus β) < inr b ↔ a <
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.liftRel_inr_inr`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Prop} 
{β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {b : β} {d : δ},   Sum.LiftRel 
r s (Sum.…
-/
theorem inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α ⊕ β) < inr b ↔ a < b :=
  liftRel_inr_inr

@[simp]
/-
**Sum.not_inl_le_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：not_inl_le_inr [LE α] [LE β] {a : α} {b : β} : ¬inl b <= inr a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.not_liftRel_inl_inr`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Pr
op} {β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {a : α} {d : δ},   ¬Sum.Lif
tRel r s (Sum…
-/
theorem not_inl_le_inr [LE α] [LE β] {a : α} {b : β} : ¬inl b ≤ inr a :=
  not_liftRel_inl_inr

@[simp]
/-
**Sum.not_inl_lt_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl b < inr a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.not_liftRel_inl_inr`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Pr
op} {β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {a : α} {d : δ},   ¬Sum.Lif
tRel r s (Sum…
-/
theorem not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl b < inr a :=
  not_liftRel_inl_inr

@[simp]
/-
**Sum.not_inr_le_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬inr b <= inl a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.not_liftRel_inr_inl`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Pr
op} {β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {b : β} {c : γ},   ¬Sum.Lif
tRel r s (Sum…
-/
theorem not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬inr b ≤ inl a :=
  not_liftRel_inr_inl

@[simp]
/-
**Sum.not_inr_lt_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr b < inl a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.not_liftRel_inr_inl`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Pr
op} {β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {b : β} {c : γ},   ¬Sum.Lif
tRel r s (Sum…
-/
theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr b < inl a :=
  not_liftRel_inr_inl

section Preorder

variable [Preorder α] [Preorder β]

/-
**Sum.instPreorderSum** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：instPreorderSum : Preorder (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorderSum : Preorder (α ⊕ β) :=
  { instLESum, instLTSum with
    le_refl := fun _ => LiftRel.refl _ _ _,
    le_trans := fun _ _ _ => LiftRel.trans _ _,
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
      · rintro ⟨⟨hab⟩ | ⟨hab⟩, hba⟩
        · exact LiftRel.inl (hab.lt_of_not_ge fun h => hba <| LiftRel.inl h)
        · exact LiftRel.inr (hab.lt_of_not_ge fun h => hba <| LiftRel.inr h) }
/-
**Sum.inl_mono** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inl_mono : Monotone (inl : α -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_mono : Monotone (inl : α → α ⊕ β) := fun _ _ => LiftRel.inl
/-
**Sum.inr_mono** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inr_mono : Monotone (inr : β -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_mono : Monotone (inr : β → α ⊕ β) := fun _ _ => LiftRel.inr
/-
**Sum.inl_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inl_strictMono : StrictMono (inl : α -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_strictMono : StrictMono (inl : α → α ⊕ β) := fun _ _ => LiftRel.inl
/-
**Sum.inr_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inr_strictMono : StrictMono (inr : β -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_strictMono : StrictMono (inr : β → α ⊕ β) := fun _ _ => LiftRel.inr

end Preorder

/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] [PartialOrder β] : PartialOrder (α ⊕ β) :=
  { instPreorderSum with
    le_antisymm := fun _ _ => show LiftRel _ _ _ _ → _ from antisymm }
/-
**Sum.noMinOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α opl
us β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α 
oplus β) < inl b ↔ a < b
· 使用定理 `Sum.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α 
oplus β) < inr b ↔ a < b
-/
instance noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α ⊕ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩
/-
**Sum.noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α opl
us β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α 
oplus β) < inl b ↔ a < b
· 使用定理 `Sum.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α 
oplus β) < inr b ↔ a < b
-/
instance noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α ⊕ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

@[simp]
/-
**Sum.noMinOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：noMinOrder_iff [LT α] [LT β] : NoMinOrder (α oplus β) ↔ NoMinOrder α ∧ NoM
inOrder β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sum.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α 
oplus β) < inl b ↔ a < b
· 使用定理 `Sum.not_inr_lt_inl`：not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr 
b < inl a
· 使用定理 `Sum.not_inl_lt_inr`：not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl 
b < inr a
· 使用定理 `Sum.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α 
oplus β) < inr b ↔ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem noMinOrder_iff [LT α] [LT β] : NoMinOrder (α ⊕ β) ↔ NoMinOrder α ∧ NoMinOrder β :=
  ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inl a : α ⊕ β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inr_lt_inl h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inr a : α ⊕ β)
        · exact (not_inl_lt_inr h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMinOrder _ _ _ _ h.1 h.2⟩

@[simp]
/-
**Sum.noMaxOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：noMaxOrder_iff [LT α] [LT β] : NoMaxOrder (α oplus β) ↔ NoMaxOrder α ∧ NoM
axOrder β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sum.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α 
oplus β) < inl b ↔ a < b
· 使用定理 `Sum.not_inl_lt_inr`：not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl 
b < inr a
· 使用定理 `Sum.not_inr_lt_inl`：not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr 
b < inl a
· 使用定理 `Sum.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α 
oplus β) < inr b ↔ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem noMaxOrder_iff [LT α] [LT β] : NoMaxOrder (α ⊕ β) ↔ NoMaxOrder α ∧ NoMaxOrder β :=
  ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inl a : α ⊕ β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inl_lt_inr h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inr a : α ⊕ β)
        · exact (not_inr_lt_inl h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMaxOrder _ _ _ _ h.1 h.2⟩
/-
**Sum.denselyOrdered** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：denselyOrdered [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β] : Dense
lyOrdered (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
-/
instance denselyOrdered [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α ⊕ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, LiftRel.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), LiftRel.inl ha, LiftRel.inl hb⟩
    | inr _, inr _, LiftRel.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), LiftRel.inr ha, LiftRel.inr hb⟩⟩

@[simp]
/-
**Sum.denselyOrdered_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：denselyOrdered_iff [LT α] [LT β] : DenselyOrdered (α oplus β) ↔ DenselyOrd
ered α ∧ DenselyOrdered β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α 
oplus β) < inl b ↔ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sum.not_inl_lt_inr`：not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl 
b < inr a
· 使用定理 `Sum.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α 
oplus β) < inr b ↔ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem denselyOrdered_iff [LT α] [LT β] :
    DenselyOrdered (α ⊕ β) ↔ DenselyOrdered α ∧ DenselyOrdered β :=
  ⟨fun _ =>
    ⟨⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α ⊕ β) _ _ _ _ (inl_lt_inl_iff.2 h)
        · exact ⟨c, inl_lt_inl_iff.1 ha, inl_lt_inl_iff.1 hb⟩
        · exact (not_inl_lt_inr ha).elim⟩,
      ⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α ⊕ β) _ _ _ _ (inr_lt_inr_iff.2 h)
        · exact (not_inl_lt_inr hb).elim
        · exact ⟨c, inr_lt_inr_iff.1 ha, inr_lt_inr_iff.1 hb⟩⟩⟩,
    fun h => @Sum.denselyOrdered _ _ _ _ h.1 h.2⟩

@[simp]
/-
**Sum.swap_le_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：swap_le_swap_iff [LE α] [LE β] {a b : α oplus β} : a.swap <= b.swap ↔ a <=
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.liftRel_swap_iff`：∀ {β : Type u_1} {β_1 : Type u_2} {s : β → β_1 → P
rop} {α : Type u_3} {α_1 : Type u_4} {r : α → α_1 → Prop} {x : α ⊕ β}   {y : α_1
 ⊕ β_1}, S…
-/
theorem swap_le_swap_iff [LE α] [LE β] {a b : α ⊕ β} : a.swap ≤ b.swap ↔ a ≤ b :=
  liftRel_swap_iff

@[simp]
/-
**Sum.swap_lt_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：swap_lt_swap_iff [LT α] [LT β] {a b : α oplus β} : a.swap < b.swap ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.liftRel_swap_iff`：∀ {β : Type u_1} {β_1 : Type u_2} {s : β → β_1 → P
rop} {α : Type u_3} {α_1 : Type u_4} {r : α → α_1 → Prop} {x : α ⊕ β}   {y : α_1
 ⊕ β_1}, S…
-/
theorem swap_lt_swap_iff [LT α] [LT β] {a b : α ⊕ β} : a.swap < b.swap ↔ a < b :=
  liftRel_swap_iff

end Disjoint

/-! ### Linear sum of two orders -/


namespace Lex


/-- The linear sum of two orders -/
notation3:30 α " ⊕ₗ " β:29 => _root_.Lex (α ⊕ β)

--TODO: Can we make `inlₗ`, `inrₗ` `local notation`?
/-- Lexicographical `Sum.inl`. Only used for pattern matching. -/
@[match_pattern]
/-
**Sum.Lex._root_.Sum.inl** 是 Mathlib 中的一个缩写定义，位于命名空间 `Sum.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lexicographical `Sum.inl`. Only used for pattern matching.
-/
abbrev _root_.Sum.inlₗ (x : α) : α ⊕ₗ β :=
  toLex (Sum.inl x)

/-- Lexicographical `Sum.inr`. Only used for pattern matching. -/
@[match_pattern]
/-
**Sum.Lex._root_.Sum.inr** 是 Mathlib 中的一个缩写定义，位于命名空间 `Sum.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lexicographical `Sum.inr`. Only used for pattern matching.
-/
abbrev _root_.Sum.inrₗ (x : β) : α ⊕ₗ β :=
  toLex (Sum.inr x)

/-- The linear/lexicographical `≤` on a sum. -/
/-
**Sum.Lex.LE** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [LE α] → [LE β] → LE (α ⊕ₗ β)
参数：α ⊕ₗ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear/lexicographical `≤` on a sum.
-/
protected instance LE [LE α] [LE β] : LE (α ⊕ₗ β) :=
  ⟨Lex (· ≤ ·) (· ≤ ·)⟩

/-- The linear/lexicographical `<` on a sum. -/
/-
**Sum.Lex.LT** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [LT α] → [LT β] → LT (α ⊕ₗ β)
参数：α ⊕ₗ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear/lexicographical `<` on a sum.
-/
protected instance LT [LT α] [LT β] : LT (α ⊕ₗ β) :=
  ⟨Lex (· < ·) (· < ·)⟩

@[simp]
/-
**Sum.Lex.toLex_le_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLex_le_toLex [LE α] [LE β] {a b : α oplus β} : toLex a <= toLex b ↔ Lex 
(· <= ·) (· <= ·) a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toLex_le_toLex [LE α] [LE β] {a b : α ⊕ β} :
    toLex a ≤ toLex b ↔ Lex (· ≤ ·) (· ≤ ·) a b :=
  Iff.rfl

@[simp]
/-
**Sum.Lex.toLex_lt_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLex_lt_toLex [LT α] [LT β] {a b : α oplus β} : toLex a < toLex b ↔ Lex (
· < ·) (· < ·) a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toLex_lt_toLex [LT α] [LT β] {a b : α ⊕ β} :
    toLex a < toLex b ↔ Lex (· < ·) (· < ·) a b :=
  Iff.rfl
/-
**Sum.Lex.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：le_def [LE α] [LE β] {a b : α oplusₗ β} : a <= b ↔ Lex (· <= ·) (· <= ·) (
ofLex a) (ofLex b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def [LE α] [LE β] {a b : α ⊕ₗ β} : a ≤ b ↔ Lex (· ≤ ·) (· ≤ ·) (ofLex a) (ofLex b) :=
  Iff.rfl
/-
**Sum.Lex.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：lt_def [LT α] [LT β] {a b : α oplusₗ β} : a < b ↔ Lex (· < ·) (· < ·) (ofL
ex a) (ofLex b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def [LT α] [LT β] {a b : α ⊕ₗ β} : a < b ↔ Lex (· < ·) (· < ·) (ofLex a) (ofLex b) :=
  Iff.rfl
/-
**Sum.Lex.inl_le_inl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_le_inl_iff [LE α] [LE β] {a b : α} : toLex (inl a : α oplus β) <= toLe
x (inl b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.lex_inl_inl`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {a₁ a₂ : α},   Sum.Lex r s (Sum.inl a₁) (Sum.inl a₂) ↔ r a₁ a₂
-/
theorem inl_le_inl_iff [LE α] [LE β] {a b : α} : toLex (inl a : α ⊕ β) ≤ toLex (inl b) ↔ a ≤ b :=
  lex_inl_inl
/-
**Sum.Lex.inr_le_inr_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inr_le_inr_iff [LE α] [LE β] {a b : β} : toLex (inr a : α oplus β) <= toLe
x (inr b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.lex_inr_inr`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {b₁ b₂ : β},   Sum.Lex r s (Sum.inr b₁) (Sum.inr b₂) ↔ s b₁ b₂
-/
theorem inr_le_inr_iff [LE α] [LE β] {a b : β} : toLex (inr a : α ⊕ β) ≤ toLex (inr b) ↔ a ≤ b :=
  lex_inr_inr
/-
**Sum.Lex.inl_lt_inl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (inl a : α oplus β) < toLex
 (inl b) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.lex_inl_inl`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {a₁ a₂ : α},   Sum.Lex r s (Sum.inl a₁) (Sum.inl a₂) ↔ r a₁ a₂
-/
theorem inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (inl a : α ⊕ β) < toLex (inl b) ↔ a < b :=
  lex_inl_inl
/-
**Sum.Lex.inr_lt_inr_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (inr a : α oplusₗ β) < toLe
x (inr b) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.lex_inr_inr`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {b₁ b₂ : β},   Sum.Lex r s (Sum.inr b₁) (Sum.inr b₂) ↔ s b₁ b₂
-/
theorem inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (inr a : α ⊕ₗ β) < toLex (inr b) ↔ a < b :=
  lex_inr_inr
/-
**Sum.Lex.inl_le_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_le_inr [LE α] [LE β] (a : α) (b : β) : toLex (inl a) <= toLex (inr b)
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_le_inr [LE α] [LE β] (a : α) (b : β) : toLex (inl a) ≤ toLex (inr b) :=
  Lex.sep _ _
/-
**Sum.Lex.inl_lt_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (inl a) < toLex (inr b)
参数：a : α；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (inl a) < toLex (inr b) :=
  Lex.sep _ _
/-
**Sum.Lex.not_inr_le_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬toLex (inr b) <= toLex (in
l a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.lex_inr_inl`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {b : β} {a : α},   ¬Sum.Lex r s (Sum.inr b) (Sum.inl a)
-/
theorem not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬toLex (inr b) ≤ toLex (inl a) :=
  lex_inr_inl
/-
**Sum.Lex.not_inr_lt_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬toLex (inr b) < toLex (inl
 a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.lex_inr_inl`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {b : β} {a : α},   ¬Sum.Lex r s (Sum.inr b) (Sum.inl a)
-/
theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬toLex (inr b) < toLex (inl a) :=
  lex_inr_inl

/-- `toLex` promoted to a `RelIso` between `<` relations. -/
/-
**Sum.Lex.toLexRelIsoLT** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：toLexRelIsoLT [LT α] [LT β] : Sum.Lex (· < · : α -> α -> Prop) (· < · : β 
-> β -> Prop) ≃r (· < · : α oplusₗ β -> _ -> _) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toLex` promoted to a `RelIso` between `<` relations.
-/
def toLexRelIsoLT [LT α] [LT β] :
    Sum.Lex (· < · : α → α → Prop) (· < · : β → β → Prop) ≃r (· < · : α ⊕ₗ β → _ → _) where
  toFun := toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
/-
**Sum.Lex.toLexRelIsoLT_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLexRelIsoLT_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLexRelIsoLT_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α := α) (β := β)) = toLex :=
  rfl

@[simp]
/-
**Sum.Lex.toLexRelIsoLT_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLexRelIsoLT_symm_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLexRelIsoLT_symm_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α := α) (β := β)).symm = ofLex :=
  rfl

/-- `toLex` promoted to a `RelIso` between `≤` relations. -/
/-
**Sum.Lex.toLexRelIsoLE** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：toLexRelIsoLE [LE α] [LE β] : Sum.Lex (· <= · : α -> α -> Prop) (· <= · : 
β -> β -> Prop) ≃r (· <= · : α oplusₗ β -> _ -> _) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toLex` promoted to a `RelIso` between `≤` relations.
-/
def toLexRelIsoLE [LE α] [LE β] :
    Sum.Lex (· ≤ · : α → α → Prop) (· ≤ · : β → β → Prop) ≃r (· ≤ · : α ⊕ₗ β → _ → _) where
  toFun := toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
/-
**Sum.Lex.toLexRelIsoLE_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLexRelIsoLE_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLexRelIsoLE_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α := α) (β := β)) = toLex :=
  rfl

@[simp]
/-
**Sum.Lex.toLexRelIsoLE_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLexRelIsoLE_symm_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLexRelIsoLE_symm_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α := α) (β := β)).symm = ofLex :=
  rfl

section Preorder

variable [Preorder α] [Preorder β]

/-
**Sum.Lex.preorder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：preorder : Preorder (α oplusₗ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preorder : Preorder (α ⊕ₗ β) :=
  { Lex.LE, Lex.LT with
    le_refl := refl_of (Lex (· ≤ ·) (· ≤ ·)),
    le_trans := fun _ _ _ => trans_of (Lex (· ≤ ·) (· ≤ ·)),
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩ | ⟨b, a⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
        · exact not_inr_lt_inl hab
      · rintro ⟨⟨hab⟩ | ⟨hab⟩ | ⟨a, b⟩, hba⟩
        · exact Lex.inl (hab.lt_of_not_ge fun h => hba <| Lex.inl h)
        · exact Lex.inr (hab.lt_of_not_ge fun h => hba <| Lex.inr h)
        · exact Lex.sep _ _ }
/-
**Sum.Lex.toLex_mono** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLex_mono : Monotone (@toLex (α oplus β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.LiftRel.lex`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s :
 β → β → Prop} {a b : α ⊕ β},   Sum.LiftRel r s a b → Sum.Lex r s a b
-/
theorem toLex_mono : Monotone (@toLex (α ⊕ β)) := fun _ _ h => h.lex
/-
**Sum.Lex.toLex_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：toLex_strictMono : StrictMono (@toLex (α oplus β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.LiftRel.lex`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s :
 β → β → Prop} {a b : α ⊕ β},   Sum.LiftRel r s a b → Sum.Lex r s a b
-/
theorem toLex_strictMono : StrictMono (@toLex (α ⊕ β)) := fun _ _ h => h.lex
/-
**Sum.Lex.inl_mono** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_mono : Monotone (toLex ∘ inl : α -> α oplusₗ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Sum.Lex.toLex_mono`：toLex_mono : Monotone (@toLex (α oplus β))
· 使用定理 `Sum.inl_mono`：inl_mono : Monotone (inl : α -> α oplus β)
-/
theorem inl_mono : Monotone (toLex ∘ inl : α → α ⊕ₗ β) :=
  toLex_mono.comp Sum.inl_mono
/-
**Sum.Lex.inr_mono** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inr_mono : Monotone (toLex ∘ inr : β -> α oplusₗ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Sum.Lex.toLex_mono`：toLex_mono : Monotone (@toLex (α oplus β))
· 使用定理 `Sum.inr_mono`：inr_mono : Monotone (inr : β -> α oplus β)
-/
theorem inr_mono : Monotone (toLex ∘ inr : β → α ⊕ₗ β) :=
  toLex_mono.comp Sum.inr_mono
/-
**Sum.Lex.inl_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_strictMono : StrictMono (toLex ∘ inl : α -> α oplusₗ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Sum.Lex.toLex_strictMono`：toLex_strictMono : StrictMono (@toLex (α oplus
 β))
· 使用定理 `Sum.inl_strictMono`：inl_strictMono : StrictMono (inl : α -> α oplus β)
-/
theorem inl_strictMono : StrictMono (toLex ∘ inl : α → α ⊕ₗ β) :=
  toLex_strictMono.comp Sum.inl_strictMono
/-
**Sum.Lex.inr_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inr_strictMono : StrictMono (toLex ∘ inr : β -> α oplusₗ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Sum.Lex.toLex_strictMono`：toLex_strictMono : StrictMono (@toLex (α oplus
 β))
· 使用定理 `Sum.inr_strictMono`：inr_strictMono : StrictMono (inr : β -> α oplus β)
-/
theorem inr_strictMono : StrictMono (toLex ∘ inr : β → α ⊕ₗ β) :=
  toLex_strictMono.comp Sum.inr_strictMono

end Preorder

/-
**Sum.Lex.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：partialOrder [PartialOrder α] [PartialOrder β] : PartialOrder (α oplusₗ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder [PartialOrder α] [PartialOrder β] : PartialOrder (α ⊕ₗ β) :=
  { Lex.preorder with le_antisymm := fun _ _ => antisymm_of (Lex (· ≤ ·) (· ≤ ·)) }
/-
**Sum.Lex.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：linearOrder [LinearOrder α] [LinearOrder β] : LinearOrder (α oplusₗ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder [LinearOrder α] [LinearOrder β] : LinearOrder (α ⊕ₗ β) :=
  { Lex.partialOrder with
    le_total := total_of (Lex (· ≤ ·) (· ≤ ·)),
    toDecidableLE := instDecidableRelSumLex,
    toDecidableLT := instDecidableRelSumLex,
    toDecidableEq := instDecidableEqSum }

/-- The lexicographical bottom of a sum is the bottom of the left component. -/
/-
**Sum.Lex.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：orderBot [LE α] [OrderBot α] [LE β] : OrderBot (α oplusₗ β) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical bottom of a sum is the bottom of the left component.
-/
instance orderBot [LE α] [OrderBot α] [LE β] :
    OrderBot (α ⊕ₗ β) where
  bot := inl ⊥
  bot_le := by
    rintro (a | b)
    · exact Lex.inl bot_le
    · exact Lex.sep _ _

@[simp]
/-
**Sum.Lex.inl_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inl_bot [LE α] [OrderBot α] [LE β] : toLex (inl ⊥ : α oplus β) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_bot [LE α] [OrderBot α] [LE β] : toLex (inl ⊥ : α ⊕ β) = ⊥ :=
  rfl

/-- The lexicographical top of a sum is the top of the right component. -/
/-
**Sum.Lex.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：orderTop [LE α] [LE β] [OrderTop β] : OrderTop (α oplusₗ β) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical top of a sum is the top of the right component.
-/
instance orderTop [LE α] [LE β] [OrderTop β] :
    OrderTop (α ⊕ₗ β) where
  top := inr ⊤
  le_top := by
    rintro (a | b)
    · exact Lex.sep _ _
    · exact Lex.inr le_top

@[simp]
/-
**Sum.Lex.inr_top** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：inr_top [LE α] [LE β] [OrderTop β] : toLex (inr ⊤ : α oplus β) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_top [LE α] [LE β] [OrderTop β] : toLex (inr ⊤ : α ⊕ β) = ⊤ :=
  rfl
/-
**Sum.Lex.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：boundedOrder [LE α] [LE β] [OrderBot α] [OrderTop β] : BoundedOrder (α opl
usₗ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance boundedOrder [LE α] [LE β] [OrderBot α] [OrderTop β] : BoundedOrder (α ⊕ₗ β) :=
  { Lex.orderBot, Lex.orderTop with }
/-
**Sum.Lex.noMinOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α opl
usₗ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.Lex.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (
inl a : α oplus β) < toLex (inl b) ↔ a < b
· 使用定理 `Sum.Lex.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (
inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
-/
instance noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩
/-
**Sum.Lex.noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α opl
usₗ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.Lex.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (
inl a : α oplus β) < toLex (inl b) ↔ a < b
· 使用定理 `Sum.Lex.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (
inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
-/
instance noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩
/-
**Sum.Lex.noMinOrder_of_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：noMinOrder_of_nonempty [LT α] [LT β] [NoMinOrder α] [Nonempty α] : NoMinOr
der (α oplusₗ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.Lex.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (
inl a : α oplus β) < toLex (inl b) ↔ a < b
· 使用定理 `Sum.Lex.inl_lt_inr`：inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (in
l a) < toLex (inr b)
-/
instance noMinOrder_of_nonempty [LT α] [LT β] [NoMinOrder α] [Nonempty α] : NoMinOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr _ => ⟨toLex (inl <| Classical.arbitrary α), inl_lt_inr _ _⟩⟩
/-
**Sum.Lex.noMaxOrder_of_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：noMaxOrder_of_nonempty [LT α] [LT β] [NoMaxOrder β] [Nonempty β] : NoMaxOr
der (α oplusₗ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.Lex.inl_lt_inr`：inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (in
l a) < toLex (inr b)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.Lex.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (
inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
-/
instance noMaxOrder_of_nonempty [LT α] [LT β] [NoMaxOrder β] [Nonempty β] : NoMaxOrder (α ⊕ₗ β) :=
  ⟨fun a =>
    match a with
    | inl _ => ⟨toLex (inr <| Classical.arbitrary β), inl_lt_inr _ _⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩
/-
**Sum.Lex.denselyOrdered_of_noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：denselyOrdered_of_noMaxOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrde
red β] [NoMaxOrder α] : DenselyOrdered (α oplusₗ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.Lex.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (
inl a : α oplus β) < toLex (inl b) ↔ a < b
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Sum.Lex.inl_lt_inr`：inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (in
l a) < toLex (inr b)
· 使用定理 `Sum.Lex.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (
inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
-/
instance denselyOrdered_of_noMaxOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMaxOrder α] : DenselyOrdered (α ⊕ₗ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl a, inr _, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_gt a
      ⟨toLex (inl c), inl_lt_inl_iff.2 h, inl_lt_inr _ _⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩
/-
**Sum.Lex.denselyOrdered_of_noMinOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：denselyOrdered_of_noMinOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrde
red β] [NoMinOrder β] : DenselyOrdered (α oplusₗ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.Lex.inl_lt_inl_iff`：inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (
inl a : α oplus β) < toLex (inl b) ↔ a < b
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Sum.Lex.inl_lt_inr`：inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (in
l a) < toLex (inr b)
· 使用定理 `Sum.Lex.inr_lt_inr_iff`：inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (
inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
-/
instance denselyOrdered_of_noMinOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMinOrder β] : DenselyOrdered (α ⊕ₗ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl _, inr b, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_lt b
      ⟨toLex (inr c), inl_lt_inr _ _, inr_lt_inr_iff.2 h⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

end Lex

end Sum

/-! ### Order isomorphisms -/


open OrderDual Sum

namespace OrderIso

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*} [LE α] [LE β] [LE γ]
  [LE α₁] [LE α₂] [LE β₁] [LE β₂] [LE γ₁] [LE γ₂] (a : α) (b : β) (c : γ)

/-- `Equiv.sumCongr` promoted to an order isomorphism. -/
@[simps! apply]
/-
**OrderIso.sumCongr** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ oplus β₁ ≃o α₂ oplus β₂ wher
e toEquiv
参数：ea : α₁ ≃o α₂；eb : β₁ ≃o β₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumCongr` promoted to an order isomorphism.
-/
def sumCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ ⊕ β₁ ≃o α₂ ⊕ β₂ where
  toEquiv := .sumCongr ea eb
  map_rel_iff' := by aesop

@[simp]
/-
**OrderIso.sumCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o
 γ₂) : (e₁.sumCongr e₂).trans (f₁.sumCongr f₂) = (e₁.trans f₁).sumCongr (e₂.tran
s f₂)
参数：e₁ : α₁ ≃o β₁；e₂ : α₂ ≃o β₂；f₁ : β₁ ≃o γ₁；f₂ : β₂ ≃o γ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.sumCongr_apply`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {β₁ : Type u_
6} {β₂ : Type u_7} [inst : LE α₁] [inst_1 : LE α₂] [inst_2 : LE β₁]   [inst_3 : 
LE β₂] (ea : …
· 使用定理 `Sum.map_map`：∀ {α' : Type u_1} {α'' : Type u_2} {β' : Type u_3} {β'' : T
ype u_4} {α : Type u_5} {β : Type u_6} (f' : α' → α'')   (g' : β' → β'') (f : α 
→…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂) :
    (e₁.sumCongr e₂).trans (f₁.sumCongr f₂) = (e₁.trans f₁).sumCongr (e₂.trans f₂) := by
  ext; simp

@[simp]
/-
**OrderIso.sumCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : (ea.sumCongr eb).symm = ea
.symm.sumCongr eb.symm
参数：ea : α₁ ≃o α₂；eb : β₁ ≃o β₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) :
    (ea.sumCongr eb).symm = ea.symm.sumCongr eb.symm :=
  rfl

@[simp]
/-
**OrderIso.sumCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumCongr_refl : sumCongr (.refl α) (.refl β) = .refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.sumCongr_apply`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {β₁ : Type u_
6} {β₂ : Type u_7} [inst : LE α₁] [inst_1 : LE α₂] [inst_2 : LE β₁]   [inst_3 : 
LE β₂] (ea : …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Sum.map_id_id`：∀ {α : Type u_1} {β : Type u_2}, Sum.map id id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumCongr_refl : sumCongr (.refl α) (.refl β) = .refl _ := by
  ext; simp

/-- `Equiv.sumComm` promoted to an order isomorphism. -/
@[simps! apply]
/-
**OrderIso.sumComm** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumComm (α β : Type*) [LE α] [LE β] : α oplus β ≃o β oplus α
参数：α β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.swap_le_swap_iff`：swap_le_swap_iff [LE α] [LE β] {a b : α oplus β} :
 a.swap <= b.swap ↔ a <= b

--- 原说明 ---
`Equiv.sumComm` promoted to an order isomorphism.
-/
def sumComm (α β : Type*) [LE α] [LE β] : α ⊕ β ≃o β ⊕ α :=
  { Equiv.sumComm α β with map_rel_iff' := swap_le_swap_iff }

@[simp]
/-
**OrderIso.sumComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumComm_symm (α β : Type*) [LE α] [LE β] : (OrderIso.sumComm α β).symm = O
rderIso.sumComm β α
参数：α β : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumComm_symm (α β : Type*) [LE α] [LE β] :
    (OrderIso.sumComm α β).symm = OrderIso.sumComm β α :=
  rfl

/-- `Equiv.sumAssoc` promoted to an order isomorphism. -/
/-
**OrderIso.sumAssoc** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α oplus β) oplus γ ≃o α o
plus (β oplus γ)
参数：α β γ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumAssoc` promoted to an order isomorphism.
-/
def sumAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α ⊕ β) ⊕ γ ≃o α ⊕ (β ⊕ γ) :=
  { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} => by
      rcases a with ((_ | _) | _) <;> rcases b with ((_ | _) | _) <;>
      simp [Equiv.sumAssoc] }

@[simp]
/-
**OrderIso.sumAssoc_apply_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc_apply_inl_inl : sumAssoc α β γ (inl (inl a)) = inl a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_apply_inl_inl : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
/-
**OrderIso.sumAssoc_apply_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc_apply_inl_inr : sumAssoc α β γ (inl (inr b)) = inr (inl b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_apply_inl_inr : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
/-
**OrderIso.sumAssoc_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc_apply_inr : sumAssoc α β γ (inr c) = inr (inr c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_apply_inr : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl

@[simp]
/-
**OrderIso.sumAssoc_symm_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc_symm_apply_inl : (sumAssoc α β γ).symm (inl a) = inl (inl a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_symm_apply_inl : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
/-
**OrderIso.sumAssoc_symm_apply_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc_symm_apply_inr_inl : (sumAssoc α β γ).symm (inr (inl b)) = inl (i
nr b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_symm_apply_inr_inl : (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
/-
**OrderIso.sumAssoc_symm_apply_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumAssoc_symm_apply_inr_inr : (sumAssoc α β γ).symm (inr (inr c)) = inr c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumAssoc_symm_apply_inr_inr : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- `orderDual` is distributive over `⊕` up to an order isomorphism. -/
/-
**OrderIso.sumDualDistrib** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumDualDistrib (α β : Type*) [LE α] [LE β] : (α oplus β)ᵒᵈ ≃o αᵒᵈ oplus βᵒ
ᵈ
参数：α β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`orderDual` is distributive over `⊕` up to an order isomorphism.
-/
def sumDualDistrib (α β : Type*) [LE α] [LE β] : (α ⊕ β)ᵒᵈ ≃o αᵒᵈ ⊕ βᵒᵈ :=
  { Equiv.refl _ with
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · change inl (toDual a) ≤ inl (toDual b) ↔ toDual (inl a) ≤ toDual (inl b)
        simp [toDual_le_toDual, inl_le_inl_iff]
      · exact iff_of_false (@not_inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _) not_inr_le_inl
      · exact iff_of_false (@not_inr_le_inl (OrderDual α) (OrderDual β) _ _ _ _) not_inl_le_inr
      · change inr (toDual a) ≤ inr (toDual b) ↔ toDual (inr a) ≤ toDual (inr b)
        simp [toDual_le_toDual, inr_le_inr_iff] }

@[simp]
/-
**OrderIso.sumDualDistrib_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumDualDistrib_inl : sumDualDistrib α β (toDual (inl a)) = inl (toDual a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumDualDistrib_inl : sumDualDistrib α β (toDual (inl a)) = inl (toDual a) :=
  rfl

@[simp]
/-
**OrderIso.sumDualDistrib_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumDualDistrib_inr : sumDualDistrib α β (toDual (inr b)) = inr (toDual b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumDualDistrib_inr : sumDualDistrib α β (toDual (inr b)) = inr (toDual b) :=
  rfl

@[simp]
/-
**OrderIso.sumDualDistrib_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumDualDistrib_symm_inl : (sumDualDistrib α β).symm (inl (toDual a)) = toD
ual (inl a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumDualDistrib_symm_inl : (sumDualDistrib α β).symm (inl (toDual a)) = toDual (inl a) :=
  rfl

@[simp]
/-
**OrderIso.sumDualDistrib_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumDualDistrib_symm_inr : (sumDualDistrib α β).symm (inr (toDual b)) = toD
ual (inr b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumDualDistrib_symm_inr : (sumDualDistrib α β).symm (inr (toDual b)) = toDual (inr b) :=
  rfl

/-- `Equiv.sumCongr` promoted to an order isomorphism between lexicographic sums. -/
@[simps! apply]
/-
**OrderIso.sumLexCongr** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumLexCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ oplusₗ β₁ ≃o α₂ oplusₗ β₂
 where toEquiv
参数：ea : α₁ ≃o α₂；eb : β₁ ≃o β₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`Equiv.sumCongr` promoted to an order isomorphism between lexicographic sums.
-/
def sumLexCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ ⊕ₗ β₁ ≃o α₂ ⊕ₗ β₂ where
  toEquiv := ofLex.trans ((Equiv.sumCongr ea eb).trans toLex)
  map_rel_iff' := by simp_rw [Lex.forall]; rintro (a | a) (b | b) <;> simp

@[simp]
/-
**OrderIso.sumLexCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂
 ≃o γ₂) : (e₁.sumLexCongr e₂).trans (f₁.sumLexCongr f₂) = (e₁.trans f₁).sumLexCo
ngr (e₂.trans f₂)
参数：e₁ : α₁ ≃o β₁；e₂ : α₂ ≃o β₂；f₁ : β₁ ≃o γ₁；f₂ : β₂ ≃o γ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.sumLexCongr_apply`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {β₁ : Type
 u_6} {β₂ : Type u_7} [inst : LE α₁] [inst_1 : LE α₂] [inst_2 : LE β₁]   [inst_3
 : LE β₂] (ea : …
· 使用定理 `Sum.map_map`：∀ {α' : Type u_1} {α'' : Type u_2} {β' : Type u_3} {β'' : T
ype u_4} {α : Type u_5} {β : Type u_6} (f' : α' → α'')   (g' : β' → β'') (f : α 
→…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumLexCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂) :
    (e₁.sumLexCongr e₂).trans (f₁.sumLexCongr f₂) = (e₁.trans f₁).sumLexCongr (e₂.trans f₂) := by
  ext; simp

@[simp]
/-
**OrderIso.sumLexCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : (ea.sumLexCongr eb).sym
m = ea.symm.sumLexCongr eb.symm
参数：ea : α₁ ≃o α₂；eb : β₁ ≃o β₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) :
    (ea.sumLexCongr eb).symm = ea.symm.sumLexCongr eb.symm :=
  rfl

@[simp]
/-
**OrderIso.sumLexCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexCongr_refl : sumLexCongr (.refl α) (.refl β) = .refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.sumLexCongr_apply`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {β₁ : Type
 u_6} {β₂ : Type u_7} [inst : LE α₁] [inst_1 : LE α₂] [inst_2 : LE β₁]   [inst_3
 : LE β₂] (ea : …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Sum.map_id_id`：∀ {α : Type u_1} {β : Type u_2}, Sum.map id id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumLexCongr_refl : sumLexCongr (.refl α) (.refl β) = .refl _ := by
  ext; simp

/-- `Equiv.sumAssoc` promoted to an order isomorphism. -/
/-
**OrderIso.sumLexAssoc** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α oplusₗ β) oplusₗ γ ≃
o α oplusₗ β oplusₗ γ
参数：α β γ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumAssoc` promoted to an order isomorphism.
-/
def sumLexAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α ⊕ₗ β) ⊕ₗ γ ≃o α ⊕ₗ β ⊕ₗ γ :=
  { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} =>
      ⟨fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl h => Lex.inl <| Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.sep _ _ => Lex.inl <| Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
        | inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inr (Lex.inl h) => Lex.inl <| Lex.inr h
        | inlₗ (inrₗ _), inrₗ _, Lex.inr (Lex.sep _ _) => Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr (Lex.inr h) => Lex.inr h,
        fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl (Lex.inl h) => Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.inl (Lex.sep _ _) => Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
        | inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inl (Lex.inr h) => Lex.inr <| Lex.inl h
        | inlₗ (inrₗ _), inrₗ _, Lex.sep _ _ => Lex.inr <| Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr h => Lex.inr <| Lex.inr h⟩ }

@[simp]
/-
**OrderIso.sumLexAssoc_apply_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc_apply_inl_inl : sumLexAssoc α β γ (toLex <| inl <| toLex <| in
l a) = toLex (inl a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexAssoc_apply_inl_inl :
    sumLexAssoc α β γ (toLex <| inl <| toLex <| inl a) = toLex (inl a) :=
  rfl

@[simp]
/-
**OrderIso.sumLexAssoc_apply_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc_apply_inl_inr : sumLexAssoc α β γ (toLex <| inl <| toLex <| in
r b) = toLex (inr <| toLex <| inl b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexAssoc_apply_inl_inr :
    sumLexAssoc α β γ (toLex <| inl <| toLex <| inr b) = toLex (inr <| toLex <| inl b) :=
  rfl

@[simp]
/-
**OrderIso.sumLexAssoc_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc_apply_inr : sumLexAssoc α β γ (toLex <| inr c) = toLex (inr <|
 toLex <| inr c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexAssoc_apply_inr :
    sumLexAssoc α β γ (toLex <| inr c) = toLex (inr <| toLex <| inr c) :=
  rfl

@[simp]
/-
**OrderIso.sumLexAssoc_symm_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc_symm_apply_inl : (sumLexAssoc α β γ).symm (inl a) = inl (inl a
)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexAssoc_symm_apply_inl : (sumLexAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
/-
**OrderIso.sumLexAssoc_symm_apply_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc_symm_apply_inr_inl : (sumLexAssoc α β γ).symm (inr (inl b)) = 
inl (inr b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexAssoc_symm_apply_inr_inl : (sumLexAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
/-
**OrderIso.sumLexAssoc_symm_apply_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexAssoc_symm_apply_inr_inr : (sumLexAssoc α β γ).symm (inr (inr c)) = 
inr c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexAssoc_symm_apply_inr_inr : (sumLexAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/-- `OrderDual` is antidistributive over `⊕ₗ` up to an order isomorphism. -/
/-
**OrderIso.sumLexDualAntidistrib** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumLexDualAntidistrib (α β : Type*) [LE α] [LE β] : (α oplusₗ β)ᵒᵈ ≃o βᵒᵈ 
oplusₗ αᵒᵈ
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` is antidistributive over `⊕ₗ` up to an order isomorphism.
-/
def sumLexDualAntidistrib (α β : Type*) [LE α] [LE β] : (α ⊕ₗ β)ᵒᵈ ≃o βᵒᵈ ⊕ₗ αᵒᵈ :=
  { Equiv.sumComm α β with
    map_rel_iff' := fun {a b} => by
      rcases a with (a | a) <;> rcases b with (b | b)
      · change
          toLex (inr <| toDual a) ≤ toLex (inr <| toDual b) ↔
            toDual (toLex <| inl a) ≤ toDual (toLex <| inl b)
        simp [toDual_le_toDual]
      · exact iff_of_false (@Lex.not_inr_le_inl (OrderDual β) (OrderDual α) _ _ _ _)
          Lex.not_inr_le_inl
      · exact iff_of_true (@Lex.inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _)
          (Lex.inl_le_inr _ _)
      · change
          toLex (inl <| toDual a) ≤ toLex (inl <| toDual b) ↔
            toDual (toLex <| inr a) ≤ toDual (toLex <| inr b)
        simp [toDual_le_toDual] }

@[simp]
/-
**OrderIso.sumLexDualAntidistrib_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexDualAntidistrib_inl : sumLexDualAntidistrib α β (toDual (inl a)) = i
nr (toDual a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexDualAntidistrib_inl :
    sumLexDualAntidistrib α β (toDual (inl a)) = inr (toDual a) :=
  rfl

@[simp]
/-
**OrderIso.sumLexDualAntidistrib_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexDualAntidistrib_inr : sumLexDualAntidistrib α β (toDual (inr b)) = i
nl (toDual b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexDualAntidistrib_inr :
    sumLexDualAntidistrib α β (toDual (inr b)) = inl (toDual b) :=
  rfl

@[simp]
/-
**OrderIso.sumLexDualAntidistrib_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexDualAntidistrib_symm_inl : (sumLexDualAntidistrib α β).symm (inl (to
Dual b)) = toDual (inr b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexDualAntidistrib_symm_inl :
    (sumLexDualAntidistrib α β).symm (inl (toDual b)) = toDual (inr b) :=
  rfl

@[simp]
/-
**OrderIso.sumLexDualAntidistrib_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexDualAntidistrib_symm_inr : (sumLexDualAntidistrib α β).symm (inr (to
Dual a)) = toDual (inl a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexDualAntidistrib_symm_inr :
    (sumLexDualAntidistrib α β).symm (inr (toDual a)) = toDual (inl a) :=
  rfl

/-- `Equiv.sumEmpty` as an `OrderIso` with the lexicographic sum. -/
/-
**OrderIso.sumLexEmpty** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumLexEmpty [IsEmpty β] : Lex (α oplus β) ≃o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumEmpty` as an `OrderIso` with the lexicographic sum.
-/
def sumLexEmpty [IsEmpty β] : Lex (α ⊕ β) ≃o α :=
  RelIso.sumLexEmpty ..

/-- `Equiv.emptySum` as an `OrderIso` with the lexicographic sum. -/
/-
**OrderIso.emptySumLex** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：emptySumLex [IsEmpty β] : Lex (β oplus α) ≃o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.emptySum` as an `OrderIso` with the lexicographic sum.
-/
def emptySumLex [IsEmpty β] : Lex (β ⊕ α) ≃o α :=
  RelIso.emptySumLex ..

@[simp]
/-
**OrderIso.sumLexEmpty_apply_inl** 是 Mathlib 中的一个引理，位于命名空间 `OrderIso`。
形式化陈述：sumLexEmpty_apply_inl [IsEmpty β] (x : α) : sumLexEmpty (β
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumLexEmpty_apply_inl [IsEmpty β] (x : α) : sumLexEmpty (β := β) (toLex <| .inl x) = x :=
  rfl

@[simp]
/-
**OrderIso.emptySumLex_apply_inr** 是 Mathlib 中的一个引理，位于命名空间 `OrderIso`。
形式化陈述：emptySumLex_apply_inr [IsEmpty β] (x : α) : emptySumLex (β
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma emptySumLex_apply_inr [IsEmpty β] (x : α) : emptySumLex (β := β) (toLex <| .inr x) = x :=
  rfl

end OrderIso

variable [LE α]

namespace WithBot

set_option backward.isDefEq.respectTransparency false in
/-- `WithBot α` is order-isomorphic to `PUnit ⊕ₗ α`, by sending `⊥` to `Unit` and `↑a` to
`a`. -/
/-
**WithBot.orderIsoPUnitSumLex** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：orderIsoPUnitSumLex : WithBot α ≃o PUnit oplusₗ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`WithBot α` is order-isomorphic to `PUnit ⊕ₗ α`, by sending `⊥` to `Unit` and `↑
a` to
`a`.
-/
def orderIsoPUnitSumLex : WithBot α ≃o PUnit ⊕ₗ α :=
  ⟨(Equiv.optionEquivSumPUnit α).trans <| (Equiv.sumComm _ _).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Equiv.sumComm_apply, swap, Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [elim_inr, lex_inl_inl, bot_le]
    · simp only [elim_inr, elim_inl, Lex.sep, bot_le]
    · simp only [elim_inl, elim_inr, lex_inr_inl, false_iff]
      exact not_coe_le_bot _
    · simp only [elim_inl, lex_inr_inr, coe_le_coe]
  ⟩

@[simp]
/-
**WithBot.orderIsoPUnitSumLex_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：orderIsoPUnitSumLex_bot : @orderIsoPUnitSumLex α _ ⊥ = toLex (inl PUnit.un
it)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoPUnitSumLex_bot : @orderIsoPUnitSumLex α _ ⊥ = toLex (inl PUnit.unit) :=
  rfl

@[simp]
/-
**WithBot.orderIsoPUnitSumLex_toLex** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：orderIsoPUnitSumLex_toLex (a : α) : orderIsoPUnitSumLex ↑a = toLex (inr a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoPUnitSumLex_toLex (a : α) : orderIsoPUnitSumLex ↑a = toLex (inr a) :=
  rfl

@[simp]
/-
**WithBot.orderIsoPUnitSumLex_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：orderIsoPUnitSumLex_symm_inl (x : PUnit) : (@orderIsoPUnitSumLex α _).symm
 (toLex <| inl x) = ⊥
参数：x : PUnit。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoPUnitSumLex_symm_inl (x : PUnit) :
    (@orderIsoPUnitSumLex α _).symm (toLex <| inl x) = ⊥ :=
  rfl

@[simp]
/-
**WithBot.orderIsoPUnitSumLex_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：orderIsoPUnitSumLex_symm_inr (a : α) : orderIsoPUnitSumLex.symm (toLex <| 
inr a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoPUnitSumLex_symm_inr (a : α) : orderIsoPUnitSumLex.symm (toLex <| inr a) = a :=
  rfl

end WithBot

namespace WithTop

set_option backward.isDefEq.respectTransparency false in
/-- `WithTop α` is order-isomorphic to `α ⊕ₗ PUnit`, by sending `⊤` to `Unit` and `↑a` to
`a`. -/
/-
**WithTop.orderIsoSumLexPUnit** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：orderIsoSumLexPUnit : WithTop α ≃o α oplusₗ PUnit
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`WithTop α` is order-isomorphic to `α ⊕ₗ PUnit`, by sending `⊤` to `Unit` and `↑
a` to
`a`.
-/
def orderIsoSumLexPUnit : WithTop α ≃o α ⊕ₗ PUnit :=
  ⟨(Equiv.optionEquivSumPUnit α).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [lex_inr_inr, le_top]
    · simp only [lex_inr_inl, false_iff]
      exact not_top_le_coe _
    · simp only [Lex.sep, le_top]
    · simp only [lex_inl_inl, coe_le_coe]⟩

@[simp]
/-
**WithTop.orderIsoSumLexPUnit_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：orderIsoSumLexPUnit_top : @orderIsoSumLexPUnit α _ ⊤ = toLex (inr PUnit.un
it)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoSumLexPUnit_top : @orderIsoSumLexPUnit α _ ⊤ = toLex (inr PUnit.unit) :=
  rfl

@[simp]
/-
**WithTop.orderIsoSumLexPUnit_toLex** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：orderIsoSumLexPUnit_toLex (a : α) : orderIsoSumLexPUnit ↑a = toLex (inl a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoSumLexPUnit_toLex (a : α) : orderIsoSumLexPUnit ↑a = toLex (inl a) :=
  rfl

@[simp]
/-
**WithTop.orderIsoSumLexPUnit_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：orderIsoSumLexPUnit_symm_inr (x : PUnit) : (@orderIsoSumLexPUnit α _).symm
 (toLex <| inr x) = ⊤
参数：x : PUnit。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoSumLexPUnit_symm_inr (x : PUnit) :
    (@orderIsoSumLexPUnit α _).symm (toLex <| inr x) = ⊤ :=
  rfl

@[simp]
/-
**WithTop.orderIsoSumLexPUnit_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：orderIsoSumLexPUnit_symm_inl (a : α) : orderIsoSumLexPUnit.symm (toLex <| 
inl a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoSumLexPUnit_symm_inl (a : α) : orderIsoSumLexPUnit.symm (toLex <| inl a) = a :=
  rfl

end WithTop

