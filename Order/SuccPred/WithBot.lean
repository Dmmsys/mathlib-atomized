/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Order.SuccPred.Basic

/-!
# Successor function on `WithBot`

This file defines the successor of `a : WithBot α` as an element of `α`, and dually for `WithTop`.
-/

@[expose] public section

namespace WithBot
variable {α : Type*} [Preorder α] [OrderBot α] [SuccOrder α] {x y : WithBot α}

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: (a : WithBot α)
  body: a.recBotCoe ⊥ Order.succ

中文:
定义 succ
  签名: (a : WithBot α)
  定义体: a.recBotCoe ⊥ Order.succ

Depends on / 依赖: Order.succ, a.recBotCoe, recBotCoe
-/
def succ (a : WithBot α) : α := a.recBotCoe ⊥ Order.succ

/--
lemma `succ_bot` / 引理 `succ_bot`

English:
lemma succ_bot
  statement: succ (⊥ : WithBot α) = ⊥
  proof: rfl

中文:
引理 succ_bot
  结论: succ (⊥ : WithBot α) = ⊥
  证明: rfl
-/
@[simp] lemma succ_bot : succ (⊥ : WithBot α) = ⊥ := rfl

/--
lemma `succ_coe` / 引理 `succ_coe`

English:
lemma succ_coe
  given: (a : α)
  statement: succ (a : WithBot α) = Order.succ a
  proof: rfl

中文:
引理 succ_coe
  条件: (a : α)
  结论: succ (a : WithBot α) = Order.succ a
  证明: rfl
-/
@[simp] lemma succ_coe (a : α) : succ (a : WithBot α) = Order.succ a := rfl

/--
lemma `succ_eq_succ` / 引理 `succ_eq_succ`

English:
lemma succ_eq_succ
  statement: forall a : WithBot α, succ a = Order.succ a

中文:
引理 succ_eq_succ
  结论: 对任意 a : WithBot α, succ a = Order.succ a
-/
lemma succ_eq_succ : forall a : WithBot α, succ a = Order.succ a
  | ⊥ => rfl
  | (a : α) => rfl

/--
lemma `lt_succ` / 引理 `lt_succ`

English:
lemma lt_succ
  given: [NoMaxOrder α] (x : WithBot α)
  statement: x < x.succ
  proof: succ_eq_succ x ▸ Order.lt_succ x

中文:
引理 lt_succ
  条件: [NoMax序 α] (x : WithBot α)
  结论: x < x.succ
  证明: succ_eq_succ x ▸ Order.lt_succ x

Depends on / 依赖: Order.lt_succ, lt_succ, succ_eq_succ
-/
lemma lt_succ [NoMaxOrder α] (x : WithBot α) : x < x.succ :=
  succ_eq_succ x ▸ Order.lt_succ x

/--
lemma `succ_mono` / 引理 `succ_mono`

English:
lemma succ_mono
  statement: Monotone (succ : WithBot α -> α)

中文:
引理 succ_mono
  结论: 递增 (succ : WithBot α -> α)
-/
lemma succ_mono : Monotone (succ : WithBot α -> α)
  | ⊥, _, _ => by simp
  | (a : α), ⊥, hab => by simp at hab
  | (a : α), (b : α), hab => Order.succ_le_succ (by simpa using hab)

/--
lemma `succ_strictMono` / 引理 `succ_strictMono`

English:
lemma succ_strictMono
  given: [NoMaxOrder α]
  statement: StrictMono (succ : WithBot α -> α)

中文:
引理 succ_strictMono
  条件: [NoMax序 α]
  结论: 严格递增 (succ : WithBot α -> α)
-/
lemma succ_strictMono [NoMaxOrder α] : StrictMono (succ : WithBot α -> α)
  | ⊥, (b : α), hab => by simp
  | (a : α), (b : α), hab => Order.succ_lt_succ (by simpa using hab)

/--
lemma `succ_le_succ` / 引理 `succ_le_succ`

English:
lemma succ_le_succ
  given: (hxy : x <= y)
  statement: x.succ <= y.succ
  proof: succ_mono hxy

中文:
引理 succ_le_succ
  条件: (hxy : x <= y)
  结论: x.succ <= y.succ
  证明: succ_mono hxy
-/
@[gcongr] lemma succ_le_succ (hxy : x <= y) : x.succ <= y.succ := succ_mono hxy
/--
lemma `succ_lt_succ` / 引理 `succ_lt_succ`

English:
lemma succ_lt_succ
  given: [NoMaxOrder α] (hxy : x < y)
  statement: x.succ < y.succ
  proof: succ_strictMono hxy

中文:
引理 succ_lt_succ
  条件: [NoMax序 α] (hxy : x < y)
  结论: x.succ < y.succ
  证明: succ_strictMono hxy
-/
@[gcongr] lemma succ_lt_succ [NoMaxOrder α] (hxy : x < y) : x.succ < y.succ := succ_strictMono hxy

section LinearOrder

variable {α : Type*} [Nontrivial α] [LinearOrder α] [OrderBot α] [SuccOrder α]

@[simp]
/--
theorem `succ_eq_bot` / 定理 `succ_eq_bot`

English:
theorem succ_eq_bot
  given: (a : WithBot α)
  statement: WithBot.succ a = ⊥ ↔ a = ⊥
  proof: by
  cases a
  · simp
  · simpa [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false] using Order.succ_ne_bot _

中文:
定理 succ_eq_bot
  条件: (a : WithBot α)
  结论: WithBot.succ a = ⊥ ↔ a = ⊥
  证明: by
  cases a
  · simp
  · simpa [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false] using Order.succ_ne_bot _

Depends on / 依赖: Order.succ_ne_bot, WithBot, WithBot.coe_ne_bot, WithBot.succ_coe, coe_ne_bot, iff_false, succ_coe, succ_ne_bot
-/
theorem succ_eq_bot (a : WithBot α) : WithBot.succ a = ⊥ ↔ a = ⊥ := by
  cases a
  · simp
  · simpa [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false] using Order.succ_ne_bot _

end LinearOrder
end WithBot

namespace WithTop
variable {α : Type*} [Preorder α] [OrderTop α] [PredOrder α] {x y : WithTop α}

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: (a : WithTop α)
  body: a.recTopCoe ⊤ Order.pred

中文:
定义 pred
  签名: (a : WithTop α)
  定义体: a.recTopCoe ⊤ Order.pred

Depends on / 依赖: Order.pred, a.recTopCoe, recTopCoe
-/
def pred (a : WithTop α) : α := a.recTopCoe ⊤ Order.pred

/--
lemma `pred_top` / 引理 `pred_top`

English:
lemma pred_top
  statement: pred (⊤ : WithTop α) = ⊤
  proof: rfl

中文:
引理 pred_top
  结论: pred (⊤ : WithTop α) = ⊤
  证明: rfl
-/
@[simp] lemma pred_top : pred (⊤ : WithTop α) = ⊤ := rfl

/--
lemma `pred_coe` / 引理 `pred_coe`

English:
lemma pred_coe
  given: (a : α)
  statement: pred (a : WithTop α) = Order.pred a
  proof: rfl

中文:
引理 pred_coe
  条件: (a : α)
  结论: pred (a : WithTop α) = Order.pred a
  证明: rfl
-/
@[simp] lemma pred_coe (a : α) : pred (a : WithTop α) = Order.pred a := rfl

/--
lemma `pred_eq_pred` / 引理 `pred_eq_pred`

English:
lemma pred_eq_pred
  statement: forall a : WithTop α, pred a = Order.pred a

中文:
引理 pred_eq_pred
  结论: 对任意 a : WithTop α, pred a = Order.pred a
-/
lemma pred_eq_pred : forall a : WithTop α, pred a = Order.pred a
  | ⊤ => rfl
  | (a : α) => rfl

/--
lemma `pred_mono` / 引理 `pred_mono`

English:
lemma pred_mono
  statement: Monotone (pred : WithTop α -> α)

中文:
引理 pred_mono
  结论: 递增 (pred : WithTop α -> α)
-/
lemma pred_mono : Monotone (pred : WithTop α -> α)
  | _, ⊤, _ => by simp
  | ⊤, (a : α), hab => by simp at hab
  | (a : α), (b : α), hab => Order.pred_le_pred (by simpa using hab)

/--
lemma `pred_strictMono` / 引理 `pred_strictMono`

English:
lemma pred_strictMono
  given: [NoMinOrder α]
  statement: StrictMono (pred : WithTop α -> α)

中文:
引理 pred_strictMono
  条件: [NoMin序 α]
  结论: 严格递增 (pred : WithTop α -> α)
-/
lemma pred_strictMono [NoMinOrder α] : StrictMono (pred : WithTop α -> α)
  | (b : α), ⊤, hab => by simp
  | (a : α), (b : α), hab => Order.pred_lt_pred (by simpa using hab)

/--
lemma `pred_le_pred` / 引理 `pred_le_pred`

English:
lemma pred_le_pred
  given: (hxy : x <= y)
  statement: x.pred <= y.pred
  proof: pred_mono hxy

中文:
引理 pred_le_pred
  条件: (hxy : x <= y)
  结论: x.pred <= y.pred
  证明: pred_mono hxy
-/
@[gcongr] lemma pred_le_pred (hxy : x <= y) : x.pred <= y.pred := pred_mono hxy
/--
lemma `pred_lt_pred` / 引理 `pred_lt_pred`

English:
lemma pred_lt_pred
  given: [NoMinOrder α] (hxy : x < y)
  statement: x.pred < y.pred
  proof: pred_strictMono hxy

中文:
引理 pred_lt_pred
  条件: [NoMin序 α] (hxy : x < y)
  结论: x.pred < y.pred
  证明: pred_strictMono hxy
-/
@[gcongr] lemma pred_lt_pred [NoMinOrder α] (hxy : x < y) : x.pred < y.pred := pred_strictMono hxy

section LinearOrder

variable {α : Type*} [Nontrivial α] [LinearOrder α] [OrderTop α] [PredOrder α]

@[simp]
/--
theorem `pred_eq_top` / 定理 `pred_eq_top`

English:
theorem pred_eq_top
  given: (a : WithTop α)
  statement: WithTop.pred a = ⊤ ↔ a = ⊤
  proof: by
  cases a <;> simp [Order.pred_ne_top]

中文:
定理 pred_eq_top
  条件: (a : WithTop α)
  结论: WithTop.pred a = ⊤ ↔ a = ⊤
  证明: by
  cases a <;> simp [Order.pred_ne_top]

Depends on / 依赖: Order.pred_ne_top, pred_ne_top
-/
theorem pred_eq_top (a : WithTop α) : WithTop.pred a = ⊤ ↔ a = ⊤ := by
  cases a <;> simp [Order.pred_ne_top]

end LinearOrder
end WithTop
