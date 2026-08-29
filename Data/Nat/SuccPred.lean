/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.SuccPred.WithBot

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succOrder` and an archimedean `predOrder`.
-/

public section


open Function Order

namespace Nat
variable {m n : Nat}

/--
Instance `instSuccOrder` / 实例 `instSuccOrder`

English:
instance instSuccOrder
  signature: : SuccOrder Nat
  body: SuccOrder.ofSuccLeIff succ Nat.succ_le_iff

中文:
实例 instSuccOrder
  签名: : SuccOrder 自然数
  定义体: SuccOrder.ofSuccLeIff succ Nat.succ_le_iff

Depends on / 依赖: Nat.succ_le_iff, SuccOrder, SuccOrder.ofSuccLeIff, ofSuccLeIff, succ_le_iff
-/
instance instSuccOrder : SuccOrder Nat :=
  SuccOrder.ofSuccLeIff succ Nat.succ_le_iff

/--
Instance `instSuccAddOrder` / 实例 `instSuccAddOrder`

English:
instance instSuccAddOrder
  signature: : SuccAddOrder Nat
  body: ⟨fun _ => rfl⟩

中文:
实例 instSuccAddOrder
  签名: : SuccAddOrder 自然数
  定义体: ⟨fun _ => rfl⟩
-/
instance instSuccAddOrder : SuccAddOrder Nat := ⟨fun _ => rfl⟩

/--
Instance `instPredOrder` / 实例 `instPredOrder`

English:
instance instPredOrder
  signature: : PredOrder Nat where
  body: pred
  pred_le := pred_le
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
    · exact (not_succ_le_self _ ha).elim
  le_pred_of_lt {a} {b} h := by
    cases b
    · exact (a.not_lt_zero h).elim
    · exact le_of_succ_le_succ h

中文:
实例 instPredOrder
  签名: : PredOrder 自然数 where
  定义体: pred
  pred_le := pred_le
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
    · exact (not_succ_le_self _ ha).elim
  le_pred_of_lt {a} {b} h := by
    cases b
    · exact (a.not_lt_zero h).elim
    · exact le_of_succ_le_succ h
-/
instance instPredOrder : PredOrder Nat where
  pred := pred
  pred_le := pred_le
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
    · exact (not_succ_le_self _ ha).elim
  le_pred_of_lt {a} {b} h := by
    cases b
    · exact (a.not_lt_zero h).elim
    · exact le_of_succ_le_succ h

/--
Instance `instPredSubOrder` / 实例 `instPredSubOrder`

English:
instance instPredSubOrder
  signature: : PredSubOrder Nat
  body: ⟨fun _ => rfl⟩

@[simp]

中文:
实例 instPredSubOrder
  签名: : PredSubOrder 自然数
  定义体: ⟨fun _ => rfl⟩

@[simp]
-/
instance instPredSubOrder : PredSubOrder Nat := ⟨fun _ => rfl⟩

@[simp]
/--
theorem `succ_eq_succ` / 定理 `succ_eq_succ`

English:
theorem succ_eq_succ
  statement: Order.succ = succ
  proof: rfl

@[simp]

中文:
定理 succ_eq_succ
  结论: Order.succ = succ
  证明: rfl

@[simp]
-/
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
/--
theorem `pred_eq_pred` / 定理 `pred_eq_pred`

English:
theorem pred_eq_pred
  statement: Order.pred = pred
  proof: rfl

中文:
定理 pred_eq_pred
  结论: Order.pred = pred
  证明: rfl
-/
theorem pred_eq_pred : Order.pred = pred :=
  rfl

/--
theorem `succ_iterate` / 定理 `succ_iterate`

English:
theorem succ_iterate
  given: (a : Nat)
  statement: forall n, succ^[n] a = a + n
  proof: Order.succ_iterate a

中文:
定理 succ_iterate
  条件: (a : 自然数)
  结论: 对任意 n, succ^[n] a = a + n
  证明: Order.succ_iterate a
-/
protected theorem succ_iterate (a : Nat) : forall n, succ^[n] a = a + n :=
  Order.succ_iterate a

/--
theorem `pred_iterate` / 定理 `pred_iterate`

English:
theorem pred_iterate
  given: (a : Nat)
  statement: forall n, pred^[n] a = a - n

中文:
定理 pred_iterate
  条件: (a : 自然数)
  结论: 对任意 n, pred^[n] a = a - n
-/
protected theorem pred_iterate (a : Nat) : forall n, pred^[n] a = a - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ']; rw [sub_succ]
    exact congr_arg _ (Nat.pred_iterate a n)

/--
lemma `covBy_iff_add_one_eq` / 引理 `covBy_iff_add_one_eq`

English:
lemma covBy_iff_add_one_eq
  statement: m ⋖ n ↔ m + 1 = n
  proof: Order.covBy_iff_add_one_eq

中文:
引理 covBy_iff_add_one_eq
  结论: m ⋖ n ↔ m + 1 = n
  证明: Order.covBy_iff_add_one_eq
-/
@[simp] lemma covBy_iff_add_one_eq : m ⋖ n ↔ m + 1 = n := Order.covBy_iff_add_one_eq

/--
lemma `le_succ_iff_eq_or_le` / 引理 `le_succ_iff_eq_or_le`

English:
lemma le_succ_iff_eq_or_le
  statement: m <= n.succ ↔ m = n.succ ∨ m <= n
  proof: Order.le_succ_iff_eq_or_le

中文:
引理 le_succ_iff_eq_or_le
  结论: m <= n.succ ↔ m = n.succ ∨ m <= n
  证明: Order.le_succ_iff_eq_or_le

Depends on / 依赖: Order.le_succ_iff_eq_or_le, le_succ_iff_eq_or_le
-/
lemma le_succ_iff_eq_or_le : m <= n.succ ↔ m = n.succ ∨ m <= n := Order.le_succ_iff_eq_or_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSuccArchimedean Nat
  body: ⟨fun {a} {b} h => ⟨b - a, by rw [succ_eq_succ, Nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩

中文:
实例 :
  签名: IsSuccArchimedean 自然数
  定义体: ⟨fun {a} {b} h => ⟨b - a, by rw [succ_eq_succ, Nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩

Depends on / 依赖: Nat.succ_iterate, add_tsub_cancel_of_le, succ_eq_succ, succ_iterate
-/
instance : IsSuccArchimedean Nat :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [succ_eq_succ, Nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPredArchimedean Nat
  body: ⟨fun {a} {b} h => ⟨b - a, by rw [pred_eq_pred, Nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

中文:
实例 :
  签名: IsPredArchimedean 自然数
  定义体: ⟨fun {a} {b} h => ⟨b - a, by rw [pred_eq_pred, Nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

Depends on / 依赖: Nat.pred_iterate, pred_eq_pred, pred_iterate, tsub_tsub_cancel_of_le
-/
instance : IsPredArchimedean Nat :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [pred_eq_pred, Nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

/--
lemma `forall_ne_zero_iff` / 引理 `forall_ne_zero_iff`

English:
lemma forall_ne_zero_iff
  given: (P : Nat -> Prop)
  proof: SuccOrder.forall_ne_bot_iff P

中文:
引理 forall_ne_zero_iff
  条件: (P : 自然数 -> 命题)
  证明: SuccOrder.forall_ne_bot_iff P

Depends on / 依赖: SuccOrder, SuccOrder.forall_ne_bot_iff, forall_ne_bot_iff
-/
lemma forall_ne_zero_iff (P : Nat -> Prop) :
    (forall i, i != 0 -> P i) ↔ (forall i, P (i + 1)) :=
  SuccOrder.forall_ne_bot_iff P

end Nat

/--
theorem `Fin.covBy_iff` / 定理 `Fin.covBy_iff`

English:
theorem Fin.covBy_iff
  given: {n : Nat} {a b : Fin n}
  statement: a ⋖ b ↔ (a : Nat) ⋖ b
  proof: and_congr_right' ⟨fun h c ha hb => @h ⟨c, hb.trans b.prop⟩ ha hb, fun h _c hc => h hc⟩

@[deprecated Fin.covBy_iff "use Fin.covBy_iff.symm instead" (since := "2026-02-13")]

中文:
定理 Fin.covBy_iff
  条件: {n : 自然数} {a b : Fin n}
  结论: a ⋖ b ↔ (a : 自然数) ⋖ b
  证明: and_congr_right' ⟨fun h c ha hb => @h ⟨c, hb.trans b.prop⟩ ha hb, fun h _c hc => h hc⟩

@[deprecated Fin.covBy_iff "use Fin.covBy_iff.symm instead" (since := "2026-02-13")]
-/
@[simp] theorem Fin.covBy_iff {n : Nat} {a b : Fin n} : a ⋖ b ↔ (a : Nat) ⋖ b :=
  and_congr_right' ⟨fun h c ha hb => @h ⟨c, hb.trans b.prop⟩ ha hb, fun h _c hc => h hc⟩

@[deprecated Fin.covBy_iff "use Fin.covBy_iff.symm instead" (since := "2026-02-13")]
/--
theorem `Fin.coe_covBy_iff` / 定理 `Fin.coe_covBy_iff`

English:
theorem Fin.coe_covBy_iff
  given: {n : Nat} {a b : Fin n}
  statement: (a : Nat) ⋖ b ↔ a ⋖ b
  proof: Fin.covBy_iff.symm

alias ⟨CovBy.coe_fin, _⟩ := Fin.covBy_iff

@[simp]

中文:
定理 Fin.coe_covBy_iff
  条件: {n : 自然数} {a b : Fin n}
  结论: (a : 自然数) ⋖ b ↔ a ⋖ b
  证明: Fin.covBy_iff.symm

alias ⟨CovBy.coe_fin, _⟩ := Fin.covBy_iff

@[simp]

Depends on / 依赖: Fin.covBy_iff.symm, covBy_iff
-/
theorem Fin.coe_covBy_iff {n : Nat} {a b : Fin n} : (a : Nat) ⋖ b ↔ a ⋖ b := Fin.covBy_iff.symm

alias ⟨CovBy.coe_fin, _⟩ := Fin.covBy_iff

@[simp]
/--
theorem `withBotSucc_zero` / 定理 `withBotSucc_zero`

English:
theorem withBotSucc_zero
  statement: WithBot.succ 0 = 1
  proof: rfl

@[simp]

中文:
定理 withBotSucc_zero
  结论: WithBot.succ 0 = 1
  证明: rfl

@[simp]
-/
theorem withBotSucc_zero : WithBot.succ 0 = 1 := rfl

@[simp]
/--
theorem `withBotSucc_one` / 定理 `withBotSucc_one`

English:
theorem withBotSucc_one
  statement: WithBot.succ 1 = 2
  proof: rfl

中文:
定理 withBotSucc_one
  结论: WithBot.succ 1 = 2
  证明: rfl
-/
theorem withBotSucc_one : WithBot.succ 1 = 2 := rfl
