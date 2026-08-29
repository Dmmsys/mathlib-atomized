/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.SuccPred

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `SuccOrder` and an archimedean `PredOrder`.
-/

public section


open Function Order

namespace Int

/--
Instance `instSuccOrder` / 实例 `instSuccOrder`

English:
instance instSuccOrder
  signature: : SuccOrder Int
  body: { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }

中文:
实例 instSuccOrder
  签名: : SuccOrder 整数
  定义体: { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }

Depends on / 依赖: Iff.rfl, SuccOrder, SuccOrder.ofSuccLeIff, ofSuccLeIff
-/
instance instSuccOrder : SuccOrder Int :=
  { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }

/--
Instance `instSuccAddOrder` / 实例 `instSuccAddOrder`

English:
instance instSuccAddOrder
  signature: : SuccAddOrder Int
  body: ⟨fun _ => rfl⟩

中文:
实例 instSuccAddOrder
  签名: : SuccAddOrder 整数
  定义体: ⟨fun _ => rfl⟩
-/
instance instSuccAddOrder : SuccAddOrder Int := ⟨fun _ => rfl⟩

/--
Instance `instPredOrder` / 实例 `instPredOrder`

English:
instance instPredOrder
  signature: : PredOrder Int where
  body: pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_ge ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt

中文:
实例 instPredOrder
  签名: : PredOrder 整数 where
  定义体: pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_ge ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt
-/
instance instPredOrder : PredOrder Int where
  pred := pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_ge ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt

/--
Instance `instPredSubOrder` / 实例 `instPredSubOrder`

English:
instance instPredSubOrder
  signature: : PredSubOrder Int
  body: ⟨fun _ => rfl⟩

@[simp]

中文:
实例 instPredSubOrder
  签名: : PredSubOrder 整数
  定义体: ⟨fun _ => rfl⟩

@[simp]
-/
instance instPredSubOrder : PredSubOrder Int := ⟨fun _ => rfl⟩

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
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSuccArchimedean Int
  body: ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩

中文:
实例 :
  签名: IsSuccArchimedean 整数
  定义体: ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩

Depends on / 依赖: add_sub_assoc, add_sub_cancel_left, succ_iterate, toNat_sub_of_le
-/
instance : IsSuccArchimedean Int :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPredArchimedean Int
  body: ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

中文:
实例 :
  签名: IsPredArchimedean 整数
  定义体: ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

Depends on / 依赖: pred_iterate, sub_sub_cancel, toNat_sub_of_le
-/
instance : IsPredArchimedean Int :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/


@[simp, norm_cast]
/--
theorem `natCast_covBy` / 定理 `natCast_covBy`

English:
theorem natCast_covBy
  given: {a b : Nat}
  statement: (a : Int) ⋖ b ↔ a ⋖ b
  proof: by
  rw [Order.covBy_iff_add_one_eq]; rw [Order.covBy_iff_add_one_eq]
  exact Int.natCast_inj

中文:
定理 natCast_covBy
  条件: {a b : 自然数}
  结论: (a : 整数) ⋖ b ↔ a ⋖ b
  证明: by
  rw [Order.covBy_iff_add_one_eq]; rw [Order.covBy_iff_add_one_eq]
  exact Int.natCast_inj

Depends on / 依赖: Int.natCast_inj, Order.covBy_iff_add_one_eq, covBy_iff_add_one_eq, natCast_inj
-/
theorem natCast_covBy {a b : Nat} : (a : Int) ⋖ b ↔ a ⋖ b := by
  rw [Order.covBy_iff_add_one_eq]; rw [Order.covBy_iff_add_one_eq]
  exact Int.natCast_inj

end Int

alias ⟨_, CovBy.intCast⟩ := Int.natCast_covBy
