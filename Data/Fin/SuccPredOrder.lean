/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.SuccPred.Basic

/-!
# `SuccOrder` and `PredOrder` of `Fin n`

In this file, we show that `Fin n` is both a `SuccOrder` and a `PredOrder`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `Fin` instance.

-/

public section


namespace Fin

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forall {n : Nat}, SuccOrder (Fin n)

中文:
实例 :
  签名: 对任意 {n : 自然数}, SuccOrder (Fin n)

Depends on / 依赖: Fin.eq_castSucc_of_ne_last, eq_castSucc_of_ne_last
-/
instance : forall {n : Nat}, SuccOrder (Fin n)
  | 0 => by constructor <;> intro a <;> exact elim0 a
  | n + 1 =>
    SuccOrder.ofCore (Fin.lastCases (Fin.last n) Fin.succ)
      (fun {i} hi j => by
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (by simpa using! hi)
        simp [castSucc_lt_iff_succ_le])
      (fun i hi => by
        obtain rfl : i = Fin.last n := by simpa using! hi
        simp)

/--
lemma `orderSucc_eq` / 引理 `orderSucc_eq`

English:
lemma orderSucc_eq
  given: {n : Nat}
  proof: rfl

中文:
引理 orderSucc_eq
  条件: {n : 自然数}
  证明: rfl
-/
lemma orderSucc_eq {n : Nat} :
    Order.succ = Fin.lastCases (Fin.last n) Fin.succ := rfl

/--
lemma `orderSucc_apply` / 引理 `orderSucc_apply`

English:
lemma orderSucc_apply
  given: {n : Nat} (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 orderSucc_apply
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: rfl

@[simp]
-/
lemma orderSucc_apply {n : Nat} (i : Fin (n + 1)) :
    Order.succ i = Fin.lastCases (Fin.last n) Fin.succ i := rfl

@[simp]
/--
lemma `orderSucc_last` / 引理 `orderSucc_last`

English:
lemma orderSucc_last
  given: (n : Nat)
  proof: by
  simp [orderSucc_apply]

@[simp]

中文:
引理 orderSucc_last
  条件: (n : 自然数)
  证明: by
  simp [orderSucc_apply]

@[simp]

Depends on / 依赖: orderSucc_apply
-/
lemma orderSucc_last (n : Nat) :
    Order.succ (Fin.last n) = Fin.last n := by
  simp [orderSucc_apply]

@[simp]
/--
lemma `orderSucc_castSucc` / 引理 `orderSucc_castSucc`

English:
lemma orderSucc_castSucc
  given: {n : Nat} (i : Fin n)
  proof: by
  simp [orderSucc_apply]

中文:
引理 orderSucc_castSucc
  条件: {n : 自然数} (i : Fin n)
  证明: by
  simp [orderSucc_apply]

Depends on / 依赖: orderSucc_apply
-/
lemma orderSucc_castSucc {n : Nat} (i : Fin n) :
    Order.succ i.castSucc = i.succ := by
  simp [orderSucc_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forall {n : Nat}, PredOrder (Fin n)

中文:
实例 :
  签名: 对任意 {n : 自然数}, PredOrder (Fin n)

Depends on / 依赖: Fin.eq_succ_of_ne_zero, eq_succ_of_ne_zero
-/
instance : forall {n : Nat}, PredOrder (Fin n)
  | 0 => by constructor <;> first | intro a; exact elim0 a
  | n + 1 =>
    PredOrder.ofCore
      (Fin.cases 0 Fin.castSucc)
      (fun {i} hi j => by
        obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by simpa using! hi)
        simp [le_castSucc_iff])
      (fun i hi => by
        obtain rfl : i = 0 := by simpa using! hi
        rfl)

/--
lemma `orderPred_eq` / 引理 `orderPred_eq`

English:
lemma orderPred_eq
  given: {n : Nat}
  proof: rfl

中文:
引理 orderPred_eq
  条件: {n : 自然数}
  证明: rfl
-/
lemma orderPred_eq {n : Nat} :
    Order.pred = Fin.cases 0 Fin.castSucc (n := n) := rfl

/--
lemma `orderPred_apply` / 引理 `orderPred_apply`

English:
lemma orderPred_apply
  given: {n : Nat} (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 orderPred_apply
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: rfl

@[simp]
-/
lemma orderPred_apply {n : Nat} (i : Fin (n + 1)) :
    Order.pred i = Fin.cases 0 Fin.castSucc i := rfl

@[simp]
/--
lemma `orderPred_zero` / 引理 `orderPred_zero`

English:
lemma orderPred_zero
  given: (n : Nat)
  proof: rfl

@[simp]

中文:
引理 orderPred_zero
  条件: (n : 自然数)
  证明: rfl

@[simp]
-/
lemma orderPred_zero (n : Nat) :
    Order.pred (0 : Fin (n + 1)) = 0 :=
  rfl

@[simp]
/--
lemma `orderPred_succ` / 引理 `orderPred_succ`

English:
lemma orderPred_succ
  given: {n : Nat} (i : Fin n)
  proof: rfl

中文:
引理 orderPred_succ
  条件: {n : 自然数} (i : Fin n)
  证明: rfl
-/
lemma orderPred_succ {n : Nat} (i : Fin n) :
    Order.pred i.succ = i.castSucc :=
  rfl

end Fin
