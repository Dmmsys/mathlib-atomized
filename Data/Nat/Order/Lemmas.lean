/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.ByContra

/-!
# Further lemmas about the natural numbers

The distinction between this file and `Mathlib/Algebra/Order/Ring/Nat.lean` is not particularly
clear. They were separated for now to minimize the porting requirements for tactics
during the transition to mathlib4. Please feel free to reorganize these two files.
-/

public section

assert_not_exists RelIso

namespace Nat



/--
Instance `Subtype.orderBot` / 实例 `Subtype.orderBot`

English:
instance Subtype.orderBot
  signature: (s : Set Nat) [DecidablePred (· in s)] [h : Nonempty s]
  body: ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2

中文:
实例 子类型.orderBot
  签名: (s : 集合 自然数) [DecidablePred (· in s)] [h : 非空 s]
  定义体: ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2

Depends on / 依赖: Nat.find, Nat.find_spec, find_spec, nonempty_subtype
-/
instance Subtype.orderBot (s : Set Nat) [DecidablePred (· in s)] [h : Nonempty s] : OrderBot s where
  bot := ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2

/--
Instance `Subtype.semilatticeSup` / 实例 `Subtype.semilatticeSup`

English:
instance Subtype.semilatticeSup
  signature: (p : Nat -> Prop)
  body: { Subtype.instLinearOrder p, LinearOrder.toLattice with }

中文:
实例 子类型.semilatticeSup
  签名: (p : 自然数 -> 命题)
  定义体: { Subtype.instLinearOrder p, LinearOrder.toLattice with }

Depends on / 依赖: LinearOrder, LinearOrder.toLattice, Subtype, Subtype.instLinearOrder, instLinearOrder, toLattice
-/
instance Subtype.semilatticeSup (p : Nat -> Prop) : SemilatticeSup (Subtype p) :=
  { Subtype.instLinearOrder p, LinearOrder.toLattice with }

/--
theorem `Subtype.coe_bot` / 定理 `Subtype.coe_bot`

English:
theorem Subtype.coe_bot
  given: {s : Set Nat} [DecidablePred (· in s)] [h : Nonempty s]
  proof: rfl

中文:
定理 子类型.coe_bot
  条件: {s : 集合 自然数} [DecidablePred (· in s)] [h : 非空 s]
  证明: rfl
-/
theorem Subtype.coe_bot {s : Set Nat} [DecidablePred (· in s)] [h : Nonempty s] :
    ((⊥ : s) : Nat) = Nat.find (nonempty_subtype.1 h) :=
  rfl

/--
theorem `set_eq_univ` / 定理 `set_eq_univ`

English:
theorem set_eq_univ
  given: {S : Set Nat}
  statement: S = Set.univ ↔ 0 in S ∧ forall k : Nat, k in S -> k + 1 in S
  proof: ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩

中文:
定理 set_eq_univ
  条件: {S : 集合 自然数}
  结论: S = 集合.univ ↔ 0 in S ∧ 对任意 k : 自然数, k in S -> k + 1 in S
  证明: ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩

Depends on / 依赖: Set.eq_univ_of_forall, eq_univ_of_forall, set_induction
-/
theorem set_eq_univ {S : Set Nat} : S = Set.univ ↔ 0 in S ∧ forall k : Nat, k in S -> k + 1 in S :=
  ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩

/--
lemma `exists_not_and_succ_of_not_zero_of_exists` / 引理 `exists_not_and_succ_of_not_zero_of_exists`

English:
lemma exists_not_and_succ_of_not_zero_of_exists
  given: {p : Nat -> Prop} (H' : ¬ p 0) (H : exists n, p n)
  proof: by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
⟨k - 1, Nat.find_min H Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [le_zero_eq] at contra
  exact H' (contra ▸ hk)

中文:
引理 存在_not_and_succ_of_not_zero_of_存在
  条件: {p : 自然数 -> 命题} (H' : ¬ p 0) (H : 存在 n, p n)
  证明: by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
⟨k - 1, Nat.find_min H Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [le_zero_eq] at contra
  exact H' (contra ▸ hk)

Depends on / 依赖: Nat.find, Nat.find_min, Nat.find_spec, Nat.pred_lt, Nat.sub_add_cancel, classical, contra, find_min, find_spec, le_zero_eq, pred_lt, sub_add_cancel, this.ne
-/
lemma exists_not_and_succ_of_not_zero_of_exists {p : Nat -> Prop} (H' : ¬ p 0) (H : exists n, p n) :
    exists n, ¬ p n ∧ p (n + 1) := by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
⟨k - 1, Nat.find_min H Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [le_zero_eq] at contra
  exact H' (contra ▸ hk)

end Nat
