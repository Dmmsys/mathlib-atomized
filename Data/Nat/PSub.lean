/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Partial predecessor and partial subtraction on the natural numbers

The usual definition of natural number subtraction (`Nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `Nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `Option` type instead:

## Main definitions

- `Nat.ppred`: a partial predecessor operation
- `Nat.psub`: a partial subtraction operation

-/

@[expose] public section

namespace Nat

/--
Definition of `ppred` / `ppred` 的定义

English:
definition ppred
  signature: : Nat -> Option Nat

中文:
定义 ppred
  签名: : 自然数 -> 选项类型 自然数
-/
def ppred : Nat -> Option Nat
  | 0 => none
  | n + 1 => some n

@[simp]
/--
theorem `ppred_zero` / 定理 `ppred_zero`

English:
theorem ppred_zero
  statement: ppred 0 = none
  proof: rfl

@[simp]

中文:
定理 ppred_zero
  结论: ppred 0 = none
  证明: rfl

@[simp]
-/
theorem ppred_zero : ppred 0 = none := rfl

@[simp]
/--
theorem `ppred_succ` / 定理 `ppred_succ`

English:
theorem ppred_succ
  given: {n : Nat}
  statement: ppred (succ n) = some n
  proof: rfl

中文:
定理 ppred_succ
  条件: {n : 自然数}
  结论: ppred (succ n) = some n
  证明: rfl
-/
theorem ppred_succ {n : Nat} : ppred (succ n) = some n := rfl

/--
Definition of `psub` / `psub` 的定义

English:
definition psub
  signature: (m : Nat)

中文:
定义 psub
  签名: (m : 自然数)
-/
def psub (m : Nat) : Nat -> Option Nat
  | 0 => some m
  | n + 1 => psub m n >>= ppred

@[simp]
/--
theorem `psub_zero` / 定理 `psub_zero`

English:
theorem psub_zero
  given: {m : Nat}
  statement: psub m 0 = some m
  proof: rfl

@[simp]

中文:
定理 psub_zero
  条件: {m : 自然数}
  结论: psub m 0 = some m
  证明: rfl

@[simp]
-/
theorem psub_zero {m : Nat} : psub m 0 = some m := rfl

@[simp]
/--
theorem `psub_succ` / 定理 `psub_succ`

English:
theorem psub_succ
  given: {m n : Nat}
  statement: psub m (succ n) = psub m n >>= ppred
  proof: rfl

中文:
定理 psub_succ
  条件: {m n : 自然数}
  结论: psub m (succ n) = psub m n >>= ppred
  证明: rfl
-/
theorem psub_succ {m n : Nat} : psub m (succ n) = psub m n >>= ppred := rfl

/--
theorem `pred_eq_ppred` / 定理 `pred_eq_ppred`

English:
theorem pred_eq_ppred
  given: (n : Nat)
  statement: pred n = (ppred n).getD 0
  proof: by cases n <;> rfl

中文:
定理 pred_eq_ppred
  条件: (n : 自然数)
  结论: pred n = (ppred n).getD 0
  证明: by cases n <;> rfl
-/
theorem pred_eq_ppred (n : Nat) : pred n = (ppred n).getD 0 := by cases n <;> rfl

/--
theorem `sub_eq_psub` / 定理 `sub_eq_psub`

English:
theorem sub_eq_psub
  given: (m : Nat)
  statement: forall n, m - n = (psub m n).getD 0

中文:
定理 sub_eq_psub
  条件: (m : 自然数)
  结论: 对任意 n, m - n = (psub m n).getD 0
-/
theorem sub_eq_psub (m : Nat) : forall n, m - n = (psub m n).getD 0
  | 0 => rfl
| n + 1 => (pred_eq_ppred (m - n)).trans by rw [sub_eq_psub m n, psub]; cases psub m n <;> rfl

@[simp]
/--
theorem `ppred_eq_some` / 定理 `ppred_eq_some`

English:
theorem ppred_eq_some
  given: {m : Nat}
  statement: forall {n}, ppred n = some m ↔ succ m = n

中文:
定理 ppred_eq_some
  条件: {m : 自然数}
  结论: 对任意 {n}, ppred n = some m ↔ succ m = n
-/
theorem ppred_eq_some {m : Nat} : forall {n}, ppred n = some m ↔ succ m = n
  | 0 => by constructor <;> intro h <;> contradiction
  | n + 1 => by constructor <;> intro h <;> injection h <;> subst m <;> rfl

@[simp]
/--
theorem `ppred_eq_none` / 定理 `ppred_eq_none`

English:
theorem ppred_eq_none
  statement: forall {n : Nat}, ppred n = none ↔ n = 0

中文:
定理 ppred_eq_none
  结论: 对任意 {n : 自然数}, ppred n = none ↔ n = 0
-/
theorem ppred_eq_none : forall {n : Nat}, ppred n = none ↔ n = 0
  | 0 => by simp
  | n + 1 => by constructor <;> intro <;> contradiction

/--
theorem `psub_eq_some` / 定理 `psub_eq_some`

English:
theorem psub_eq_some
  given: {m : Nat}
  statement: forall {n k}, psub m n = some k ↔ k + n = m

中文:
定理 psub_eq_some
  条件: {m : 自然数}
  结论: 对任意 {n k}, psub m n = some k ↔ k + n = m
-/
theorem psub_eq_some {m : Nat} : forall {n k}, psub m n = some k ↔ k + n = m
  | 0, k => by simp [eq_comm]
  | n + 1, k => by
    apply Option.bind_eq_some_iff.trans
    simp only [psub_eq_some, ppred_eq_some]
    simp [add_comm, add_left_comm]

/--
theorem `psub_eq_none` / 定理 `psub_eq_none`

English:
theorem psub_eq_none
  given: {m n : Nat}
  statement: psub m n = none ↔ m < n
  proof: by
  rcases s : psub m n
  · simp only [true_iff]
    refine lt_of_not_ge fun h => ?_
    obtain ⟨k, e⟩ := le.dest h
    injection s.symm.trans (psub_eq_some.2 <| (add_comm _ _).trans e)
  · grind [psub_eq_some]

中文:
定理 psub_eq_none
  条件: {m n : 自然数}
  结论: psub m n = none ↔ m < n
  证明: by
  rcases s : psub m n
  · simp only [true_iff]
    refine lt_of_not_ge fun h => ?_
    obtain ⟨k, e⟩ := le.dest h
    injection s.symm.trans (psub_eq_some.2 <| (add_comm _ _).trans e)
  · grind [psub_eq_some]

Depends on / 依赖: add_comm, injection, le.dest, lt_of_not_ge, psub_eq_some, s.symm.trans, true_iff
-/
theorem psub_eq_none {m n : Nat} : psub m n = none ↔ m < n := by
  rcases s : psub m n
  · simp only [true_iff]
    refine lt_of_not_ge fun h => ?_
    obtain ⟨k, e⟩ := le.dest h
    injection s.symm.trans (psub_eq_some.2 <| (add_comm _ _).trans e)
  · grind [psub_eq_some]

/--
theorem `ppred_eq_pred` / 定理 `ppred_eq_pred`

English:
theorem ppred_eq_pred
  given: {n} (h : 0 < n)
  statement: ppred n = some (pred n)
  proof: ppred_eq_some.2 succ_pred_eq_of_pos h

中文:
定理 ppred_eq_pred
  条件: {n} (h : 0 < n)
  结论: ppred n = some (pred n)
  证明: ppred_eq_some.2 succ_pred_eq_of_pos h

Depends on / 依赖: ppred_eq_some, succ_pred_eq_of_pos
-/
theorem ppred_eq_pred {n} (h : 0 < n) : ppred n = some (pred n) :=
ppred_eq_some.2 succ_pred_eq_of_pos h

/--
theorem `psub_eq_sub` / 定理 `psub_eq_sub`

English:
theorem psub_eq_sub
  given: {m n} (h : n <= m)
  statement: psub m n = some (m - n)
  proof: psub_eq_some.2 Nat.sub_add_cancel h

中文:
定理 psub_eq_sub
  条件: {m n} (h : n <= m)
  结论: psub m n = some (m - n)
  证明: psub_eq_some.2 Nat.sub_add_cancel h

Depends on / 依赖: Nat.sub_add_cancel, psub_eq_some, sub_add_cancel
-/
theorem psub_eq_sub {m n} (h : n <= m) : psub m n = some (m - n) :=
psub_eq_some.2 Nat.sub_add_cancel h

/--
theorem `psub_add` / 定理 `psub_add`

English:
theorem psub_add
  given: (m n k)
  proof: by
    induction k with
    | zero => simp
    | succ n ih => simp only [ih, add_succ, psub_succ, bind_assoc]

中文:
定理 psub_add
  条件: (m n k)
  证明: by
    induction k with
    | zero => simp
    | succ n ih => simp only [ih, add_succ, psub_succ, bind_assoc]

Depends on / 依赖: add_succ, bind_assoc, psub_succ
-/
theorem psub_add (m n k) :
    psub m (n + k) = (do psub (← psub m n) k) := by
    induction k with
    | zero => simp
    | succ n ih => simp only [ih, add_succ, psub_succ, bind_assoc]

/-- Same as `psub`, but with a more efficient implementation. -/
@[inline]
/--
Definition of `psub'` / `psub'` 的定义

English:
definition psub'
  signature: (m n : Nat)
  body: if n <= m then some (m - n) else none

中文:
定义 psub'
  签名: (m n : 自然数)
  定义体: if n <= m then some (m - n) else none
-/
def psub' (m n : Nat) : Option Nat :=
  if n <= m then some (m - n) else none

/--
theorem `psub'_eq_psub` / 定理 `psub'_eq_psub`

English:
theorem psub'_eq_psub
  given: (m n)
  statement: psub' m n = psub m n
  proof: by
  rw [psub']
  split_ifs with h
  · exact (psub_eq_sub h).symm
  · exact (psub_eq_none.2 (not_le.1 h)).symm

中文:
定理 psub'_eq_psub
  条件: (m n)
  结论: psub' m n = psub m n
  证明: by
  rw [psub']
  split_ifs with h
  · exact (psub_eq_sub h).symm
  · exact (psub_eq_none.2 (not_le.1 h)).symm
-/
theorem psub'_eq_psub (m n) : psub' m n = psub m n := by
  rw [psub']
  split_ifs with h
  · exact (psub_eq_sub h).symm
  · exact (psub_eq_none.2 (not_le.1 h)).symm

end Nat
