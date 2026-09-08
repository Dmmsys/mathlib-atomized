/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Data.Nat.Cast.Defs

/-!
# Lemmas about nonzero elements of an `AddMonoidWithOne`
-/

public section

open Nat

namespace NeZero

/-
**NeZero.one_le** 是 Mathlib 中的一个定理，位于命名空间 `NeZero`。
形式化陈述：one_le {n : Nat} [NeZero n] : 1 <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem one_le {n : ℕ} [NeZero n] : 1 ≤ n := by have := NeZero.ne n; lia
/-
**NeZero.natCast_ne** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：natCast_ne (n : Nat) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : 
R) != 0
参数：n : Nat；R；n : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma natCast_ne (n : ℕ) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : R) ≠ 0 := h.out
/-
**NeZero.of_neZero_natCast** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：of_neZero_natCast (R) [AddMonoidWithOne R] {n : Nat} [h : NeZero (n : R)] 
: NeZero n
参数：R；n : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [h : NeZero (n : R)] : NeZero n :=
  ⟨by rintro rfl; exact h.out Nat.cast_zero⟩
/-
**NeZero.pos_of_neZero_natCast** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : Nat} [NeZero (n : R)] 
: 0 < n
参数：R；n : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用引理 `NeZero.of_neZero_natCast`：of_neZero_natCast (R) [AddMonoidWithOne R] {n 
: Nat} [h : NeZero (n : R)] : NeZero n
-/
lemma pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_neZero_natCast R).out

end NeZero

