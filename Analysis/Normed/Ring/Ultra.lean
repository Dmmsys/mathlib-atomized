/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Ultrametric norms on rings where the norm of one is one

This file contains results on the behavior of norms in ultrametric normed rings.
The norm must send one to one.

## Main results

* `norm_intCast_le_one`:
  the norm of the image of an integer in the ring is always less than or equal to one

## Implementation details

A `[NormedRing R]` only assumes a submultiplicative norm and does not have `[NormOneClass R]`.
The weakest ring-like structure that has a bundled norm such that `‖1‖ = 1` is
`[NormedDivisionRing K]`.
Since the statements below hold in any context, we can state them
in an unbundled fashion using `[NormOneClass R]`.
In fact one can actually prove all these lemmas only assuming
`{R : Type*} [SeminormedAddGroup R] [One R] [NormOneClass R] [IsUltrametricDist R]`.
But one has to give the typeclass machinery a little help in order to get it to recognise that there
is a coercion from `ℕ` or `ℤ` to `R`.
Instead, we use weakest pre-existing typeclass that implies both
`[SeminormedAddGroup R]` and `[AddGroupWithOne R]`, which is `[SeminormedRing R]`.

## Tags

ultrametric, nonarchimedean
-/

public section
open Metric NNReal

namespace IsUltrametricDist

section NormOneClass

variable {R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-
**IsUltrametricDist.norm_add_one_le_max_norm_one** 是 Mathlib 中的一个引理，位于命名空间 `IsUl
trametricDist`。
形式化陈述：norm_add_one_le_max_norm_one (x : R) : ‖x + 1‖ <= max ‖x‖ 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `IsUltrametricDist.norm_add_le_max`：∀ {S : Type u_1} [inst : SeminormedAd
dGroup S] [IsUltrametricDist S] (x y : S), ‖x + y‖ ≤ max ‖x‖ ‖y‖
-/
lemma norm_add_one_le_max_norm_one (x : R) :
    ‖x + 1‖ ≤ max ‖x‖ 1 := by
  simpa only [le_max_iff, norm_one] using norm_add_le_max x 1
/-
**IsUltrametricDist.nnnorm_add_one_le_max_nnnorm_one** 是 Mathlib 中的一个引理，位于命名空间 `
IsUltrametricDist`。
形式化陈述：nnnorm_add_one_le_max_nnnorm_one (x : R) : ‖x + 1‖₊ <= max ‖x‖₊ 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.norm_add_one_le_max_norm_one`：norm_add_one_le_max_norm
_one (x : R) : ‖x + 1‖ <= max ‖x‖ 1
-/
lemma nnnorm_add_one_le_max_nnnorm_one (x : R) :
    ‖x + 1‖₊ ≤ max ‖x‖₊ 1 :=
  norm_add_one_le_max_norm_one _

variable (R)
/-
**IsUltrametricDist.nnnorm_natCast_le_one** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametr
icDist`。
形式化陈述：nnnorm_natCast_le_one (n : Nat) : ‖(n : R)‖₊ <= 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `IsUltrametricDist.nnnorm_add_one_le_max_nnnorm_one`：nnnorm_add_one_le_ma
x_nnnorm_one (x : R) : ‖x + 1‖₊ <= max ‖x‖₊ 1
-/
lemma nnnorm_natCast_le_one (n : ℕ) :
    ‖(n : R)‖₊ ≤ 1 := by
  induction n with
  | zero => simp only [Nat.cast_zero, nnnorm_zero, zero_le]
  | succ n hn => simpa only [Nat.cast_add, Nat.cast_one, hn, max_eq_right] using
    nnnorm_add_one_le_max_nnnorm_one (n : R)
/-
**IsUltrametricDist.norm_natCast_le_one** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametric
Dist`。
形式化陈述：norm_natCast_le_one (n : Nat) : ‖(n : R)‖ <= 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.nnnorm_natCast_le_one`：nnnorm_natCast_le_one (n : Nat)
 : ‖(n : R)‖₊ <= 1
-/
lemma norm_natCast_le_one (n : ℕ) :
    ‖(n : R)‖ ≤ 1 :=
  nnnorm_natCast_le_one R n
/-
**IsUltrametricDist.nnnorm_intCast_le_one** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametr
icDist`。
形式化陈述：nnnorm_intCast_le_one (z : Int) : ‖(z : R)‖₊ <= 1
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `IsUltrametricDist.nnnorm_natCast_le_one`：nnnorm_natCast_le_one (n : Nat)
 : ‖(n : R)‖₊ <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
-/
lemma nnnorm_intCast_le_one (z : ℤ) :
    ‖(z : R)‖₊ ≤ 1 := by
  cases z <;>
  simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc, Nat.cast_one, nnnorm_neg]
    using nnnorm_natCast_le_one _ _
/-
**IsUltrametricDist.norm_intCast_le_one** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametric
Dist`。
形式化陈述：norm_intCast_le_one (z : Int) : ‖(z : R)‖ <= 1
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.nnnorm_intCast_le_one`：nnnorm_intCast_le_one (z : Int)
 : ‖(z : R)‖₊ <= 1
-/
lemma norm_intCast_le_one (z : ℤ) :
    ‖(z : R)‖ ≤ 1 :=
  nnnorm_intCast_le_one _ z

end NormOneClass

end IsUltrametricDist

