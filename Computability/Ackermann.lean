/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Ackermann function

In this file, we define the two-argument Ackermann function `ack`. Despite having a recursive
definition, we show that this isn't a primitive recursive function.

## Main results

- `exists_lt_ack_of_nat_primrec`: any primitive recursive function is pointwise bounded above by
  `ack m` for some `m`.
- `not_primrec₂_ack`: the two-argument Ackermann function is not primitive recursive.
- `computable₂_ack`: the two-argument Ackermann function is computable.

## Proof approach

We very broadly adapt the proof idea from
https://www.planetmath.org/ackermannfunctionisnotprimitiverecursive. Namely, we prove that for any
primitive recursive `f : ℕ → ℕ`, there exists `m` such that `f n < ack m n` for all `n`. This then
implies that `fun n => ack n n` can't be primitive recursive, and so neither can `ack`. We aren't
able to use the same bounds as in that proof though, since our approach of using pairing functions
differs from their approach of using multivariate functions.

The important bounds we show during the main inductive proof (`exists_lt_ack_of_nat_primrec`)
are the following. Assuming `∀ n, f n < ack a n` and `∀ n, g n < ack b n`, we have:

- `∀ n, pair (f n) (g n) < ack (max a b + 3) n`.
- `∀ n, g (f n) < ack (max a b + 2) n`.
- `∀ n, Nat.rec (f n.unpair.1) (fun (y IH : ℕ) => g (pair n.unpair.1 (pair y IH)))
  n.unpair.2 < ack (max a b + 9) n`.

The last one is evidently the hardest. Using `unpair_add_le`, we reduce it to the more manageable

- `∀ m n, rec (f m) (fun (y IH : ℕ) => g (pair m (pair y IH))) n <
  ack (max a b + 9) (m + n)`.

We then prove this by induction on `n`. Our proof crucially depends on `ack_pair_lt`, which is
applied twice, giving us a constant of `4 + 4`. The rest of the proof consists of simpler bounds
which bump up our constant to `9`.
-/

@[expose] public section


open Nat

/-- The two-argument Ackermann function, defined so that

- `ack 0 n = n + 1`
- `ack (m + 1) 0 = ack m 1`
- `ack (m + 1) (n + 1) = ack m (ack (m + 1) n)`.

This is of interest as both a fast-growing function, and as an example of a recursive function that
isn't primitive recursive. -/
/-
**ack** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two-argument Ackermann function, defined so that

- `ack 0 n = n + 1`
- `ack (m + 1) 0 = ack m 1`
- `ack (m + 1) (n + 1) = ack m (ack (m + 1) n)`.

This is of interest as both a fast-growing function, and as an example of a recu
rsive function that
isn't primitive recursive.
-/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

@[simp]
/-
**ack_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_zero (n : Nat) : ack 0 n = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack.eq_1`：∀ (x : ℕ), ack 0 x = x + 1
-/
theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]

@[simp]
/-
**ack_succ_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack.eq_2`：∀ (m : ℕ), ack m.succ 0 = ack m 1
-/
theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp]
/-
**ack_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack.eq_3`：∀ (m n : ℕ), ack m.succ n.succ = ack m (ack (m + 1) n)
-/
theorem ack_succ_succ (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

@[simp]
/-
**ack_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_one (n : Nat) : ack 1 n = n + 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack_succ_zero`：ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1
· 使用定理 `ack_zero`：ack_zero (n : Nat) : ack 0 n = n + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
-/
theorem ack_one (n : ℕ) : ack 1 n = n + 2 := by
  induction n with
  | zero => simp
  | succ n IH => simp [IH]

@[simp]
/-
**ack_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_two (n : Nat) : ack 2 n = 2 * n + 3
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack_succ_zero`：ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ack_zero`：ack_zero (n : Nat) : ack 0 n = n + 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ack_one`：ack_one (n : Nat) : ack 1 n = n + 2
-/
theorem ack_two (n : ℕ) : ack 2 n = 2 * n + 3 := by
  induction n with
  | zero => simp
  | succ n IH => simpa [mul_succ]

@[simp]
/-
**ack_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_three (n : Nat) : ack 3 n = 2 ^ (n + 3) - 3
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack_succ_zero`：ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ack_zero`：ack_zero (n : Nat) : ack 0 n = n + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ack_two`：ack_two (n : Nat) : ack 2 n = 2 * n + 3
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mul_sub_left_distrib`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Nat.add_sub_add_right`：∀ (n k m : ℕ), n + k - (m + k) = n - m
-/
theorem ack_three (n : ℕ) : ack 3 n = 2 ^ (n + 3) - 3 := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [ack_succ_succ, IH, ack_two, Nat.succ_add, Nat.pow_succ 2 (n + 3), mul_comm _ 2,
        Nat.mul_sub_left_distrib, ← Nat.sub_add_comm, two_mul 3, Nat.add_sub_add_right]
    calc 2 * 3
      _ ≤ 2 * 2 ^ 3 := by simp
      _ ≤ 2 * 2 ^ (n + 3) := by gcongr <;> lia
/-
**ack_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (m n : ℕ), 0 < ack m n
参数：m n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ack_pos : ∀ m n, 0 < ack m n
  | 0, n => by simp
  | m + 1, 0 => by
    rw [ack_succ_zero]
    apply ack_pos
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    apply ack_pos
/-
**one_lt_ack_succ_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (m n : ℕ), 1 < ack (m + 1) n
参数：m n : ℕ；m + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_lt_ack_succ_left : ∀ m n, 1 < ack (m + 1) n
  | 0, n => by simp
  | m + 1, 0 => by
    rw [ack_succ_zero]
    apply one_lt_ack_succ_left
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    apply one_lt_ack_succ_left
/-
**one_lt_ack_succ_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (m n : ℕ), 1 < ack m (n + 1)
参数：m n : ℕ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ack_zero`：ack_zero (n : Nat) : ack 0 n = n + 1
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `one_lt_ack_succ_left`：∀ (m n : ℕ), 1 < ack (m + 1) n
-/
theorem one_lt_ack_succ_right : ∀ m n, 1 < ack m (n + 1)
  | 0, n => by simp
  | m + 1, n => one_lt_ack_succ_left m (n + 1)
/-
**ack_strictMono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (m : ℕ), StrictMono (ack m)
参数：m : ℕ；ack m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ack_strictMono_right._unary`：∀ (_x : (_ : ℕ) ×' (a : ℕ) ×' (b : ℕ) ×' a 
< b), ack _x.1 _x.2.1 < ack _x.1 _x.2.2.1
-/
theorem ack_strictMono_right : ∀ m, StrictMono (ack m)
  | 0, n₁, n₂, h => by simpa using h
  | m + 1, 0, n + 1, _h => by
    rw [ack_succ_zero, ack_succ_succ]
    exact ack_strictMono_right _ (one_lt_ack_succ_left m n)
  | m + 1, n₁ + 1, n₂ + 1, h => by
    rw [ack_succ_succ, ack_succ_succ]
    apply ack_strictMono_right _ (ack_strictMono_right _ _)
    rwa [add_lt_add_iff_right] at h
/-
**ack_mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_mono_right (m : Nat) : Monotone (ack m)
参数：m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
-/
theorem ack_mono_right (m : ℕ) : Monotone (ack m) :=
  (ack_strictMono_right m).monotone
/-
**ack_injective_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_injective_right (m : Nat) : Function.Injective (ack m)
参数：m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
-/
theorem ack_injective_right (m : ℕ) : Function.Injective (ack m) :=
  (ack_strictMono_right m).injective

@[simp]
/-
**ack_lt_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_lt_iff_right {m n₁ n₂ : Nat} : ack m n₁ < ack m n₂ ↔ n₁ < n₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
-/
theorem ack_lt_iff_right {m n₁ n₂ : ℕ} : ack m n₁ < ack m n₂ ↔ n₁ < n₂ :=
  (ack_strictMono_right m).lt_iff_lt

@[simp]
/-
**ack_le_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_le_iff_right {m n₁ n₂ : Nat} : ack m n₁ <= ack m n₂ ↔ n₁ <= n₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
-/
theorem ack_le_iff_right {m n₁ n₂ : ℕ} : ack m n₁ ≤ ack m n₂ ↔ n₁ ≤ n₂ :=
  (ack_strictMono_right m).le_iff_le

@[simp]
/-
**ack_inj_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_inj_right {m n₁ n₂ : Nat} : ack m n₁ = ack m n₂ ↔ n₁ = n₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ack_injective_right`：ack_injective_right (m : Nat) : Function.Injective 
(ack m)
-/
theorem ack_inj_right {m n₁ n₂ : ℕ} : ack m n₁ = ack m n₂ ↔ n₁ = n₂ :=
  (ack_injective_right m).eq_iff
/-
**max_ack_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_ack_right (m n₁ n₂ : Nat) : ack m (max n₁ n₂) = max (ack m n₁) (ack m 
n₂)
参数：m n₁ n₂ : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `ack_mono_right`：ack_mono_right (m : Nat) : Monotone (ack m)
-/
theorem max_ack_right (m n₁ n₂ : ℕ) : ack m (max n₁ n₂) = max (ack m n₁) (ack m n₂) :=
  (ack_mono_right m).map_max
/-
**add_lt_ack** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_lt_ack : forall m n, m + n < ack m n | 0, n => by simp | m + 1, 0 => b
y simpa using add_lt_ack m 1 | m + 1, n + 1 => calc m + 1 + n + 1 <= m + (m + n 
+ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_ack._unary`：∀ (_x : (_ : ℕ) ×' ℕ), _x.1 + _x.2 < ack _x.1 _x.2
-/
theorem add_lt_ack : ∀ m n, m + n < ack m n
  | 0, n => by simp
  | m + 1, 0 => by simpa using add_lt_ack m 1
  | m + 1, n + 1 =>
    calc
      m + 1 + n + 1 ≤ m + (m + n + 2) := by lia
      _ < ack m (m + n + 2) := add_lt_ack _ _
      _ ≤ ack m (ack (m + 1) n) :=
        ack_mono_right m <| le_of_eq_of_le (by rw [succ_eq_add_one]; ring_nf)
        <| succ_le_of_lt <| add_lt_ack (m + 1) n
      _ = ack (m + 1) (n + 1) := (ack_succ_succ m n).symm
/-
**add_add_one_le_ack** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_add_one_le_ack (m n : Nat) : m + n + 1 <= ack m n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `add_lt_ack`：add_lt_ack : forall m n, m + n < ack m n | 0, n => by simp |
 m + 1, 0 => by simpa using add_lt_ack m 1 | m + 1, n + 1 => calc m + 1 + n + 1 
…
-/
theorem add_add_one_le_ack (m n : ℕ) : m + n + 1 ≤ ack m n :=
  succ_le_of_lt (add_lt_ack m n)
/-
**lt_ack_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_ack_left (m n : Nat) : m < ack m n
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `add_lt_ack`：add_lt_ack : forall m n, m + n < ack m n | 0, n => by simp |
 m + 1, 0 => by simpa using add_lt_ack m 1 | m + 1, n + 1 => calc m + 1 + n + 1 
…
-/
theorem lt_ack_left (m n : ℕ) : m < ack m n :=
  (self_le_add_right m n).trans_lt <| add_lt_ack m n
/-
**lt_ack_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_ack_right (m n : Nat) : n < ack m n
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `add_lt_ack`：add_lt_ack : forall m n, m + n < ack m n | 0, n => by simp |
 m + 1, 0 => by simpa using add_lt_ack m 1 | m + 1, n + 1 => calc m + 1 + n + 1 
…
-/
theorem lt_ack_right (m n : ℕ) : n < ack m n :=
  (self_le_add_left n m).trans_lt <| add_lt_ack m n

-- we reorder the arguments to appease the equation compiler
/-
**ack_strict_mono_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ack_strict_mono_left' : ∀ {m₁ m₂} (n), m₁ < m₂ → ack m₁ n < ack m₂ n
  | m, 0, _ => fun h => (not_lt_zero m h).elim
  | 0, m + 1, 0 => fun _h => by simpa using one_lt_ack_succ_right m 0
  | 0, m + 1, n + 1 => fun h => by
    rw [ack_zero, ack_succ_succ]
    calc
      n + 1 + 1 ≤ m + (m + 1 + n + 1) := by lia
      _ ≤ m + ack (m + 1) n := by gcongr; exact add_add_one_le_ack ..
      _ < ack m (ack (m + 1) n) := add_lt_ack ..
  | m₁ + 1, m₂ + 1, 0 => fun h => by
    simpa using ack_strict_mono_left' 1 ((add_lt_add_iff_right 1).1 h)
  | m₁ + 1, m₂ + 1, n + 1 => fun h => by
    rw [ack_succ_succ, ack_succ_succ]
    exact
      (ack_strict_mono_left' _ <| (add_lt_add_iff_right 1).1 h).trans
        (ack_strictMono_right _ <| ack_strict_mono_left' n h)
/-
**ack_strictMono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_strictMono_left (n : Nat) : StrictMono fun m => ack m n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Computability.Ackermann.0.ack_strict_mono_left'`：∀ {m₁ 
m₂ : ℕ} (n : ℕ), m₁ < m₂ → ack m₁ n < ack m₂ n
-/
theorem ack_strictMono_left (n : ℕ) : StrictMono fun m => ack m n := fun _m₁ _m₂ =>
  ack_strict_mono_left' n
/-
**ack_mono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_mono_left (n : Nat) : Monotone fun m => ack m n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `ack_strictMono_left`：ack_strictMono_left (n : Nat) : StrictMono fun m =>
 ack m n
-/
theorem ack_mono_left (n : ℕ) : Monotone fun m => ack m n :=
  (ack_strictMono_left n).monotone
/-
**ack_injective_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_injective_left (n : Nat) : Function.Injective fun m => ack m n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `ack_strictMono_left`：ack_strictMono_left (n : Nat) : StrictMono fun m =>
 ack m n
-/
theorem ack_injective_left (n : ℕ) : Function.Injective fun m => ack m n :=
  (ack_strictMono_left n).injective

@[simp]
/-
**ack_lt_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_lt_iff_left {m₁ m₂ n : Nat} : ack m₁ n < ack m₂ n ↔ m₁ < m₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `ack_strictMono_left`：ack_strictMono_left (n : Nat) : StrictMono fun m =>
 ack m n
-/
theorem ack_lt_iff_left {m₁ m₂ n : ℕ} : ack m₁ n < ack m₂ n ↔ m₁ < m₂ :=
  (ack_strictMono_left n).lt_iff_lt

@[simp]
/-
**ack_le_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_le_iff_left {m₁ m₂ n : Nat} : ack m₁ n <= ack m₂ n ↔ m₁ <= m₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `ack_strictMono_left`：ack_strictMono_left (n : Nat) : StrictMono fun m =>
 ack m n
-/
theorem ack_le_iff_left {m₁ m₂ n : ℕ} : ack m₁ n ≤ ack m₂ n ↔ m₁ ≤ m₂ :=
  (ack_strictMono_left n).le_iff_le

@[simp]
/-
**ack_inj_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_inj_left {m₁ m₂ n : Nat} : ack m₁ n = ack m₂ n ↔ m₁ = m₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ack_injective_left`：ack_injective_left (n : Nat) : Function.Injective fu
n m => ack m n
-/
theorem ack_inj_left {m₁ m₂ n : ℕ} : ack m₁ n = ack m₂ n ↔ m₁ = m₂ :=
  (ack_injective_left n).eq_iff
/-
**max_ack_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_ack_left (m₁ m₂ n : Nat) : ack (max m₁ m₂) n = max (ack m₁ n) (ack m₂ 
n)
参数：m₁ m₂ n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `ack_mono_left`：ack_mono_left (n : Nat) : Monotone fun m => ack m n
-/
theorem max_ack_left (m₁ m₂ n : ℕ) : ack (max m₁ m₂) n = max (ack m₁ n) (ack m₂ n) :=
  (ack_mono_left n).map_max

@[gcongr]
/-
**ack_le_ack** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_le_ack {m₁ m₂ n₁ n₂ : Nat} (hm : m₁ <= m₂) (hn : n₁ <= n₂) : ack m₁ n₁
 <= ack m₂ n₂
参数：hm : m₁ <= m₂；hn : n₁ <= n₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ack_mono_left`：ack_mono_left (n : Nat) : Monotone fun m => ack m n
· 使用定理 `ack_mono_right`：ack_mono_right (m : Nat) : Monotone (ack m)
-/
theorem ack_le_ack {m₁ m₂ n₁ n₂ : ℕ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) : ack m₁ n₁ ≤ ack m₂ n₂ :=
  (ack_mono_left n₁ hm).trans <| ack_mono_right m₂ hn
/-
**ack_succ_right_le_ack_succ_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_succ_right_le_ack_succ_left (m n : Nat) : ack m (n + 1) <= ack (m + 1)
 n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ack_succ_zero`：ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
· 使用定理 `ack_mono_right`：ack_mono_right (m : Nat) : Monotone (ack m)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_add_one_le_ack`：add_add_one_le_ack (m n : Nat) : m + n + 1 <= ack m 
n
-/
theorem ack_succ_right_le_ack_succ_left (m n : ℕ) : ack m (n + 1) ≤ ack (m + 1) n := by
  rcases n with - | n
  · simp
  · rw [ack_succ_succ]
    apply ack_mono_right m (le_trans _ <| add_add_one_le_ack _ n)
    lia

-- All the inequalities from this point onwards are specific to the main proof.
/-
**sq_le_two_pow_add_one_minus_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sq_le_two_pow_add_one_minus_three (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) - 3 := by
  induction n with
  | zero => simp
  | succ k => cases k <;> lia
/-
**ack_add_one_sq_lt_ack_add_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (m n : ℕ), (ack m n + 1) ^ 2 ≤ ack (m + 3) n
参数：m n : ℕ；ack m n + 1；m + 3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ack_add_one_sq_lt_ack_add_three : ∀ m n, (ack m n + 1) ^ 2 ≤ ack (m + 3) n
  | 0, n => by simpa using sq_le_two_pow_add_one_minus_three (n + 2)
  | m + 1, 0 => by
    rw [ack_succ_zero, ack_succ_zero]
    apply ack_add_one_sq_lt_ack_add_three
  | m + 1, n + 1 => by
    rw [ack_succ_succ, ack_succ_succ]
    apply (ack_add_one_sq_lt_ack_add_three _ _).trans (ack_mono_right _ <| ack_mono_left _ _)
    lia
/-
**ack_ack_lt_ack_max_add_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_ack_lt_ack_max_add_two (m n k : Nat) : ack m (ack n k) < ack (max m n 
+ 2) k
参数：m n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ack_mono_left`：ack_mono_left (n : Nat) : Monotone fun m => ack m n
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
· 使用定理 `ack_strictMono_left`：ack_strictMono_left (n : Nat) : StrictMono fun m =>
 ack m n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
· 使用定理 `ack_succ_right_le_ack_succ_left`：ack_succ_right_le_ack_succ_left (m n : 
Nat) : ack m (n + 1) <= ack (m + 1) n
-/
theorem ack_ack_lt_ack_max_add_two (m n k : ℕ) : ack m (ack n k) < ack (max m n + 2) k :=
  calc
    ack m (ack n k) ≤ ack (max m n) (ack n k) := ack_mono_left _ (le_max_left _ _)
    _ < ack (max m n) (ack (max m n + 1) k) :=
      ack_strictMono_right _ <| ack_strictMono_left k <| lt_succ_of_le <| le_max_right m n
    _ = ack (max m n + 1) (k + 1) := (ack_succ_succ _ _).symm
    _ ≤ ack (max m n + 2) k := ack_succ_right_le_ack_succ_left _ _
/-
**ack_add_one_sq_lt_ack_add_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_add_one_sq_lt_ack_add_four (m n : Nat) : ack m ((n + 1) ^ 2) < ack (m 
+ 4) n
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `lt_ack_right`：lt_ack_right (m n : Nat) : n < ack m n
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ack_mono_right`：ack_mono_right (m : Nat) : Monotone (ack m)
· 使用定理 `ack_add_one_sq_lt_ack_add_three`：∀ (m n : ℕ), (ack m n + 1) ^ 2 ≤ ack (m
 + 3) n
· 使用定理 `ack_mono_left`：ack_mono_left (n : Nat) : Monotone fun m => ack m n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
· 使用定理 `ack_succ_right_le_ack_succ_left`：ack_succ_right_le_ack_succ_left (m n : 
Nat) : ack m (n + 1) <= ack (m + 1) n
-/
theorem ack_add_one_sq_lt_ack_add_four (m n : ℕ) : ack m ((n + 1) ^ 2) < ack (m + 4) n :=
  calc
    ack m ((n + 1) ^ 2) < ack m ((ack m n + 1) ^ 2) :=
      ack_strictMono_right m <| Nat.pow_lt_pow_left (succ_lt_succ <| lt_ack_right m n) two_ne_zero
    _ ≤ ack m (ack (m + 3) n) := ack_mono_right m <| ack_add_one_sq_lt_ack_add_three m n
    _ ≤ ack (m + 2) (ack (m + 3) n) := ack_mono_left _ <| by lia
    _ = ack (m + 3) (n + 1) := (ack_succ_succ _ n).symm
    _ ≤ ack (m + 4) n := ack_succ_right_le_ack_succ_left _ n
/-
**ack_pair_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ack_pair_lt (m n k : Nat) : ack m (pair n k) < ack (m + 4) (max n k)
参数：m n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
· 使用定理 `Nat.pair_lt_max_add_one_sq`：pair_lt_max_add_one_sq (m n : Nat) : pair m 
n < (max m n + 1) ^ 2
· 使用定理 `ack_add_one_sq_lt_ack_add_four`：ack_add_one_sq_lt_ack_add_four (m n : Na
t) : ack m ((n + 1) ^ 2) < ack (m + 4) n
-/
theorem ack_pair_lt (m n k : ℕ) : ack m (pair n k) < ack (m + 4) (max n k) :=
  (ack_strictMono_right m <| pair_lt_max_add_one_sq n k).trans <|
    ack_add_one_sq_lt_ack_add_four _ _

/-- If `f` is primitive recursive, there exists `m` such that `f n < ack m n` for all `n`. -/
/-
**exists_lt_ack_of_nat_primrec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_ack_of_nat_primrec {f : Nat -> Nat} (hf : Nat.Primrec f) : exist
s m, forall n, f n < ack m n
参数：hf : Nat.Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ack_pos`：∀ (m n : ℕ), 0 < ack m n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_eq_one_add`：∀ (n : ℕ), n.succ = 1 + n
· 使用定理 `add_lt_ack`：add_lt_ack : forall m n, m + n < ack m n | 0, n => by simp |
 m + 1, 0 => by simpa using add_lt_ack m 1 | m + 1, n + 1 => calc m + 1 + n + 1 
…
· 使用定理 `ack_zero`：ack_zero (n : Nat) : ack 0 n = n + 1
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.unpair_left_le`：∀ (n : ℕ), (Nat.unpair n).1 ≤ n
· 使用定理 `Nat.unpair_right_le`：unpair_right_le (n : Nat) : (unpair n).2 <= n
· 使用定理 `Nat.pair_lt_max_add_one_sq`：pair_lt_max_add_one_sq (m n : Nat) : pair m 
n < (max m n + 1) ^ 2
· 使用定理 `max_ack_left`：max_ack_left (m₁ m₂ n : Nat) : ack (max m₁ m₂) n = max (ac
k m₁ n) (ack m₂ n)
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ack_add_one_sq_lt_ack_add_three`：∀ (m n : ℕ), (ack m n + 1) ^ 2 ≤ ack (m
 + 3) n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ack_strictMono_right`：∀ (m : ℕ), StrictMono (ack m)
· 使用定理 `ack_ack_lt_ack_max_add_two`：ack_ack_lt_ack_max_add_two (m n k : Nat) : a
ck m (ack n k) < ack (max m n + 2) k
· 使用定理 `ack_strictMono_left`：ack_strictMono_left (n : Nat) : StrictMono fun m =>
 ack m n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ack_pair_lt`：ack_pair_lt (m n k : Nat) : ack m (pair n k) < ack (m + 4) 
(max n k)
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `ack_le_ack`：ack_le_ack {m₁ m₂ n₁ n₂ : Nat} (hm : m₁ <= m₂) (hn : n₁ <= n
₂) : ack m₁ n₁ <= ack m₂ n₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is primitive recursive, there exists `m` such that `f n < ack m n` for al
l `n`.
-/
theorem exists_lt_ack_of_nat_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ m, ∀ n, f n < ack m n := by
  induction hf with
  | zero => exact ⟨0, ack_pos 0⟩
  | succ =>
    refine ⟨1, fun n => ?_⟩
    rw [succ_eq_one_add]
    apply add_lt_ack
  | left =>
    refine ⟨0, fun n => ?_⟩
    rw [ack_zero, Nat.lt_succ_iff]
    exact unpair_left_le n
  | right =>
    refine ⟨0, fun n => ?_⟩
    rw [ack_zero, Nat.lt_succ_iff]
    exact unpair_right_le n
  | @pair f g hf hg IHf IHg =>
    obtain ⟨a, ha⟩ := IHf; obtain ⟨b, hb⟩ := IHg
    refine ⟨max a b + 3, fun n => ?_⟩
    calc
      pair (f n) (g n) < (max (f n) (g n) + 1) ^ 2 := pair_lt_max_add_one_sq ..
      _ ≤ (ack (max a b) n + 1) ^ 2 := by rw [max_ack_left]; gcongr; exacts [(ha n).le, (hb n).le]
      _ ≤ ack (max a b + 3) n := ack_add_one_sq_lt_ack_add_three ..
  | comp hf hg IHf IHg =>
    obtain ⟨a, ha⟩ := IHf; obtain ⟨b, hb⟩ := IHg
    exact
      ⟨max a b + 2, fun n =>
        (ha _).trans <| (ack_strictMono_right a <| hb n).trans <| ack_ack_lt_ack_max_add_two a b n⟩
  | @prec f g hf hg IHf IHg =>
    obtain ⟨a, ha⟩ := IHf; obtain ⟨b, hb⟩ := IHg
    -- We prove this simpler inequality first.
    have :
      ∀ {m n},
        rec (f m) (fun y IH => g <| pair m <| pair y IH) n < ack (max a b + 9) (m + n) := by
      intro m n
      -- We induct on n.
      induction n with
      | zero => -- The base case is easy.
        apply (ha m).trans (ack_strictMono_left m <| (le_max_left a b).trans_lt _)
        lia
      | succ n IH => -- We get rid of the first `pair`.
        simp only
        apply (hb _).trans ((ack_pair_lt _ _ _).trans_le _)
        -- If m is the maximum, we get a very weak inequality.
        rcases lt_or_ge _ m with h₁ | h₁
        · rw [max_eq_left h₁.le]
          gcongr <;> omega
        rw [max_eq_right h₁]
        -- We get rid of the second `pair`.
        apply (ack_pair_lt _ _ _).le.trans
        -- If n is the maximum, we get a very weak inequality.
        rcases lt_or_ge _ n with h₂ | h₂
        · rw [max_eq_left h₂.le, add_assoc]
          exact
            ack_le_ack (Nat.add_le_add (le_max_right a b) <| by simp)
              ((le_succ n).trans <| self_le_add_left _ _)
        rw [max_eq_right h₂]
        -- We now use the inductive hypothesis, and some simple algebraic manipulation.
        apply (ack_strictMono_right _ IH).le.trans
        rw [add_succ m, add_succ _ 8, succ_eq_add_one, succ_eq_add_one,
            ack_succ_succ (_ + 8), add_assoc]
        exact ack_mono_left _ (Nat.add_le_add (le_max_right a b) le_rfl)
    -- The proof is now simple.
    exact ⟨max a b + 9, fun n => this.trans_le <| ack_mono_right _ <| unpair_add_le n⟩
/-
**not_nat_primrec_ack_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_nat_primrec_ack_self : ¬Nat.Primrec fun n => ack n n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_ack_of_nat_primrec`：exists_lt_ack_of_nat_primrec {f : Nat -> N
at} (hf : Nat.Primrec f) : exists m, forall n, f n < ack m n
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
-/
theorem not_nat_primrec_ack_self : ¬Nat.Primrec fun n => ack n n := fun h => by
  obtain ⟨m, hm⟩ := exists_lt_ack_of_nat_primrec h
  exact (hm m).false
/-
**not_primrec_ack_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_primrec_ack_self : ¬Primrec fun n => ack n n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
· 使用定理 `not_nat_primrec_ack_self`：not_nat_primrec_ack_self : ¬Nat.Primrec fun n 
=> ack n n
-/
theorem not_primrec_ack_self : ¬Primrec fun n => ack n n := by
  rw [Primrec.nat_iff]
  exact not_nat_primrec_ack_self

/-- The Ackermann function is not primitive recursive. -/
/-
**not_primrec** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Ackermann function is not primitive recursive.
-/
theorem not_primrec₂_ack : ¬Primrec₂ ack := fun h =>
  not_primrec_ack_self <| h.comp Primrec.id Primrec.id

namespace Nat.Partrec.Code

/-- The code for the partially applied Ackermann function.
This is used to prove that the Ackermann function is computable. -/
/-
**Nat.Partrec.Code.pappAck** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：pappAck : Nat -> Code | 0 => .succ | n + 1 => step (pappAck n) where /-- Y
ields single recursion step on `pappAck`. -/ step (c : Code) : Code
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The code for the partially applied Ackermann function.
This is used to prove that the Ackermann function is computable.
-/
def pappAck : ℕ → Code
  | 0 => .succ
  | n + 1 => step (pappAck n)
where
  /-- Yields single recursion step on `pappAck`. -/
  step (c : Code) : Code :=
    .curry (.prec (.comp c (.const 1)) (.comp c (.comp .right .right))) 0
/-
**Nat.Partrec.Code.primrec_pappAck_step** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Partrec.C
ode`。
形式化陈述：primrec_pappAck_step : Primrec pappAck.step
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Nat.Partrec.Code.primrec₂_curry`：primrec₂_curry : Primrec₂ curry
· 使用定理 `Nat.Partrec.Code.primrec₂_prec`：primrec₂_prec : Primrec₂ prec
· 使用定理 `Nat.Partrec.Code.primrec₂_comp`：primrec₂_comp : Primrec₂ comp
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Nat.Primrec.const`：const : forall n : Nat, Nat.Primrec fun _ => n | 0 =>
 zero | n + 1 => Primrec.succ.comp (const n)  protected theorem id : Nat.Primrec
 id
-/
lemma primrec_pappAck_step : Primrec pappAck.step := by
  apply_rules
    [Code.primrec₂_curry.comp, Code.primrec₂_prec.comp, Code.primrec₂_comp.comp,
      _root_.Primrec.id, Primrec.const]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.Partrec.Code.eval_pappAck_step_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Partrec
.Code`。
形式化陈述：eval_pappAck_step_zero (c : Code) : (pappAck.step c).eval 0 = c.eval 1
参数：c : Code。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.eval_curry`：eval_curry (c n x) : eval (curry c n) x = e
val c (Nat.pair n x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Nat.Partrec.Code.eval_const`：∀ (n m : ℕ), (Nat.Partrec.Code.const n).eva
l m = Part.some n
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_pappAck_step_zero (c : Code) : (pappAck.step c).eval 0 = c.eval 1 := by
  simp [pappAck.step, Code.eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.Partrec.Code.eval_pappAck_step_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Partrec
.Code`。
形式化陈述：eval_pappAck_step_succ (c : Code) (n) : (pappAck.step c).eval (n + 1) = ((
pappAck.step c).eval n).bind c.eval
参数：c : Code；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partrec.Code.eval_curry`：eval_curry (c n x) : eval (curry c n) x = e
val c (Nat.pair n x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Nat.Partrec.Code.eval_const`：∀ (n m : ℕ), (Nat.Partrec.Code.const n).eva
l m = Part.some n
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_pappAck_step_succ (c : Code) (n) :
    (pappAck.step c).eval (n + 1) = ((pappAck.step c).eval n).bind c.eval := by
  simp [pappAck.step, Code.eval]
/-
**Nat.Partrec.Code.primrec_pappAck** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：primrec_pappAck : Primrec pappAck
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.nat_rec₁`：nat_rec₁ {f : Nat -> α -> α} (a : α) (hf : Primrec₂ f)
 : Primrec (Nat.rec a f)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用引理 `Nat.Partrec.Code.primrec_pappAck_step`：primrec_pappAck_step : Primrec pa
ppAck.step
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma primrec_pappAck : Primrec pappAck := by
  suffices Primrec (Nat.rec Code.succ (fun _ c => pappAck.step c)) by
    convert! this using 2 with n; induction n <;> simp [pappAck, *]
  apply_rules [Primrec.nat_rec₁, primrec_pappAck_step.comp, Primrec.snd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Nat.Partrec.Code.eval_pappAck** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Partrec.Code`。
形式化陈述：eval_pappAck (m n) : (pappAck m).eval n = Part.some (ack m n)
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ack.induct`：∀ (motive : ℕ → ℕ → Prop),   (∀ (n : ℕ), motive 0 n) →     (
∀ (m : ℕ), motive m 1 → motive m.succ 0) →       (∀ (m n : ℕ), motive (m + 1) n 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.Partrec.Code.eval.eq_2`：Nat.Partrec.Code.succ.eval = ↑Nat.succ
· 使用定理 `ack_zero`：ack_zero (n : Nat) : ack 0 n = n + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.Partrec.Code.eval_pappAck_step_zero`：eval_pappAck_step_zero (c : Cod
e) : (pappAck.step c).eval 0 = c.eval 1
· 使用定理 `ack_succ_zero`：ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1
· 使用引理 `Nat.Partrec.Code.eval_pappAck_step_succ`：eval_pappAck_step_succ (c : Cod
e) (n) : (pappAck.step c).eval (n + 1) = ((pappAck.step c).eval n).bind c.eval
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `ack_succ_succ`：ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (
ack (m + 1) n)
-/
lemma eval_pappAck (m n) : (pappAck m).eval n = Part.some (ack m n) := by
  induction m, n using ack.induct with
    | case1 n => simp [Code.eval, pappAck]
    | case2 m hm => simp [pappAck, hm]
    | case3 m n hmn₁ hmn₂ => dsimp only [pappAck] at *; simp [hmn₁, hmn₂]

/-- The Ackermann function is computable. -/
/-
**Nat.Partrec.Code._root_.computable** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec.Code
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Ackermann function is computable.
-/
theorem _root_.computable₂_ack : Computable₂ ack := by
  apply _root_.Partrec.of_eq_tot
    (f := fun p : ℕ × ℕ => (pappAck p.1).eval p.2) (g := fun p : ℕ × ℕ => ack p.1 p.2)
  · change Partrec₂ (fun m n => (pappAck m).eval n)
    apply_rules only
      [Code.eval_part.comp₂, Computable.fst, Computable.snd, primrec_pappAck.to_comp.comp]
  · simp

end Nat.Partrec.Code

