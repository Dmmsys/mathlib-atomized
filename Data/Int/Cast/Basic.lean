/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`).

There is also `Mathlib.Data.Int.Cast.Lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `Mathlib.Data.Int.Cast.Defs` is
`Mathlib.Algebra.Group.Basic`.
-/

public section


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
/-
**Nat.cast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]

@[simp, norm_cast]
/-
**Nat.cast_pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u} [inst : AddGroupWithOne R] {n : ℕ}, 0 < n → ↑(n - 1) = ↑n -
 1
参数：n - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
  | n + 1, _ => by rw [cast_succ, add_sub_cancel_right, Nat.add_sub_cancel_right]

end Nat

open Nat

namespace Int

variable {R : Type u}

@[simp, norm_cast]
/-
**Int.cast_ite** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) : ((ite P m n : 
Int) : R) = ite P (m : R) (n : R)
参数：P : Prop；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : ℤ) :
    ((ite P m n : ℤ) : R) = ite P (m : R) (n : R) :=
  apply_ite _ _ _ _

variable [AddGroupWithOne R]

-- TODO: I don't like that `norm_cast` is used here, because it results in `norm_cast`
-- introducing the "implementation detail" `Int.negSucc`.
@[simp, norm_cast squash]
/-
**Int.cast_negSucc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
-/
theorem cast_negSucc (n : ℕ) : (-[n+1] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.intCast_negSucc n

@[simp, norm_cast]
/-
**Int.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_zero : ((0 : Int) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero

-- This lemma competes with `Int.ofNat_eq_natCast` to come later
@[simp high, norm_cast]
/-
**Int.cast_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_natCast (n : Nat) : ((n : Int) : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
-/
theorem cast_natCast (n : ℕ) : ((n : ℤ) : R) = n :=
  AddGroupWithOne.intCast_ofNat _

@[simp, norm_cast]
/-
**Int.cast_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) : R) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
-/
theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℤ) : R) = ofNat(n) := by
  simpa only [OfNat.ofNat] using! AddGroupWithOne.intCast_ofNat (R := R) n

@[simp, norm_cast]
/-
**Int.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_one : ((1 : Int) : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_one`：↑1 = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem cast_one : ((1 : ℤ) : R) = 1 := by
  rw [← Int.natCast_one, cast_natCast, Nat.cast_one]

@[simp, norm_cast]
/-
**Int.cast_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) = -↑n
参数：n : ℤ；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.neg_ofNat_succ`：∀ (n : ℕ), -↑n.succ = Int.negSucc n
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.neg_negSucc`：∀ (n : ℕ), -Int.negSucc n = ↑(n + 1)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by simp
  | (n + 1 : ℕ) => by rw [cast_natCast, neg_ofNat_succ]; simp
  | -[n+1] => by rw [Int.neg_negSucc, cast_natCast]; simp

@[simp, norm_cast]
/-
**Int.cast_subNatNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_subNatNat (m n) : ((Int.subNatNat m n : Int) : R) = m - n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.le_of_sub_eq_zero`：∀ {n m : ℕ}, n - m = 0 → n ≤ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold subNatNat
  cases e : n - m
  · simp [Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]

@[simp]
/-
**Int.cast_negOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = -n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_negOfNat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [Int.cast_neg, negOfNat_eq]

@[simp, norm_cast]
/-
**Int.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m + n) = ↑m + ↑n
参数：m n : ℤ；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.ofNat_add_negSucc`：∀ (m n : ℕ), ↑m + Int.negSucc n = Int.subNatNat m
 n.succ
· 使用定理 `Int.cast_subNatNat`：cast_subNatNat (m n) : ((Int.subNatNat m n : Int) : 
R) = m - n
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Int.negSucc_add_ofNat`：∀ (m n : ℕ), Int.negSucc m + ↑n = Int.subNatNat n
 m.succ
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_neg_add_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G},
 a = -b + c ↔ b + a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Int.negSucc_add_negSucc`：∀ (m n : ℕ), Int.negSucc m + Int.negSucc n = In
t.negSucc (m + n).succ
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
-/
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← Int.natCast_add]
  | (m : ℕ), -[n+1] => by
    rw [Int.ofNat_add_negSucc, cast_subNatNat, cast_natCast, cast_negSucc, sub_eq_add_neg]
  | -[m+1], (n : ℕ) => by
    rw [Int.negSucc_add_ofNat, cast_subNatNat, cast_natCast, cast_negSucc, sub_eq_iff_eq_add,
      add_assoc, eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] => by
    rw [Int.negSucc_add_negSucc, succ_eq_add_one, cast_negSucc, cast_negSucc, cast_negSucc,
      ← neg_add_rev, ← Nat.cast_add, Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]

@[simp, norm_cast]
/-
**Int.cast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_sub (m n) : ((m - n : Int) : R) = m - n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]
/-
**Int.cast_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_two : ((2 : Int) : R) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cast_two : ((2 : ℤ) : R) = 2 := cast_ofNat _
/-
**Int.cast_three** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_three : ((3 : Int) : R) = 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cast_three : ((3 : ℤ) : R) = 3 := cast_ofNat _
/-
**Int.cast_four** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_four : ((4 : Int) : R) = 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cast_four : ((4 : ℤ) : R) = 4 := cast_ofNat _

end Int

section zsmul

variable {R : Type*}

/-
**zsmul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = ↑n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
-/
@[simp] lemma zsmul_one [AddGroupWithOne R] (n : ℤ) : n • (1 : R) = n := by cases n <;> simp

end zsmul

