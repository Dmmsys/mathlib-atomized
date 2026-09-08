/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Integer powers of square matrices

In this file, we define integer power of matrices, relying on
the nonsingular inverse definition for negative powers.

## Implementation details

The main definition is a direct recursive call on the integer inductive type,
as provided by the `DivInvMonoid.Pow` default implementation.
The lemma names are taken from `Algebra.GroupWithZero.Power`.

## Tags

matrix inverse, matrix powers
-/

public section


open Matrix

namespace Matrix

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

local notation "M" => Matrix n' n' R
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DivInvMonoid (Matrix n' n' R) where
  __ : Monoid M := inferInstance
  __ : Inv M := inferInstance

section NatPow

@[simp]
/-
**Matrix.inv_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
参数：A : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Matrix.mul_inv_rev`：mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ *
 A⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem inv_pow' (A : M) (n : ℕ) : A⁻¹ ^ n = (A ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']
/-
**Matrix.pow_sub'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：pow_sub' (A : M) {m n : Nat} (ha : IsUnit A.det) (h : n <= m) : A ^ (m - n
) = A ^ m * (A ^ n)⁻¹
参数：A : M；ha : IsUnit A.det；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `Matrix.det_pow`：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det
 M ^ n
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
-/
theorem pow_sub' (A : M) {m n : ℕ} (ha : IsUnit A.det) (h : n ≤ m) :
    A ^ (m - n) = A ^ m * (A ^ n)⁻¹ := by
  rw [← tsub_add_cancel_of_le h, pow_add, Matrix.mul_assoc, mul_nonsing_inv,
    tsub_add_cancel_of_le h, Matrix.mul_one]
  simpa using ha.pow n
/-
**Matrix.pow_inv_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：pow_inv_comm' (A : M) (m n : Nat) : A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m
参数：A : M；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.inv_pow'`：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.nonsing_inv_cancel_or_zero`：nonsing_inv_cancel_or_zero : A⁻¹ * A 
= 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem pow_inv_comm' (A : M) (m n : ℕ) : A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m := by
  induction n generalizing m with
  | zero => simp
  | succ n IH =>
    rcases m with m | m
    · simp
    rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h
    · calc
        A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
          simp only [pow_succ A⁻¹, pow_succ' A, Matrix.mul_assoc]
        _ = A ^ n * A⁻¹ ^ m := by simp only [h, Matrix.mul_one, IH m]
        _ = A ^ n * (A * A⁻¹) * A⁻¹ ^ m := by simp only [h', Matrix.mul_one]
        _ = A ^ (n + 1) * A⁻¹ ^ (m + 1) := by
          simp only [pow_succ A, pow_succ' A⁻¹, Matrix.mul_assoc]
    · simp [h]

end NatPow

section ZPow

open Int

@[simp]
/-
**Matrix.one_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R] (n : ℤ), 1 ^ n = 1
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem one_zpow : ∀ n : ℤ, (1 : M) ^ n = 1
  | (n : ℕ) => by rw [zpow_natCast, one_pow]
  | -[n+1] => by rw [zpow_negSucc, one_pow, inv_one]
/-
**Matrix.zero_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R] (z : ℤ),   z ≠ 0 → 0 ^ z = 0
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Matrix.inv_zero`：inv_zero : (0 : Matrix n n α)⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : M) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_natCast, zero_pow]
    exact mod_cast h
  | -[n+1], _ => by simp [zero_pow n.succ_ne_zero]
/-
**Matrix.zero_zpow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_zpow_eq (n : Int) : (0 : M) ^ n = if n = 0 then 1 else 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Matrix.zero_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fi
ntype n'] {R : Type u_2} [inst_2 : CommRing R] (z : ℤ),   z ≠ 0 → 0 ^ z = 0
-/
theorem zero_zpow_eq (n : ℤ) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]
/-
**Matrix.inv_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : ℤ), A⁻¹ ^ n = (A ^ n)⁻¹
参数：A : Matrix n' n' R；n : ℤ；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Matrix.inv_pow'`：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
theorem inv_zpow (A : M) : ∀ n : ℤ, A⁻¹ ^ n = (A ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, inv_pow']
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, inv_pow']

@[simp]
/-
**Matrix.zpow_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_neg_one (A : M) : A ^ (-1 : Int) = A⁻¹
参数：A : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
-/
theorem zpow_neg_one (A : M) : A ^ (-1 : ℤ) = A⁻¹ := by
  simpa using DivInvMonoid.zpow_neg' 0 A

@[simp]
/-
**Matrix.zpow_neg_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : Int) = (A ^ n)⁻¹
参数：A : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
-/
theorem zpow_neg_natCast (A : M) (n : ℕ) : A ^ (-n : ℤ) = (A ^ n)⁻¹ := by
  cases n
  · simp
  · exact DivInvMonoid.zpow_neg' _ _
/-
**Matrix._root_.IsUnit.det_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.det_zpow {A : M} (h : IsUnit A.det) (n : ℤ) : IsUnit (A ^ n).det := by
  rcases n with n | n
  · simpa using h.pow n
  · simpa using h.pow n.succ
/-
**Matrix.isUnit_det_zpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_det_zpow_iff {A : M} {z : Int} : IsUnit (A ^ z).det ↔ IsUnit A.det 
∨ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Matrix.det_pow`：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det
 M ^ n
· 使用引理 `isUnit_pow_succ_iff`：isUnit_pow_succ_iff : IsUnit (a ^ (n + 1)) ↔ IsUnit
 a
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `Matrix.zpow_neg_natCast`：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : 
Int) = (A ^ n)⁻¹
· 使用定理 `Matrix.isUnit_nonsing_inv_det_iff`：isUnit_nonsing_inv_det_iff {A : Matri
x n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
-/
theorem isUnit_det_zpow_iff {A : M} {z : ℤ} : IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0 := by
  induction z with
  | zero => simp
  | succ z =>
    rw [← Int.natCast_succ, zpow_natCast, det_pow, isUnit_pow_succ_iff, ← Int.ofNat_zero,
      Int.ofNat_inj]
    simp
  | pred z =>
    rw [← neg_add', ← Int.natCast_succ, zpow_neg_natCast, isUnit_nonsing_inv_det_iff, det_pow,
      isUnit_pow_succ_iff, neg_eq_zero, ← Int.ofNat_zero, Int.ofNat_inj]
    simp
/-
**Matrix.zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.det → ∀ (n : ℤ), A ^
 (-n) = (A ^ n)⁻¹
参数：n : ℤ；-n；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.zpow_neg_natCast`：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : 
Int) = (A ^ n)⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Int.neg_negSucc`：∀ (n : ℕ), -Int.negSucc n = ↑(n + 1)
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Matrix.nonsing_inv_nonsing_inv`：nonsing_inv_nonsing_inv (h : IsUnit A.de
t) : A⁻¹⁻¹ = A
· 使用定理 `Matrix.det_pow`：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det
 M ^ n
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
-/
theorem zpow_neg {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (-n) = (A ^ n)⁻¹
  | (n : ℕ) => zpow_neg_natCast _ _
  | -[n+1] => by
    rw [zpow_negSucc, neg_negSucc, zpow_natCast, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _
/-
**Matrix.inv_zpow'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：inv_zpow' {A : M} (h : IsUnit A.det) (n : Int) : A⁻¹ ^ n = A ^ (-n)
参数：h : IsUnit A.det；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zpow_neg`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
· 使用定理 `Matrix.inv_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : ℤ), A⁻
¹ ^ n…
-/
theorem inv_zpow' {A : M} (h : IsUnit A.det) (n : ℤ) : A⁻¹ ^ n = A ^ (-n) := by
  rw [zpow_neg h, inv_zpow]
/-
**Matrix.zpow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_add_one {A : M} (h : IsUnit A.det) : forall n : Int, A ^ (n + 1) = A 
^ n * A | (n : Nat) => by simp only [← Nat.cast_succ, pow_succ, zpow_natCast] | 
-[n+1] => calc A ^ (-(n + 1) + 1 : Int) = (A ^ n)⁻¹
参数：h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `Matrix.zpow_neg`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
· 使用定理 `Matrix.mul_inv_rev`：mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ *
 A⁻¹
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem zpow_add_one {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (n + 1) = A ^ n * A
  | (n : ℕ) => by simp only [← Nat.cast_succ, pow_succ, zpow_natCast]
  | -[n+1] =>
    calc
      A ^ (-(n + 1) + 1 : ℤ) = (A ^ n)⁻¹ := by
        rw [neg_add, neg_add_cancel_right, zpow_neg h, zpow_natCast]
      _ = (A * A ^ n)⁻¹ * A := by
        rw [mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]
      _ = A ^ (-(n + 1 : ℤ)) * A := by
        rw [zpow_neg h, ← Int.natCast_succ, zpow_natCast, pow_succ']
/-
**Matrix.zpow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_sub_one {A : M} (h : IsUnit A.det) (n : Int) : A ^ (n - 1) = A ^ n * 
A⁻¹
参数：h : IsUnit A.det；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Matrix.mul_nonsing_inv`：mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.zpow_add_one`：zpow_add_one {A : M} (h : IsUnit A.det) : forall n 
: Int, A ^ (n + 1) = A ^ n * A | (n : Nat) => by simp only [← Nat.cast_succ, pow
_succ, zp…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem zpow_sub_one {A : M} (h : IsUnit A.det) (n : ℤ) : A ^ (n - 1) = A ^ n * A⁻¹ :=
  calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc, mul_nonsing_inv _ h, mul_one]
    _ = A ^ n * A⁻¹ := by rw [← zpow_add_one h, sub_add_cancel]
/-
**Matrix.zpow_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_add {A : M} (ha : IsUnit A.det) (m n : Int) : A ^ (m + n) = A ^ m * A
 ^ n
参数：ha : IsUnit A.det；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.zpow_add_one`：zpow_add_one {A : M} (h : IsUnit A.det) : forall n 
: Int, A ^ (n + 1) = A ^ n * A | (n : Nat) => by simp only [← Nat.cast_succ, pow
_succ, zp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Matrix.zpow_sub_one`：zpow_sub_one {A : M} (h : IsUnit A.det) (n : Int) :
 A ^ (n - 1) = A ^ n * A⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
-/
theorem zpow_add {A : M} (ha : IsUnit A.det) (m n : ℤ) : A ^ (m + n) = A ^ m * A ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← add_assoc, zpow_add_one ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]
/-
**Matrix.zpow_add_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_add_of_nonpos {A : M} {m n : Int} (hm : m <= 0) (hn : n <= 0) : A ^ (
m + n) = A ^ m * A ^ n
参数：hm : m <= 0；hn : n <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_cancel_or_zero`：nonsing_inv_cancel_or_zero : A⁻¹ * A 
= 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
· 使用定理 `Matrix.zpow_add`：zpow_add {A : M} (ha : IsUnit A.det) (m n : Int) : A ^ 
(m + n) = A ^ m * A ^ n
· 使用定理 `Matrix.isUnit_det_of_left_inverse`：isUnit_det_of_left_inverse (h : B * A
 = 1) : IsUnit A.det
· 使用定理 `Int.exists_eq_neg_ofNat`：∀ {a : ℤ}, a ≤ 0 → ∃ n, a = -↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.zpow_neg_natCast`：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : 
Int) = (A ^ n)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zpow_add_of_nonpos {A : M} {m n : ℤ} (hm : m ≤ 0) (hn : n ≤ 0) :
    A ^ (m + n) = A ^ m * A ^ n := by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
  · exact zpow_add (isUnit_det_of_left_inverse h) m n
  · obtain ⟨k, rfl⟩ := exists_eq_neg_ofNat hm
    obtain ⟨l, rfl⟩ := exists_eq_neg_ofNat hn
    simp_rw [← neg_add, ← Int.natCast_add, zpow_neg_natCast, ← inv_pow', h, pow_add]
/-
**Matrix.zpow_add_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_add_of_nonneg {A : M} {m n : Int} (hm : 0 <= m) (hn : 0 <= n) : A ^ (
m + n) = A ^ m * A ^ n
参数：hm : 0 <= m；hn : 0 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
-/
theorem zpow_add_of_nonneg {A : M} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    A ^ (m + n) = A ^ m * A ^ n := by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  rw [← Int.natCast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
/-
**Matrix.zpow_one_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_one_add {A : M} (h : IsUnit A.det) (i : Int) : A ^ (1 + i) = A * A ^ 
i
参数：h : IsUnit A.det；i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zpow_add`：zpow_add {A : M} (ha : IsUnit A.det) (m n : Int) : A ^ 
(m + n) = A ^ m * A ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
-/
theorem zpow_one_add {A : M} (h : IsUnit A.det) (i : ℤ) : A ^ (1 + i) = A * A ^ i := by
  rw [zpow_add h, zpow_one]
/-
**Matrix.SemiconjBy.zpow_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SemiconjBy`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A X Y : Matrix n' n' R}, IsUnit X.det → IsUnit Y.d
et → SemiconjBy A X Y → ∀ (m : ℤ), SemiconjBy A (X ^ m) (Y ^ m)
参数：m : ℤ；X ^ m；Y ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
· 使用定理 `Matrix.det_pow`：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det
 M ^ n
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Matrix.nonsing_inv_apply`：nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (
↑h.unit⁻¹ : α) • A.adjugate
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Matrix.isRegular_of_isLeftRegular_det`：isRegular_of_isLeftRegular_det {A
 : Matrix n n α} (hA : IsLeftRegular A.det) : IsRegular A
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
-/
theorem SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det)
    (h : SemiconjBy A X Y) : ∀ m : ℤ, SemiconjBy A (X ^ m) (Y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
  | -[n+1] => by
    have hx' : IsUnit (X ^ n.succ).det := by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_negSucc, zpow_negSucc, nonsing_inv_apply _ hx', nonsing_inv_apply _ hy', SemiconjBy]
    refine (isRegular_of_isLeftRegular_det hy'.isRegular.left).left ?_
    dsimp only
    rw [← mul_assoc, ← (h.pow_right n.succ).eq, mul_assoc, Matrix.mul_smul,
      mul_adjugate, ← Matrix.mul_assoc, Matrix.mul_smul (Y ^ _) (↑hy'.unit⁻¹ : R),
      mul_adjugate, smul_smul, smul_smul, hx'.val_inv_mul,
      hy'.val_inv_mul, one_smul, Matrix.mul_one, Matrix.one_mul]
/-
**Matrix.Commute.zpow_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}, Commute A B → ∀ (m : ℤ), Co
mmute A (B ^ m)
参数：m : ℤ；B ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.nonsing_inv_cancel_or_zero`：nonsing_inv_cancel_or_zero : A⁻¹ * A 
= 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
· 使用定理 `Matrix.SemiconjBy.zpow_right`：∀ {n' : Type u_1} [inst : DecidableEq n'] 
[inst_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A X Y : Matrix n' 
n' R}, IsUnit X.de…
· 使用定理 `Matrix.isUnit_det_of_left_inverse`：isUnit_det_of_left_inverse (h : B * A
 = 1) : IsUnit A.det
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Commute.zpow_right {A B : M} (h : Commute A B) (m : ℤ) : Commute A (B ^ m) := by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, _⟩ | hB)
  · refine SemiconjBy.zpow_right ?_ ?_ h _ <;> exact isUnit_det_of_left_inverse hB
  · cases m
    · simpa using h.pow_right _
    · simp [← inv_pow', hB]
/-
**Matrix.Commute.zpow_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}, Commute A B → ∀ (m : ℤ), Co
mmute (A ^ m) B
参数：m : ℤ；A ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Matrix.Commute.zpow_right`：∀ {n' : Type u_1} [inst : DecidableEq n'] [in
st_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}
, Commute A B →…
-/
theorem Commute.zpow_left {A B : M} (h : Commute A B) (m : ℤ) : Commute (A ^ m) B :=
  (Commute.zpow_right h.symm m).symm
/-
**Matrix.Commute.zpow_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}, Commute A B → ∀ (m n : ℤ), 
Commute (A ^ m) (B ^ n)
参数：m n : ℤ；A ^ m；B ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Commute.zpow_right`：∀ {n' : Type u_1} [inst : DecidableEq n'] [in
st_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}
, Commute A B →…
· 使用定理 `Matrix.Commute.zpow_left`：∀ {n' : Type u_1} [inst : DecidableEq n'] [ins
t_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R},
 Commute A B →…
-/
theorem Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : ℤ) : Commute (A ^ m) (B ^ n) :=
  Commute.zpow_right (Commute.zpow_left h _) _
/-
**Matrix.Commute.zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : ℤ), Commute (A ^ n) A
参数：A : Matrix n' n' R；n : ℤ；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Commute.zpow_left`：∀ {n' : Type u_1} [inst : DecidableEq n'] [ins
t_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R},
 Commute A B →…
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem Commute.zpow_self (A : M) (n : ℤ) : Commute (A ^ n) A :=
  Commute.zpow_left (Commute.refl A) _
/-
**Matrix.Commute.self_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : ℤ), Commute A (A ^ n)
参数：A : Matrix n' n' R；n : ℤ；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Commute.zpow_right`：∀ {n' : Type u_1} [inst : DecidableEq n'] [in
st_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}
, Commute A B →…
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem Commute.self_zpow (A : M) (n : ℤ) : Commute A (A ^ n) :=
  Commute.zpow_right (Commute.refl A) _
/-
**Matrix.Commute.zpow_zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (m n : ℤ), Commute (A ^ m) (A 
^ n)
参数：A : Matrix n' n' R；m n : ℤ；A ^ m；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Commute.zpow_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [ins
t_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R},
 Commute A B →…
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem Commute.zpow_zpow_self (A : M) (m n : ℤ) : Commute (A ^ m) (A ^ n) :=
  Commute.zpow_zpow (Commute.refl A) _ _
/-
**Matrix.zpow_add_one_of_ne_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R} (n : ℤ), n ≠ -1 → A ^ (n + 1) 
= A ^ n * A
参数：n : ℤ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.nonsing_inv_cancel_or_zero`：nonsing_inv_cancel_or_zero : A⁻¹ * A 
= 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0
· 使用定理 `Matrix.zpow_add_one`：zpow_add_one {A : M} (h : IsUnit A.det) : forall n 
: Int, A ^ (n + 1) = A ^ n * A | (n : Nat) => by simp only [← Nat.cast_succ, pow
_succ, zp…
· 使用定理 `Matrix.isUnit_det_of_left_inverse`：isUnit_det_of_left_inverse (h : B * A
 = 1) : IsUnit A.det
· 使用定理 `Matrix.zpow_neg_natCast`：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : 
Int) = (A ^ n)⁻¹
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem zpow_add_one_of_ne_neg_one {A : M} : ∀ n : ℤ, n ≠ -1 → A ^ (n + 1) = A ^ n * A
  | (n : ℕ), _ => by simp only [pow_succ, ← Nat.cast_succ, zpow_natCast]
  | -1, h => absurd rfl h
  | -((n : ℕ) + 2), _ => by
    rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
    · apply zpow_add_one (isUnit_det_of_left_inverse h)
    · change A ^ (-((n + 1 : ℕ) : ℤ)) = A ^ (-((n + 2 : ℕ) : ℤ)) * A
      simp_rw [zpow_neg_natCast, ← inv_pow', h, zero_pow <| Nat.succ_ne_zero _, zero_mul]
/-
**Matrix.zpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R), IsUnit A.det → ∀ (m n : ℤ), A
 ^ (m * n) = (A ^ m) ^ n
参数：A : Matrix n' n' R；m n : ℤ；m * n；A ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Int.ofNat_mul_negSucc`：∀ (m n : ℕ), ↑m * Int.negSucc n = -↑(m * n.succ)
· 使用定理 `Matrix.zpow_neg_natCast`：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : 
Int) = (A ^ n)⁻¹
· 使用定理 `Matrix.inv_pow'`：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
· 使用定理 `Int.negSucc_mul_ofNat`：∀ (m n : ℕ), Int.negSucc m * ↑n = -↑(m.succ * n)
· 使用定理 `Int.negSucc_mul_negSucc`：∀ (m n : ℕ), Int.negSucc m * Int.negSucc n = ↑m
.succ * ↑n.succ
· 使用定理 `Matrix.nonsing_inv_nonsing_inv`：nonsing_inv_nonsing_inv (h : IsUnit A.de
t) : A⁻¹⁻¹ = A
· 使用定理 `Matrix.det_pow`：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det
 M ^ n
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
-/
theorem zpow_mul (A : M) (h : IsUnit A.det) : ∀ m n : ℤ, A ^ (m * n) = (A ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_natCast, zpow_natCast, ← pow_mul, ← zpow_natCast, Int.natCast_mul]
  | (m : ℕ), -[n+1] => by
    rw [zpow_natCast, zpow_negSucc, ← pow_mul, ofNat_mul_negSucc, zpow_neg_natCast]
  | -[m+1], (n : ℕ) => by
    rw [zpow_natCast, zpow_negSucc, ← inv_pow', ← pow_mul, negSucc_mul_ofNat, zpow_neg_natCast,
        inv_pow']
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, negSucc_mul_negSucc, ← Int.natCast_mul, zpow_natCast, inv_pow',
      ← pow_mul, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _
/-
**Matrix.zpow_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_mul' (A : M) (h : IsUnit A.det) (m n : Int) : A ^ (m * n) = (A ^ n) ^
 m
参数：A : M；h : IsUnit A.det；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Matrix.zpow_mul`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R), IsUnit A.d
et → …
-/
theorem zpow_mul' (A : M) (h : IsUnit A.det) (m n : ℤ) : A ^ (m * n) = (A ^ n) ^ m := by
  rw [mul_comm, zpow_mul _ h]


@[simp, norm_cast]
/-
**Matrix.coe_units_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (u : (Matrix n' n' R)ˣ) (n : ℤ), ↑(u ^ n) = ↑u ^ n
参数：u : (Matrix n' n' R)ˣ；n : ℤ；u ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Matrix.inv_pow'`：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
-/
theorem coe_units_zpow (u : Mˣ) : ∀ n : ℤ, ((u ^ n : Mˣ) : M) = (u : M) ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
  | -[k+1] => by
    rw [zpow_negSucc, zpow_negSucc, ← inv_pow, u⁻¹.val_pow_eq_pow_val, ← inv_pow', coe_units_inv]
/-
**Matrix.zpow_ne_zero_of_isUnit_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_ne_zero_of_isUnit_det [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUn
it A.det) (z : Int) : A ^ z != 0
参数：ha : IsUnit A.det；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.det_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_zero`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] [Nonempty n],   Matrix.det 0 = 0
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
-/
theorem zpow_ne_zero_of_isUnit_det [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det)
    (z : ℤ) : A ^ z ≠ 0 := by
  have := ha.det_zpow z
  contrapose this
  rw [this, det_zero]
  exact not_isUnit_zero
/-
**Matrix.zpow_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_sub {A : M} (ha : IsUnit A.det) (z1 z2 : Int) : A ^ (z1 - z2) = A ^ z
1 / A ^ z2
参数：ha : IsUnit A.det；z1 z2 : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.zpow_add`：zpow_add {A : M} (ha : IsUnit A.det) (m n : Int) : A ^ 
(m + n) = A ^ m * A ^ n
· 使用定理 `Matrix.zpow_neg`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem zpow_sub {A : M} (ha : IsUnit A.det) (z1 z2 : ℤ) : A ^ (z1 - z2) = A ^ z1 / A ^ z2 := by
  rw [sub_eq_add_neg, zpow_add ha, zpow_neg ha, div_eq_mul_inv]
/-
**Matrix.Commute.mul_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Commute`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A B : Matrix n' n' R}, Commute A B → ∀ (i : ℤ), (A
 * B) ^ i = A ^ i * B ^ i
参数：i : ℤ；A * B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_inv_rev`：mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ *
 A⁻¹
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
-/
theorem Commute.mul_zpow {A B : M} (h : Commute A B) : ∀ i : ℤ, (A * B) ^ i = A ^ i * B ^ i
  | (n : ℕ) => by simp [h.mul_pow n]
  | -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, zpow_negSucc, ← mul_inv_rev,
      h.mul_pow n.succ, (h.pow_pow _ _).eq]
/-
**Matrix.zpow_neg_mul_zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zpow_neg_mul_zpow_self (n : Int) {A : M} (h : IsUnit A.det) : A ^ (-n) * A
 ^ n = 1
参数：n : Int；h : IsUnit A.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zpow_neg`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `IsUnit.det_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
-/
theorem zpow_neg_mul_zpow_self (n : ℤ) {A : M} (h : IsUnit A.det) : A ^ (-n) * A ^ n = 1 := by
  rw [zpow_neg h, nonsing_inv_mul _ (h.det_zpow _)]
/-
**Matrix.one_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_div_pow {A : M} (n : Nat) : (1 / A) ^ n = 1 / A ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Matrix.inv_pow'`：inv_pow' (A : M) (n : Nat) : A⁻¹ ^ n = (A ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_pow {A : M} (n : ℕ) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_pow']
/-
**Matrix.one_div_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_div_zpow {A : M} (n : Int) : (1 / A) ^ n = 1 / A ^ n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Matrix.inv_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : ℤ), A⁻
¹ ^ n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_div_zpow {A : M} (n : ℤ) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_zpow]

@[simp]
/-
**Matrix.transpose_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : ℤ), (A ^ n).transpose = A
.transpose ^ n
参数：A : Matrix n' n' R；n : ℤ；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Matrix.transpose_pow`：transpose_pow [CommSemiring α] [Fintype m] [Decida
bleEq m] (M : Matrix m m α) (k : Nat) : (M ^ k)ᵀ = Mᵀ ^ k
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Matrix.transpose_nonsing_inv`：transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹
-/
theorem transpose_zpow (A : M) : ∀ n : ℤ, (A ^ n)ᵀ = Aᵀ ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, transpose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, transpose_nonsing_inv, transpose_pow]

@[simp]
/-
**Matrix.conjTranspose_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   [inst_3 : StarRing R] (A : Matrix n' n' R) (n : ℤ),
 (A ^ n).conjTranspose = A.conjTranspose ^ n
参数：A : Matrix n' n' R；n : ℤ；A ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Matrix.conjTranspose_pow`：conjTranspose_pow [Semiring α] [StarRing α] [F
intype m] [DecidableEq m] (M : Matrix m m α) (k : Nat) : (M ^ k)ᴴ = Mᴴ ^ k
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Matrix.conjTranspose_nonsing_inv`：conjTranspose_nonsing_inv [StarRing α]
 : A⁻¹ᴴ = Aᴴ⁻¹
-/
theorem conjTranspose_zpow [StarRing R] (A : M) : ∀ n : ℤ, (A ^ n)ᴴ = Aᴴ ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, conjTranspose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, conjTranspose_nonsing_inv, conjTranspose_pow]
/-
**Matrix.IsSymm.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fintype n'] {R : Type 
u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, A.IsSymm → ∀ (k : ℤ), (A ^ k)
.IsSymm
参数：k : ℤ；A ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Matrix.transpose_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1
 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   (A : Matrix n' n' R) (n : 
ℤ), (A ^ n)…
-/
theorem IsSymm.zpow {A : M} (h : A.IsSymm) (k : ℤ) :
    (A ^ k).IsSymm := by
  rw [IsSymm, transpose_zpow, h]

end ZPow

end Matrix

