/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Ring.Commute

/-!
# Cast of natural numbers: lemmas about `Commute`

-/

public section

variable {α : Type*}

namespace Nat

section AddCommute

variable [AddMonoidWithOne α]

/-
**Nat.addCommute_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：addCommute_cast (m n : Nat) : AddCommute (m : α) (n : α)
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `addCommute_iff_eq`：∀ {S : Type u_3} [inst : Add S] (a b : S), AddCommute
 a b ↔ a + b = b + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem addCommute_cast (m n : ℕ) : AddCommute (m : α) (n : α) := by
  rw [addCommute_iff_eq, ← Nat.cast_add, ← Nat.cast_add, m.add_comm]
/-
**Nat.addCommute_cast_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：addCommute_cast_one (n : Nat) : AddCommute (n : α) 1
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.addCommute_cast`：addCommute_cast (m n : Nat) : AddCommute (m : α) (n
 : α)
-/
theorem addCommute_cast_one (n : ℕ) : AddCommute (n : α) 1 :=
  mod_cast addCommute_cast n 1
/-
**Nat.cast_add_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_add_comm (m n : Nat) : (m : α) + n = n + m
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.addCommute_cast`：addCommute_cast (m n : Nat) : AddCommute (m : α) (n
 : α)
-/
theorem cast_add_comm (m n : ℕ) : (m : α) + n = n + m :=
  addCommute_cast m n
/-
**Nat.cast_add_one_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_add_one_comm (n : Nat) : (n : α) + 1 = 1 + n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.addCommute_cast_one`：addCommute_cast_one (n : Nat) : AddCommute (n :
 α) 1
-/
theorem cast_add_one_comm (n : ℕ) : (n : α) + 1 = 1 + n :=
  addCommute_cast_one n

end AddCommute

section NonAssocSemiring

variable [NonAssocSemiring α]

/-
**Nat.cast_commute** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_commute (n : Nat) (x : α) : Commute (n : α) x
参数：n : Nat；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Commute.zero_left`：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Commute.add_left`：add_left [Distrib R] {a b c : R} : Commute a c -> Comm
ute b c -> Commute (a + b) c
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
-/
theorem cast_commute (n : ℕ) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)
/-
**Nat._root_.Commute.ofNat_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.ofNat_left (n : ℕ) [n.AtLeastTwo] (x : α) : Commute (OfNat.ofNat n) x :=
  n.cast_commute x
/-
**Nat.cast_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
参数：n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
-/
theorem cast_comm (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq
/-
**Nat.commute_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：commute_cast (x : α) (n : Nat) : Commute x n
参数：x : α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
-/
theorem commute_cast (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm
/-
**Nat._root_.Commute.ofNat_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.ofNat_right (x : α) (n : ℕ) [n.AtLeastTwo] : Commute x (OfNat.ofNat n) :=
  n.commute_cast x

end NonAssocSemiring
end Nat

namespace SemiconjBy
variable [Semiring α] {a x y : α}

@[simp]
/-
**SemiconjBy.natCast_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `SemiconjBy`。
形式化陈述：natCast_mul_right (h : SemiconjBy a x y) (n : Nat) : SemiconjBy a (n * x) 
(n * y)
参数：h : SemiconjBy a x y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_right`：mul_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x * x') (y * y')
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
-/
lemma natCast_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]
/-
**SemiconjBy.natCast_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `SemiconjBy`。
形式化陈述：natCast_mul_left (h : SemiconjBy a x y) (n : Nat) : SemiconjBy (n * a) x y
参数：h : SemiconjBy a x y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_left`：mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b
 x y) : SemiconjBy (a * b) x z
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
-/
lemma natCast_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h
/-
**SemiconjBy.natCast_mul_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `SemiconjBy`。
形式化陈述：natCast_mul_natCast_mul (h : SemiconjBy a x y) (m n : Nat) : SemiconjBy (m
 * a) (n * x) (n * y)
参数：h : SemiconjBy a x y；m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma natCast_mul_natCast_mul (h : SemiconjBy a x y) (m n : ℕ) :
    SemiconjBy (m * a) (n * x) (n * y) := by
  simp [h]

end SemiconjBy

namespace Commute
variable [Semiring α] {a b : α}

/-
**Commute.natCast_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {a b : α}, Commute a b → ∀ (n : ℕ), C
ommute a (↑n * b)
参数：n : ℕ；↑n * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.natCast_mul_right`：natCast_mul_right (h : SemiconjBy a x y) (
n : Nat) : SemiconjBy a (n * x) (n * y)
-/
@[simp] lemma natCast_mul_right (h : Commute a b) (n : ℕ) : Commute a (n * b) :=
  SemiconjBy.natCast_mul_right h n
/-
**Commute.natCast_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {a b : α}, Commute a b → ∀ (n : ℕ), C
ommute (↑n * a) b
参数：n : ℕ；↑n * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.natCast_mul_left`：natCast_mul_left (h : SemiconjBy a x y) (n 
: Nat) : SemiconjBy (n * a) x y
-/
@[simp] lemma natCast_mul_left (h : Commute a b) (n : ℕ) : Commute (n * a) b :=
  SemiconjBy.natCast_mul_left h n
/-
**Commute.natCast_mul_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：natCast_mul_natCast_mul (h : Commute a b) (m n : Nat) : Commute (m * a) (n
 * b)
参数：h : Commute a b；m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma natCast_mul_natCast_mul (h : Commute a b) (m n : ℕ) : Commute (m * a) (n * b) := by
  simp [h]

variable (a) (m n : ℕ)
/-
**Commute.self_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：self_natCast_mul : Commute a (n * a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.natCast_mul_right`：∀ {α : Type u_1} [inst : Semiring α] {a b : α
}, Commute a b → ∀ (n : ℕ), Commute a (↑n * b)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma self_natCast_mul : Commute a (n * a) := (Commute.refl a).natCast_mul_right n
/-
**Commute.natCast_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：natCast_mul_self : Commute (n * a) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.natCast_mul_left`：∀ {α : Type u_1} [inst : Semiring α] {a b : α}
, Commute a b → ∀ (n : ℕ), Commute (↑n * a) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma natCast_mul_self : Commute (n * a) a := (Commute.refl a).natCast_mul_left n
/-
**Commute.self_natCast_mul_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：self_natCast_mul_natCast_mul : Commute (m * a) (n * a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.natCast_mul_natCast_mul`：natCast_mul_natCast_mul (h : Commute a 
b) (m n : Nat) : Commute (m * a) (n * b)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma self_natCast_mul_natCast_mul : Commute (m * a) (n * a) :=
  (Commute.refl a).natCast_mul_natCast_mul m n

end Commute

