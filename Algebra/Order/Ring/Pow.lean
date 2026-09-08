/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.Abel

/-! # Bernoulli's inequality

In this file we prove several versions of Bernoulli's inequality.
Besides the standard version `1 + n * a ≤ (1 + a) ^ n`,
we also prove `a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n`,
which can be regarded as Bernoulli's inequality for `b / a` multiplied by `a ^ n`.

Also, we prove versions for different typeclass assumptions on the (semi)ring.
-/

public section

variable {R : Type*}

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b : R}

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators. -/
/-
**Commute.pow_add_mul_le_add_pow_of_sq_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.pow_add_mul_le_add_pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 
<= a) (Hsq : 0 <= b ^ 2) (Hsq' : 0 <= (a + b) ^ 2) (H : 0 <= 2 * a + b) : forall
 n : Nat, a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n | 0 => by simp | 1 => by si
mp | 2 => calc a ^ 2 + (2 : Nat) * a ^ 1 * b <= a ^ 2 + (2 : Nat) * a ^ 1 * b + 
b ^ 2
参数：Hcomm : Commute a b；ha : 0 <= a；Hsq : 0 <= b ^ 2；Hsq' : 0 <= (a + b) ^ 2；H : 
0 <= 2 * a + b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Bernoulli's inequality for `b / a`, written after multiplication by the denomina
tors.
-/
lemma Commute.pow_add_mul_le_add_pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 ≤ a)
    (Hsq : 0 ≤ b ^ 2) (Hsq' : 0 ≤ (a + b) ^ 2) (H : 0 ≤ 2 * a + b) :
    ∀ n : ℕ, a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n
  | 0 => by simp
  | 1 => by simp
  | 2 =>
    calc
      a ^ 2 + (2 : ℕ) * a ^ 1 * b ≤ a ^ 2 + (2 : ℕ) * a ^ 1 * b + b ^ 2 :=
        le_add_of_nonneg_right Hsq
      _ = (a + b) ^ 2 := by simp [sq, add_mul, mul_add, two_mul, Hcomm.eq, add_assoc]
  | n + 3 => by
    calc
      _ ≤ a ^ (n + 3) + ↑(n + 3) * a ^ (n + 2) * b +
            ((n + 1) * (b ^ 2 * (2 * a + b) * a ^ n) + a ^ (n + 1) * b ^ 2) :=
        le_add_of_nonneg_right <| by
          apply_rules [add_nonneg, mul_nonneg, Nat.cast_nonneg, pow_nonneg, zero_le_one]
      _ = (a + b) ^ 2 * (a ^ (n + 1) + ↑(n + 1) * a ^ n * b) := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ', add_mul, mul_add,
          two_mul, pow_zero, mul_one,
          Hcomm.eq, (n.cast_commute (_ : R)).symm.left_comm, mul_assoc, (Hcomm.pow_left _).eq,
          (Hcomm.pow_left _).left_comm, Hcomm.left_comm, ← @two_add_one_eq_three R, one_mul]
        abel
      _ ≤ (a + b) ^ 2 * (a + b) ^ (n + 1) := by
        gcongr
        apply Commute.pow_add_mul_le_add_pow_of_sq_nonneg <;> assumption
      _ = (a + b) ^ (n + 3) := by simp [pow_succ', mul_assoc]

/-- **Bernoulli's inequality**. This version works for semirings but requires
additional hypotheses `0 ≤ a ^ 2` and `0 ≤ (1 + a) ^ 2`. -/
/-
**one_add_mul_le_pow_of_sq_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_add_mul_le_pow_of_sq_nonneg (Hsq : 0 <= a ^ 2) (Hsq' : 0 <= (1 + a) ^ 
2) (H : 0 <= 2 + a) (n : Nat) : 1 + n * a <= (1 + a) ^ n
参数：Hsq : 0 <= a ^ 2；Hsq' : 0 <= (1 + a) ^ 2；H : 0 <= 2 + a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Commute.pow_add_mul_le_add_pow_of_sq_nonneg`：Commute.pow_add_mul_le_add_
pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 <= a) (Hsq : 0 <= b ^ 2) (Hsq' : 
0 <= (a + b) ^ 2) (H : 0 <= 2 * a…
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
**Bernoulli's inequality**. This version works for semirings but requires
additional hypotheses `0 ≤ a ^ 2` and `0 ≤ (1 + a) ^ 2`.
-/
lemma one_add_mul_le_pow_of_sq_nonneg (Hsq : 0 ≤ a ^ 2) (Hsq' : 0 ≤ (1 + a) ^ 2) (H : 0 ≤ 2 + a)
    (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n

end OrderedSemiring

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators.

This version works for partially ordered commutative semirings,
but explicitly assumes that `b ^ 2` and `(a + b) ^ 2` are nonnegative. -/
/-
**pow_add_mul_le_add_pow_of_sq_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_add_mul_le_add_pow_of_sq_nonneg [CommSemiring R] [PartialOrder R] [IsO
rderedRing R] {a b : R} (ha : 0 <= a) (Hsq : 0 <= b ^ 2) (Hsq' : 0 <= (a + b) ^ 
2) (H : 0 <= 2 * a + b) (n : Nat) : a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n
参数：ha : 0 <= a；Hsq : 0 <= b ^ 2；Hsq' : 0 <= (a + b) ^ 2；H : 0 <= 2 * a + b；n : N
at。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Commute.pow_add_mul_le_add_pow_of_sq_nonneg`：Commute.pow_add_mul_le_add_
pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 <= a) (Hsq : 0 <= b ^ 2) (Hsq' : 
0 <= (a + b) ^ 2) (H : 0 <= 2 * a…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
Bernoulli's inequality for `b / a`, written after multiplication by the denomina
tors.

This version works for partially ordered commutative semirings,
but explicitly assumes that `b ^ 2` and `(a + b) ^ 2` are nonnegative.
-/
lemma pow_add_mul_le_add_pow_of_sq_nonneg [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {a b : R} (ha : 0 ≤ a) (Hsq : 0 ≤ b ^ 2) (Hsq' : 0 ≤ (a + b) ^ 2) (H : 0 ≤ 2 * a + b)
    (n : ℕ) : a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n :=
  (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha Hsq Hsq' H n

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators.

This is a version for a linear ordered semiring. -/
/-
**Commute.pow_add_mul_le_add_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.pow_add_mul_le_add_pow [Semiring R] [LinearOrder R] [IsOrderedRing
 R] [ExistsAddOfLE R] {a b : R} (Hcomm : Commute a b) (ha : 0 <= a) (H : 0 <= 2 
* a + b) (n : Nat) : a ^ n + n * a ^ (n - 1) * b <= (a + b) ^ n
参数：Hcomm : Commute a b；ha : 0 <= a；H : 0 <= 2 * a + b；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Commute.pow_add_mul_le_add_pow_of_sq_nonneg`：Commute.pow_add_mul_le_add_
pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 <= a) (Hsq : 0 <= b ^ 2) (Hsq' : 
0 <= (a + b) ^ 2) (H : 0 <= 2 * a…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R

--- 原说明 ---
Bernoulli's inequality for `b / a`, written after multiplication by the denomina
tors.

This is a version for a linear ordered semiring.
-/
lemma Commute.pow_add_mul_le_add_pow [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a b : R} (Hcomm : Commute a b) (ha : 0 ≤ a) (H : 0 ≤ 2 * a + b)
    (n : ℕ) : a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n :=
  Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg _) (sq_nonneg _) H n

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators.

This is a version for a linear ordered semiring. -/
/-
**pow_add_mul_le_add_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_add_mul_le_add_pow [CommSemiring R] [LinearOrder R] [IsOrderedRing R] 
[ExistsAddOfLE R] {a b : R} (ha : 0 <= a) (H : 0 <= 2 * a + b) (n : Nat) : a ^ n
 + n * a ^ (n - 1) * b <= (a + b) ^ n
参数：ha : 0 <= a；H : 0 <= 2 * a + b；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Commute.pow_add_mul_le_add_pow`：Commute.pow_add_mul_le_add_pow [Semiring
 R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R] {a b : R} (Hcomm : Commu
te a b) (ha : 0 <= a…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
Bernoulli's inequality for `b / a`, written after multiplication by the denomina
tors.

This is a version for a linear ordered semiring.
-/
lemma pow_add_mul_le_add_pow [CommSemiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R]
    {a b : R} (ha : 0 ≤ a) (H : 0 ≤ 2 * a + b) (n : ℕ) :
    a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n :=
  (Commute.all a b).pow_add_mul_le_add_pow ha H n

/-- Bernoulli's inequality for linear ordered semirings. -/
/-
**one_add_le_pow_of_two_add_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_add_le_pow_of_two_add_nonneg [Semiring R] [LinearOrder R] [IsOrderedRi
ng R] [ExistsAddOfLE R] {a : R} (H : 0 <= 2 + a) (n : Nat) : 1 + n * a <= (1 + a
) ^ n
参数：H : 0 <= 2 + a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_add_mul_le_pow_of_sq_nonneg`：one_add_mul_le_pow_of_sq_nonneg (Hsq : 
0 <= a ^ 2) (Hsq' : 0 <= (1 + a) ^ 2) (H : 0 <= 2 + a) (n : Nat) : 1 + n * a <= 
(1 + a) ^ n
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R

--- 原说明 ---
Bernoulli's inequality for linear ordered semirings.
-/
lemma one_add_le_pow_of_two_add_nonneg [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a : R} (H : 0 ≤ 2 + a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow_of_sq_nonneg (sq_nonneg _) (sq_nonneg _) H _

section LinearOrderedRing
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℕ}

/-- **Bernoulli's inequality** for `n : ℕ`, `-2 ≤ a`. -/
/-
**one_add_mul_le_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_add_mul_le_pow (H : -2 <= a) (n : Nat) : 1 + n * a <= (1 + a) ^ n
参数：H : -2 <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_add_le_pow_of_two_add_nonneg`：one_add_le_pow_of_two_add_nonneg [Semi
ring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R] {a : R} (H : 0 <= 2 
+ a) (n : Nat) : 1 + n…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_le_iff_add_nonneg'`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b : α}, -a ≤ b ↔ 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R

--- 原说明 ---
**Bernoulli's inequality** for `n : ℕ`, `-2 ≤ a`.
-/
lemma one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_le_pow_of_two_add_nonneg (neg_le_iff_add_nonneg'.mp H) n

/-- **Bernoulli's inequality** reformulated to estimate `a^n`. -/
/-
**one_add_mul_sub_le_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_add_mul_sub_le_pow (H : -1 <= a) (n : Nat) : 1 + n * (a - 1) <= a ^ n
参数：H : -1 <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sub_le_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a b : α} (c : α), a - c ≤ b - c ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `one_add_mul_le_pow`：one_add_mul_le_pow (H : -2 <= a) (n : Nat) : 1 + n *
 a <= (1 + a) ^ n

--- 原说明 ---
**Bernoulli's inequality** reformulated to estimate `a^n`.
-/
lemma one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + n * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

end LinearOrderedRing

