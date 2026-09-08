/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Centers of rings

-/

public section

assert_not_exists RelIso Finset Subsemigroup Field

variable {M : Type*}

namespace Set

variable (M)

@[simp]
/-
**Set.natCast_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：natCast_mem_center [NonAssocSemiring M] (n : Nat) : (n : M) in Set.center 
M where comm _
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem natCast_mem_center [NonAssocSemiring M] (n : ℕ) : (n : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

@[simp]
/-
**Set.ofNat_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofNat_mem_center [NonAssocSemiring M] (n : Nat) [n.AtLeastTwo] : ofNat(n) 
in Set.center M
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.natCast_mem_center`：natCast_mem_center [NonAssocSemiring M] (n : Nat
) : (n : M) in Set.center M where comm _
-/
theorem ofNat_mem_center [NonAssocSemiring M] (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ Set.center M :=
  natCast_mem_center M n

@[simp]
/-
**Set.intCast_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：intCast_mem_center [NonAssocRing M] (n : Int) : (n : M) in Set.center M wh
ere comm _
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `IsMulCentral.left_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulC
entral z → ∀ (b c : M), z * (b * c) = z * b * c
· 使用定理 `Set.natCast_mem_center`：natCast_mem_center [NonAssocSemiring M] (n : Nat
) : (n : M) in Set.center M where comm _
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem intCast_mem_center [NonAssocRing M] (n : ℤ) : (n : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, add_mul, add_mul, add_mul,
        neg_mul, one_mul, neg_mul 1, one_mul, ← neg_mul, add_right_inj, neg_mul,
        (natCast_mem_center _ n).left_assoc _ _, neg_mul, neg_mul]
  right_assoc _ _ := match n with
    | (n : ℕ) => by rw [Int.cast_natCast, (natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add, mul_add, mul_add, mul_neg, mul_one, mul_neg, mul_neg, mul_one, mul_neg,
          add_right_inj, (natCast_mem_center _ n).right_assoc _ _, mul_neg, mul_neg]

variable {M}

@[simp]
/-
**Set.add_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：add_mem_center [Distrib M] {a b : M} (ha : a in Set.center M) (hb : b in S
et.center M) : a + b in Set.center M where comm _
参数：ha : a in Set.center M；hb : b in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `IsMulCentral.left_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulC
entral z → ∀ (b c : M), z * (b * c) = z * b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
-/
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ← add_mul, ← add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ← mul_add, ← mul_add]

@[simp]
/-
**Set.neg_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a in Set.center M) 
: -a in Set.center M where comm _
参数：ha : a in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul_comm`：neg_mul_comm (a b : α) : -a * b = a * -b
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsMulCentral.left_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulC
entral z → ∀ (b c : M), z * (b * c) = z * b * c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
-/
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a ∈ Set.center M) :
    -a ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, ← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]

end Set

