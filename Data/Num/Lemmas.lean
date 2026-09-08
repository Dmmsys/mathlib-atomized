/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.PSub
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Num.Bitwise
import all Init.Data.Nat.Bitwise.Basic  -- for unfolding `bitwise`

/-!
# Properties of the binary representation of integers
-/

@[expose] public section

open Int

attribute [local simp] add_assoc

namespace PosNum

variable {α : Type*}

@[simp, norm_cast]
/-
**PosNum.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1 :=
  rfl

@[simp]
/-
**PosNum.cast_one'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_one' [One α] [Add α] : (PosNum.one : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_one' [One α] [Add α] : (PosNum.one : α) = 1 :=
  rfl

@[simp, norm_cast]
/-
**PosNum.cast_bit0** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) = (n : α) + n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) = (n : α) + n :=
  rfl

@[simp, norm_cast]
/-
**PosNum.cast_bit1** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) = ((n : α) + n) + 1
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) = ((n : α) + n) + 1 :=
  rfl

@[simp, norm_cast]
/-
**PosNum.cast_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : PosNum), ↑↑n = ↑n
参数：n : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_to_nat [AddMonoidWithOne α] : ∀ n : PosNum, ((n : ℕ) : α) = n
  | 1 => Nat.cast_one
  | bit0 p => by dsimp; rw [Nat.cast_add, p.cast_to_nat]
  | bit1 p => by dsimp; rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, p.cast_to_nat]

@[norm_cast]
/-
**PosNum.to_nat_to_int** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
-/
theorem to_nat_to_int (n : PosNum) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _

@[simp, norm_cast]
/-
**PosNum.cast_to_int** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n : Int) : α) = n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.to_nat_to_int`：to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
-/
theorem cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_natCast, cast_to_nat]
/-
**PosNum.succ_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : PosNum), ↑n.succ = ↑n + 1
参数：n : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_to_nat : ∀ n, (succ n : ℕ) = n + 1
  | 1 => rfl
  | bit0 _ => rfl
  | bit1 p =>
    (congr_arg (fun n ↦ n + n) (succ_to_nat p)).trans <|
      show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1 by simp [add_left_comm]
/-
**PosNum.one_add** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：one_add (n : PosNum) : 1 + n = succ n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem one_add (n : PosNum) : 1 + n = succ n := by cases n <;> rfl
/-
**PosNum.add_one** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：add_one (n : PosNum) : n + 1 = succ n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_one (n : PosNum) : n + 1 = succ n := by cases n <;> rfl

@[norm_cast]
/-
**PosNum.add_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (m n : PosNum), ↑(m + n) = ↑m + ↑n
参数：m n : PosNum；m + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_to_nat : ∀ m n, ((m + n : PosNum) : ℕ) = m + n
  | 1, b => by rw [one_add b, succ_to_nat, add_comm, cast_one]
  | a, 1 => by rw [add_one a, succ_to_nat, cast_one]
  | bit0 a, bit0 b => (congr_arg (fun n ↦ n + n) (add_to_nat a b)).trans <| add_add_add_comm _ _ _ _
  | bit0 a, bit1 b =>
    (congr_arg (fun n ↦ (n + n) + 1) (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + (b + b + 1) by simp [add_left_comm]
  | bit1 a, bit0 b =>
    (congr_arg (fun n ↦ (n + n) + 1) (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + 1 + (b + b) by simp [add_comm, add_left_comm]
  | bit1 a, bit1 b =>
    show (succ (a + b) + succ (a + b) : ℕ) = a + a + 1 + (b + b + 1) by
      rw [succ_to_nat, add_to_nat a b]; simp [add_left_comm]
/-
**PosNum.add_succ** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (m n : PosNum), m + n.succ = (m + n).succ
参数：m n : PosNum；m + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_succ : ∀ m n : PosNum, m + succ n = succ (m + n)
  | 1, b => by simp [one_add]
  | bit0 a, 1 => congr_arg bit0 (add_one a)
  | bit1 a, 1 => congr_arg bit1 (add_one a)
  | bit0 _, bit0 _ => rfl
  | bit0 a, bit1 b => congr_arg bit0 (add_succ a b)
  | bit1 _, bit0 _ => rfl
  | bit1 a, bit1 b => congr_arg bit1 (add_succ a b)
/-
**PosNum.bit0_of_bit0** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : PosNum), n + n = n.bit0
参数：n : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit0_of_bit0 : ∀ n, n + n = bit0 n
  | 1 => rfl
  | bit0 p => congr_arg bit0 (bit0_of_bit0 p)
  | bit1 p => show bit0 (succ (p + p)) = _ by rw [bit0_of_bit0 p, succ]
/-
**PosNum.bit1_of_bit1** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：bit1_of_bit1 (n : PosNum) : (n + n) + 1 = bit1 n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.add_one`：add_one (n : PosNum) : n + 1 = succ n
· 使用定理 `PosNum.bit0_of_bit0`：∀ (n : PosNum), n + n = n.bit0
· 使用定理 `PosNum.succ.eq_3`：∀ (n : PosNum), n.bit0.succ = n.bit1
-/
theorem bit1_of_bit1 (n : PosNum) : (n + n) + 1 = bit1 n :=
  show (n + n) + 1 = bit1 n by rw [add_one, bit0_of_bit0, succ]

@[norm_cast]
/-
**PosNum.mul_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (m n : PosNum), ↑(m * n) = ↑m * ↑n
参数：m n : PosNum；m * n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_to_nat (m) : ∀ n, ((m * n : PosNum) : ℕ) = m * n
  | 1 => (mul_one _).symm
  | bit0 p => show (↑(m * p) + ↑(m * p) : ℕ) = ↑m * (p + p) by rw [mul_to_nat m p, left_distrib]
  | bit1 p =>
    (add_to_nat (bit0 (m * p)) m).trans <|
      show (↑(m * p) + ↑(m * p) + ↑m : ℕ) = ↑m * (p + p) + m by rw [mul_to_nat m p, left_distrib]
/-
**PosNum.to_nat_pos** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：to_nat_pos : forall n : PosNum, 0 < (n : Nat) | 1 => Nat.zero_lt_one | bit
0 p => let h
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_nat_pos : ∀ n : PosNum, 0 < (n : ℕ)
  | 1 => Nat.zero_lt_one
  | bit0 p =>
    let h := to_nat_pos p
    add_pos h h
  | bit1 _p => Nat.succ_pos _
/-
**PosNum.cmp_to_nat_lemma** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cmp_to_nat_lemma {m n : PosNum} : (m : Nat) < n -> (bit1 m : Nat) < bit0 n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
-/
theorem cmp_to_nat_lemma {m n : PosNum} : (m : ℕ) < n → (bit1 m : ℕ) < bit0 n :=
  show (m : ℕ) < n → (m + m + 1 + 1 : ℕ) ≤ n + n by
    intro h; rw [Nat.add_right_comm m m 1, add_assoc]; exact Nat.add_le_add h h
/-
**PosNum.cmp_swap** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cmp_swap (m) : forall n, (cmp m n).swap = cmp n m
参数：m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.cmp.eq_def`：∀ (x x_1 : PosNum),   x.cmp x_1 =     match x, x_1 wi
th     | PosNum.one, PosNum.one => Ordering.eq     | x, PosNum.one => Ordering.g
t     |…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cmp_swap (m) : ∀ n, (cmp m n).swap = cmp n m := by
  induction m with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    intro n <;> obtain - | n | n := n <;> unfold cmp <;>
      try { rfl } <;> rw [← IH] <;> cases cmp m n <;> rfl
/-
**PosNum.cmp_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) ((m : Nat) < n) (m = 
n) ((n : Nat) < m) : Prop) | 1, 1 => rfl | bit0 a, 1 => let h : (1 : Nat) <= a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 1, 1 => rfl
  | bit0 a, 1 =>
    let h : (1 : ℕ) ≤ a := to_nat_pos a
    Nat.add_le_add h h
  | bit1 a, 1 => Nat.succ_lt_succ <| to_nat_pos <| bit0 a
  | 1, bit0 b =>
    let h : (1 : ℕ) ≤ b := to_nat_pos b
    Nat.add_le_add h h
  | 1, bit1 b => Nat.succ_lt_succ <| to_nat_pos <| bit0 b
  | bit0 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.add_lt_add this this
    · rw [this]
    · exact Nat.add_lt_add this this
  | bit0 a, bit1 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.le_succ_of_le (Nat.add_lt_add this this)
    · rw [this]
      apply Nat.lt_succ_self
    · exact cmp_to_nat_lemma this
  | bit1 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact cmp_to_nat_lemma this
    · rw [this]
      apply Nat.lt_succ_self
    · exact Nat.le_succ_of_le (Nat.add_lt_add this this)
  | bit1 a, bit1 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.succ_lt_succ (Nat.add_lt_add this this)
    · rw [this]
    · exact Nat.succ_lt_succ (Nat.add_lt_add this this)

@[norm_cast]
/-
**PosNum.lt_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：lt_to_nat {m n : PosNum} : (m : Nat) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.cmp_to_nat`：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) 
((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop) | 1, 1 => rfl | bit0 a, 1 => let
 h : (1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem lt_to_nat {m n : PosNum} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]
/-
**PosNum.le_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：le_to_nat {m n : PosNum} : (m : Nat) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `PosNum.lt_to_nat`：lt_to_nat {m n : PosNum} : (m : Nat) < n ↔ m < n
-/
theorem le_to_nat {m n : PosNum} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_nat

end PosNum

namespace Num

variable {α : Type*}

open PosNum

/-
**Num.add_zero** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：add_zero (n : Num) : n + 0 = n
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_zero (n : Num) : n + 0 = n := by cases n <;> rfl
/-
**Num.zero_add** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：zero_add (n : Num) : 0 + n = n
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zero_add (n : Num) : 0 + n = n := by cases n <;> rfl
/-
**Num.add_one** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n + 1 = n.succ
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_one : ∀ n : Num, n + 1 = succ n
  | 0 => rfl
  | pos p => by cases p <;> rfl
/-
**Num.add_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (m n : Num), m + n.succ = (m + n).succ
参数：m n : Num；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.zero_add`：zero_add (n : Num) : 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PosNum.add_one`：add_one (n : PosNum) : n + 1 = succ n
· 使用定理 `Num.add_zero`：add_zero (n : Num) : n + 0 = n
· 使用定理 `Num.succ.eq_1`：∀ (n : Num), n.succ = Num.pos n.succ'
· 使用定理 `Num.succ'.eq_2`：∀ (p : PosNum), (Num.pos p).succ' = p.succ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.add_succ`：∀ (m n : PosNum), m + n.succ = (m + n).succ
-/
theorem add_succ : ∀ m n : Num, m + succ n = succ (m + n)
  | 0, n => by simp [zero_add]
  | pos p, 0 => show pos (p + 1) = succ (pos p + 0) by rw [PosNum.add_one, add_zero, succ, succ']
  | pos _, pos _ => congr_arg pos (PosNum.add_succ _ _)
/-
**Num.bit0_of_bit0** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n + n = n.bit0
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.bit0_of_bit0`：∀ (n : PosNum), n + n = n.bit0
-/
theorem bit0_of_bit0 : ∀ n : Num, n + n = n.bit0
  | 0 => rfl
  | pos p => congr_arg pos p.bit0_of_bit0
/-
**Num.bit1_of_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n + n + 1 = n.bit1
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PosNum.bit1_of_bit1`：bit1_of_bit1 (n : PosNum) : (n + n) + 1 = bit1 n
-/
theorem bit1_of_bit1 : ∀ n : Num, (n + n) + 1 = n.bit1
  | 0 => rfl
  | pos p => congr_arg pos p.bit1_of_bit1

@[simp]
/-
**Num.ofNat'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：Num.ofNat' 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofNat'_zero : Num.ofNat' 0 = 0 := by simp [Num.ofNat']
/-
**Num.ofNat'_bit** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (b : Bool) (n : ℕ), Num.ofNat' (Nat.bit b n) = (bif b then Num.bit1 else
 Num.bit0) (Num.ofNat' n)
参数：b : Bool；n : ℕ；Nat.bit b n；bif b then Num.bit1 else Num.bit0；Num.ofNat' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
-/
theorem ofNat'_bit (b n) : ofNat' (Nat.bit b n) = cond b Num.bit1 Num.bit0 (ofNat' n) :=
  Nat.binaryRec_eq _ _ (.inl rfl)

@[simp]
/-
**Num.ofNat'_one** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：Num.ofNat' 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofNat'_one : Num.ofNat' 1 = 1 := by simp [Num.ofNat', Num.bit1]
/-
**Num.bit1_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), n.bit1.succ = n.succ.bit0
参数：n : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bit1_succ : ∀ n : Num, n.bit1.succ = n.succ.bit0
  | 0 => rfl
  | pos _n => rfl
/-
**Num.ofNat'_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {n : ℕ}, Num.ofNat' (n + 1) = Num.ofNat' n + 1
参数：n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Num.ofNat'_one`：Num.ofNat' 1 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `Num.zero_add`：zero_add (n : Num) : 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Num.ofNat'_bit`：∀ (b : Bool) (n : ℕ), Num.ofNat' (Nat.bit b n) = (bif b 
then Num.bit1 else Num.bit0) (Num.ofNat' n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Num.add_one`：∀ (n : Num), n + 1 = n.succ
· 使用定理 `Num.bit1_succ`：∀ (n : Num), n.bit1.succ = n.succ.bit0
-/
theorem ofNat'_succ : ∀ {n}, ofNat' (n + 1) = ofNat' n + 1 :=
  @(Nat.binaryRec (by simp [zero_add]) fun b n ih => by
    cases b
    · erw [ofNat'_bit true n, ofNat'_bit]
      simp only [← bit1_of_bit1, ← bit0_of_bit0, cond]
    · rw [show n.bit true + 1 = (n + 1).bit false by simp [Nat.bit, mul_add],
        ofNat'_bit, ofNat'_bit, ih]
      simp only [cond, add_one, bit1_succ])

@[simp]
/-
**Num.add_ofNat'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：add_ofNat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `Num.add_zero`：add_zero (n : Num) : n + 0 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Num.ofNat'_succ`：∀ {n : ℕ}, Num.ofNat' (n + 1) = Num.ofNat' n + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Num.add_one`：∀ (n : Num), n + 1 = n.succ
· 使用定理 `Num.add_succ`：∀ (m n : Num), m + n.succ = (m + n).succ
-/
theorem add_ofNat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n := by
  induction n
  · simp only [Nat.add_zero, ofNat'_zero, add_zero]
  · simp only [Nat.add_succ, Nat.add_zero, ofNat'_succ, add_one, add_succ, *]

@[simp, norm_cast]
/-
**Num.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0 :=
  rfl

@[simp]
/-
**Num.cast_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_zero' [Zero α] [One α] [Add α] : (Num.zero : α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_zero' [Zero α] [One α] [Add α] : (Num.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Num.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_one [Zero α] [One α] [Add α] : ((1 : Num) : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_one [Zero α] [One α] [Add α] : ((1 : Num) : α) = 1 :=
  rfl

@[simp]
/-
**Num.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos n : α) = n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos n : α) = n :=
  rfl
/-
**Num.succ'_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), ↑n.succ' = ↑n + 1
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `PosNum.succ_to_nat`：∀ (n : PosNum), ↑n.succ = ↑n + 1
-/
theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n + 1
  | 0 => (Nat.zero_add _).symm
  | pos _p => PosNum.succ_to_nat _
/-
**Num.succ_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：succ_to_nat (n) : (succ n : Nat) = n + 1
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
-/
theorem succ_to_nat (n) : (succ n : ℕ) = n + 1 :=
  succ'_to_nat n

@[simp, norm_cast]
/-
**Num.cast_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num), ↑↑n = ↑n
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
-/
theorem cast_to_nat [AddMonoidWithOne α] : ∀ n : Num, ((n : ℕ) : α) = n
  | 0 => Nat.cast_zero
  | pos p => p.cast_to_nat

@[norm_cast]
/-
**Num.add_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (m n : Num), ↑(m + n) = ↑m + ↑n
参数：m n : Num；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `PosNum.add_to_nat`：∀ (m n : PosNum), ↑(m + n) = ↑m + ↑n
-/
theorem add_to_nat : ∀ m n, ((m + n : Num) : ℕ) = m + n
  | 0, 0 => rfl
  | 0, pos _q => (Nat.zero_add _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.add_to_nat _ _

@[norm_cast]
/-
**Num.mul_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (m n : Num), ↑(m * n) = ↑m * ↑n
参数：m n : Num；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `PosNum.mul_to_nat`：∀ (m n : PosNum), ↑(m * n) = ↑m * ↑n
-/
theorem mul_to_nat : ∀ m n, ((m * n : Num) : ℕ) = m * n
  | 0, 0 => rfl
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.mul_to_nat _ _
/-
**Num.cmp_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) ((m : Nat) < n) (m = 
n) ((n : Nat) < m) : Prop) | 0, 0 => rfl | 0, pos _ => to_nat_pos _ | pos _, 0 =
> to_nat_pos _ | pos a, pos b => by have
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.to_nat_pos`：to_nat_pos : forall n : PosNum, 0 < (n : Nat) | 1 => 
Nat.zero_lt_one | bit0 p => let h
· 使用定理 `PosNum.cmp_to_nat`：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) 
((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop) | 1, 1 => rfl | bit0 a, 1 => let
 h : (1…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 0, 0 => rfl
  | 0, pos _ => to_nat_pos _
  | pos _, 0 => to_nat_pos _
  | pos a, pos b => by
    have := PosNum.cmp_to_nat a b; revert this; dsimp [cmp]; cases PosNum.cmp a b
    exacts [id, congr_arg pos, id]

@[norm_cast]
/-
**Num.lt_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：lt_to_nat {m n : Num} : (m : Nat) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.cmp_to_nat`：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) ((m
 : Nat) < n) (m = n) ((n : Nat) < m) : Prop) | 0, 0 => rfl | 0, pos _ => to_nat_
pos …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem lt_to_nat {m n : Num} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]
/-
**Num.le_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：le_to_nat {m n : Num} : (m : Nat) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Num.lt_to_nat`：lt_to_nat {m n : Num} : (m : Nat) < n ↔ m < n
-/
theorem le_to_nat {m n : Num} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_nat

end Num

namespace PosNum

@[simp]
/-
**PosNum.of_to_nat'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : PosNum), Num.ofNat' ↑n = Num.pos n
参数：n : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_to_nat' : ∀ n : PosNum, Num.ofNat' (n : ℕ) = Num.pos n
  | 1 => by
      simp only [cast_one, Num.ofNat'_one]
      norm_cast
  | bit0 p => by
      simpa only [Nat.bit_false, cond_false, two_mul, of_to_nat' p] using! Num.ofNat'_bit false p
  | bit1 p => by
      simpa only [Nat.bit_true, cond_true, two_mul, of_to_nat' p] using! Num.ofNat'_bit true p

end PosNum

namespace Num

@[simp, norm_cast]
/-
**Num.of_to_nat'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), Num.ofNat' ↑n = n
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `PosNum.of_to_nat'`：∀ (n : PosNum), Num.ofNat' ↑n = Num.pos n
-/
theorem of_to_nat' : ∀ n : Num, Num.ofNat' (n : ℕ) = n
  | 0 => ofNat'_zero
  | pos p => p.of_to_nat'
/-
**Num.toNat_injective** 是 Mathlib 中的一个引理，位于命名空间 `Num`。
形式化陈述：toNat_injective : Function.Injective (castNum : Num -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Num.of_to_nat'`：∀ (n : Num), Num.ofNat' ↑n = n
-/
lemma toNat_injective : Function.Injective (castNum : Num → ℕ) :=
  Function.LeftInverse.injective of_to_nat'

@[norm_cast]
/-
**Num.to_nat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：to_nat_inj {m n : Num} : (m : Nat) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Num.toNat_injective`：toNat_injective : Function.Injective (castNum : Num
 -> Nat)
-/
theorem to_nat_inj {m n : Num} : (m : ℕ) = n ↔ m = n := toNat_injective.eq_iff

/-- This tactic tries to turn an (in)equality about `Num`s to one about `Nat`s by rewriting.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `Num`s by transferring them to the `Nat` world and
then trying to call `simp`.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp))

/-
**Num.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：addMonoid : AddMonoid Num where zero_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.zero_add`：zero_add (n : Num) : 0 + n = n
· 使用定理 `Num.add_zero`：add_zero (n : Num) : n + 0 = n
-/
instance addMonoid : AddMonoid Num where
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := by transfer
  nsmul := nsmulRec
/-
**Num.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：addMonoidWithOne : AddMonoidWithOne Num
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `Num.ofNat'_succ`：∀ {n : ℕ}, Num.ofNat' (n + 1) = Num.ofNat' n + 1
-/
instance addMonoidWithOne : AddMonoidWithOne Num :=
  { Num.addMonoid with
    natCast := Num.ofNat'
    natCast_zero := ofNat'_zero
    natCast_succ := fun _ => ofNat'_succ }
/-
**Num.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：commSemiring : CommSemiring Num where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
instance commSemiring : CommSemiring Num where
  __ := Num.addMonoid
  __ := Num.addMonoidWithOne
  npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩
  mul_zero _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, mul_zero]
  zero_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, zero_mul]
  mul_one _ := by rw [← to_nat_inj, mul_to_nat, cast_one, mul_one]
  one_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_one, one_mul]
  add_comm _ _ := by simp_rw [← to_nat_inj, add_to_nat, add_comm]
  mul_comm _ _ := by simp_rw [← to_nat_inj, mul_to_nat, mul_comm]
  mul_assoc _ _ _ := by simp_rw [← to_nat_inj, mul_to_nat, mul_assoc]
  left_distrib _ _ _ := by simp only [← to_nat_inj, mul_to_nat, add_to_nat, mul_add]
  right_distrib _ _ _ := by simp only [← to_nat_inj, mul_to_nat, add_to_nat, add_mul]
/-
**Num.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：partialOrder : PartialOrder Num where lt_iff_le_not_ge a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder Num where
  lt_iff_le_not_ge a b := by simp only [← lt_to_nat, ← le_to_nat, lt_iff_le_not_ge]
  le_refl := by transfer
  le_trans a b c := by transfer_rw; apply le_trans
  le_antisymm a b := by transfer_rw; apply le_antisymm
/-
**Num.isOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Num where add_le_add_l
eft a b h c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.le_to_nat`：le_to_nat {m n : Num} : (m : Nat) <= n ↔ m <= n
· 使用定理 `Num.add_to_nat`：∀ (m n : Num), ↑(m + n) = ↑m + ↑n
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
instance isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Num where
  add_le_add_left a b h c := by revert h; transfer_rw; exact fun h => add_le_add_left h c
  le_of_add_le_add_left a b c := by transfer_rw; apply le_of_add_le_add_left
/-
**Num.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：linearOrder : LinearOrder Num
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder : LinearOrder Num :=
  { le_total := by
      intro a b
      transfer_rw
      apply le_total
    toDecidableLT := Num.decidableLT
    toDecidableLE := Num.decidableLE
    -- This is relying on an automatically generated instance name,
    -- generated in a `deriving` handler.
    -- See https://github.com/leanprover/lean4/issues/2343
    toDecidableEq := instDecidableEqNum }
/-
**Num.isStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Num`。
形式化陈述：isStrictOrderedRing : IsStrictOrderedRing Num where zero_le_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.lt_to_nat`：lt_to_nat {m n : Num} : (m : Nat) < n ↔ m < n
· 使用定理 `Num.mul_to_nat`：∀ (m n : Num), ↑(m * n) = ↑m * ↑n
· 使用定理 `Num.cast_zero`：cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
instance isStrictOrderedRing : IsStrictOrderedRing Num where
  zero_le_one := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_lt_mul_of_pos_left a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_right

@[norm_cast]
/-
**Num.add_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：add_of_nat (m n) : ((m + n : Nat) : Num) = m + n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.add_ofNat'`：add_ofNat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + N
um.ofNat' n
-/
theorem add_of_nat (m n) : ((m + n : ℕ) : Num) = m + n :=
  add_ofNat' _ _

@[norm_cast]
/-
**Num.to_nat_to_int** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：to_nat_to_int (n : Num) : ((n : Nat) : Int) = n
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
-/
theorem to_nat_to_int (n : Num) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _

@[simp, norm_cast]
/-
**Num.cast_to_int** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_to_int {α} [AddGroupWithOne α] (n : Num) : ((n : Int) : α) = n
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.to_nat_to_int`：to_nat_to_int (n : Num) : ((n : Nat) : Int) = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
-/
theorem cast_to_int {α} [AddGroupWithOne α] (n : Num) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_natCast, cast_to_nat]
/-
**Num.to_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ℕ), ↑↑n = n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_of_nat : ∀ n : ℕ, ((n : Num) : ℕ) = n
  | 0 => by rw [Nat.cast_zero, cast_zero]
  | n + 1 => by rw [Nat.cast_succ, add_one, succ_to_nat, to_of_nat n]

@[simp, norm_cast]
/-
**Num.of_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：of_natCast {α} [AddMonoidWithOne α] (n : Nat) : ((n : Num) : α) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
· 使用定理 `Num.to_of_nat`：∀ (n : ℕ), ↑↑n = n
-/
theorem of_natCast {α} [AddMonoidWithOne α] (n : ℕ) : ((n : Num) : α) = n := by
  rw [← cast_to_nat, to_of_nat]

@[norm_cast]
/-
**Num.of_nat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：of_nat_inj {m n : Nat} : (m : Num) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Num.to_of_nat`：∀ (n : ℕ), ↑↑n = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem of_nat_inj {m n : ℕ} : (m : Num) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩

-- The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
/-
**Num.of_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：of_to_nat : forall n : Num, ((n : Nat) : Num) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.of_to_nat'`：∀ (n : Num), Num.ofNat' ↑n = n
-/
theorem of_to_nat : ∀ n : Num, ((n : ℕ) : Num) = n :=
  of_to_nat'

@[norm_cast]
/-
**Num.dvd_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：dvd_to_nat (m n : Num) : (m : Nat) ∣ n ↔ m ∣ n
参数：m n : Num。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.of_to_nat`：of_to_nat : forall n : Num, ((n : Nat) : Num) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Num.mul_to_nat`：∀ (m n : Num), ↑(m * n) = ↑m * ↑n
-/
theorem dvd_to_nat (m n : Num) : (m : ℕ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_nat n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e, mul_to_nat]⟩⟩

end Num

namespace PosNum

variable {α : Type*}

open Num

-- The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
/-
**PosNum.of_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：of_to_nat : forall n : PosNum, ((n : Nat) : Num) = Num.pos n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.of_to_nat'`：∀ (n : PosNum), Num.ofNat' ↑n = Num.pos n
-/
theorem of_to_nat : ∀ n : PosNum, ((n : ℕ) : Num) = Num.pos n :=
  of_to_nat'

@[norm_cast]
/-
**PosNum.to_nat_inj** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：to_nat_inj {m n : PosNum} : (m : Nat) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.pos.inj`：∀ {a a_1 : PosNum}, Num.pos a = Num.pos a_1 → a = a_1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.of_to_nat`：of_to_nat : forall n : PosNum, ((n : Nat) : Num) = Num
.pos n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem to_nat_inj {m n : PosNum} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h => Num.pos.inj <| by rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h], congr_arg _⟩
/-
**PosNum.pred'_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : PosNum), ↑n.pred' = (↑n).pred
参数：n : PosNum；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
-/
theorem pred'_to_nat : ∀ n, (pred' n : ℕ) = Nat.pred n
  | 1 => rfl
  | bit0 n =>
    have : Nat.succ ↑(pred' n) = ↑n := by
      rw [pred'_to_nat n, Nat.succ_pred_eq_of_pos (to_nat_pos n)]
    match (motive :=
        ∀ k : Num, Nat.succ ↑k = ↑n → ↑(Num.casesOn k 1 bit1 : PosNum) = Nat.pred (n + n))
      pred' n, this with
    | 0, (h : ((1 : Num) : ℕ) = n) => by rw [← to_nat_inj.1 h]; rfl
    | Num.pos p, (h : Nat.succ ↑p = n) => by rw [← h]; exact (Nat.succ_add p p).symm
  | bit1 _ => rfl

@[simp]
/-
**PosNum.pred'_succ'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : Num), n.succ'.pred' = n
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Num.to_nat_inj`：to_nat_inj {m n : Num} : (m : Nat) = n ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.pred'_to_nat`：∀ (n : PosNum), ↑n.pred' = (↑n).pred
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `Nat.add_one`：∀ (n : ℕ), n + 1 = n.succ
· 使用定理 `Nat.pred_succ`：∀ (n : ℕ), n.succ.pred = n
-/
theorem pred'_succ' (n) : pred' (succ' n) = n :=
  Num.to_nat_inj.1 <| by rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]
/-
**PosNum.succ'_pred'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : PosNum), n.pred'.succ' = n
参数：n : PosNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `PosNum.to_nat_inj`：to_nat_inj {m n : PosNum} : (m : Nat) = n ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `PosNum.pred'_to_nat`：∀ (n : PosNum), ↑n.pred' = (↑n).pred
· 使用定理 `Nat.add_one`：∀ (n : ℕ), n + 1 = n.succ
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `PosNum.to_nat_pos`：to_nat_pos : forall n : PosNum, 0 < (n : Nat) | 1 => 
Nat.zero_lt_one | bit0 p => let h
-/
theorem succ'_pred' (n) : succ' (pred' n) = n :=
  to_nat_inj.1 <| by
    rw [succ'_to_nat, pred'_to_nat, Nat.add_one, Nat.succ_pred_eq_of_pos (to_nat_pos _)]
/-
**PosNum.dvd** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
形式化陈述：dvd : Dvd PosNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance dvd : Dvd PosNum :=
  ⟨fun m n => pos m ∣ pos n⟩

@[norm_cast]
/-
**PosNum.dvd_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：dvd_to_nat {m n : PosNum} : (m : Nat) ∣ n ↔ m ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.dvd_to_nat`：dvd_to_nat (m n : Num) : (m : Nat) ∣ n ↔ m ∣ n
-/
theorem dvd_to_nat {m n : PosNum} : (m : ℕ) ∣ n ↔ m ∣ n :=
  Num.dvd_to_nat (pos m) (pos n)
/-
**PosNum.size_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：size_to_nat : forall n, (size n : Nat) = Nat.size n | 1 => Nat.size_one.sy
mm | bit0 n => by rw [size]; rw [succ_to_nat]; rw [size_to_nat n]; rw [cast_bit0
]; rw [← two_mul]; rw [← Nat.bit_false_apply]; rw [Nat.size_bit] have
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 1 => Nat.size_one.symm
  | bit0 n => by
      rw [size, succ_to_nat, size_to_nat n, cast_bit0, ← two_mul, ← Nat.bit_false_apply,
        Nat.size_bit]
      have := to_nat_pos n
      dsimp [Nat.bit]; lia
  | bit1 n => by
      rw [size, succ_to_nat, size_to_nat n, cast_bit1, ← two_mul, ← Nat.bit_true_apply,
        Nat.size_bit]
      dsimp [Nat.bit]; lia
/-
**PosNum.size_eq_natSize** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (n : PosNum), ↑n.size = n.natSize
参数：n : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem size_eq_natSize : ∀ n, (size n : ℕ) = natSize n
  | 1 => rfl
  | bit0 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]
  | bit1 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]
/-
**PosNum.natSize_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：natSize_to_nat (n) : natSize n = Nat.size n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.size_eq_natSize`：∀ (n : PosNum), ↑n.size = n.natSize
· 使用定理 `PosNum.size_to_nat`：size_to_nat : forall n, (size n : Nat) = Nat.size n 
| 1 => Nat.size_one.symm | bit0 n => by rw [size]; rw [succ_to_nat]; rw [size_to
_nat n];…
-/
theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]
/-
**PosNum.natSize_pos** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：natSize_pos (n) : 0 < natSize n
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem natSize_pos (n) : 0 < natSize n := by cases n <;> apply Nat.succ_pos

/-- This tactic tries to turn an (in)equality about `PosNum`s to one about `Nat`s by rewriting.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `PosNum`s by transferring them to the `Nat` world
and then trying to call `simp`.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

/-
**PosNum.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
形式化陈述：addCommSemigroup : AddCommSemigroup PosNum where add_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup : AddCommSemigroup PosNum where
  add_assoc := by transfer
  add_comm := by transfer
/-
**PosNum.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
形式化陈述：commMonoid : CommMonoid PosNum where npow
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid : CommMonoid PosNum where
  npow := @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩
  mul_assoc := by transfer
  one_mul := by transfer
  mul_one := by transfer
  mul_comm := by transfer
/-
**PosNum.distrib** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
形式化陈述：distrib : Distrib PosNum where left_distrib
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distrib : Distrib PosNum where
  left_distrib := by transfer; simp [mul_add]
  right_distrib := by transfer; simp [mul_add, mul_comm]
/-
**PosNum.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `PosNum`。
形式化陈述：linearOrder : LinearOrder PosNum where lt_iff_le_not_ge
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder : LinearOrder PosNum where
  lt_iff_le_not_ge := by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le_refl := by transfer
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    transfer_rw
    apply le_antisymm
  le_total := by
    intro a b
    transfer_rw
    apply le_total
  toDecidableLT := by infer_instance
  toDecidableLE := by infer_instance
  toDecidableEq := by infer_instance

@[simp]
/-
**PosNum.cast_to_num** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_to_num (n : PosNum) : ↑n = Num.pos n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `PosNum.of_to_nat`：of_to_nat : forall n : PosNum, ((n : Nat) : Num) = Num
.pos n
-/
theorem cast_to_num (n : PosNum) : ↑n = Num.pos n := by rw [← cast_to_nat, ← of_to_nat n]

@[simp, norm_cast]
/-
**PosNum.bit_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：bit_to_nat (b n) : (bit b n : Nat) = Nat.bit b n
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by cases b <;> simp [bit, two_mul]

@[simp, norm_cast]
/-
**PosNum.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum) : α) = m + n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `PosNum.add_to_nat`：∀ (m n : PosNum), ↑(m + n) = ↑m + ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]

@[simp 500, norm_cast]
/-
**PosNum.cast_succ** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n : α) = n + 1
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.add_one`：add_one (n : PosNum) : n + 1 = succ n
· 使用定理 `PosNum.cast_add`：cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum)
 : α) = m + n
· 使用定理 `PosNum.cast_one`：cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1
-/
theorem cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]

@[simp, norm_cast]
/-
**PosNum.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_inj [AddMonoidWithOne α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ 
m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `PosNum.to_nat_inj`：to_nat_inj {m n : PosNum} : (m : Nat) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_inj [AddMonoidWithOne α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]

@[simp]
/-
**PosNum.one_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：one_le_cast [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : Pos
Num) : (1 : α) <= n
参数：n : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `PosNum.to_nat_pos`：to_nat_pos : forall n : PosNum, 0 < (n : Nat) | 1 => 
Nat.zero_lt_one | bit0 p => let h
-/
theorem one_le_cast [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum) :
    (1 : α) ≤ n := by
  rw [← cast_to_nat, ← Nat.cast_one, Nat.cast_le (α := α)]; apply to_nat_pos

@[simp]
/-
**PosNum.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_pos [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum
) : 0 < (n : α)
参数：n : PosNum。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `PosNum.one_le_cast`：one_le_cast [Semiring α] [PartialOrder α] [IsStrictO
rderedRing α] (n : PosNum) : (1 : α) <= n
-/
theorem cast_pos [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum) : 0 < (n : α) :=
  lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp, norm_cast]
/-
**PosNum.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_mul [NonAssocSemiring α] (m n) : ((m * n : PosNum) : α) = m * n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `PosNum.mul_to_nat`：∀ (m n : PosNum), ↑(m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem cast_mul [NonAssocSemiring α] (m n) : ((m * n : PosNum) : α) = m * n := by
  rw [← cast_to_nat, mul_to_nat, Nat.cast_mul, cast_to_nat, cast_to_nat]

@[simp]
/-
**PosNum.cmp_eq** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n
参数：m n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.cmp_to_nat`：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) 
((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop) | 1, 1 => rfl | bit0 a, 1 => let
 h : (1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]
/-
**PosNum.cast_lt** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : PosNu
m} : (m : α) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `PosNum.lt_to_nat`：lt_to_nat {m n : PosNum} : (m : Nat) < n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : PosNum} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt (α := α), lt_to_nat]

@[simp, norm_cast]
/-
**PosNum.cast_le** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : PosNum
} : (m : α) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `PosNum.cast_lt`：cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRi
ng α] {m n : PosNum} : (m : α) < n ↔ m < n
-/
theorem cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : PosNum} :
    (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt

end PosNum

namespace Num

variable {α : Type*}

open PosNum

/-
**Num.bit_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：bit_to_nat (b n) : (bit b n : Nat) = Nat.bit b n
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by
  cases b <;> cases n <;> simp [bit, two_mul] <;> rfl
/-
**Num.cast_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_succ' [AddMonoidWithOne α] (n) : (succ' n : α) = n + 1
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Po
sNum), ↑↑n = ↑n
· 使用定理 `Num.succ'_to_nat`：∀ (n : Num), ↑n.succ' = ↑n + 1
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
-/
theorem cast_succ' [AddMonoidWithOne α] (n) : (succ' n : α) = n + 1 := by
  rw [← PosNum.cast_to_nat, succ'_to_nat, Nat.cast_add_one, cast_to_nat]
/-
**Num.cast_succ** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_succ [AddMonoidWithOne α] (n) : (succ n : α) = n + 1
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.cast_succ'`：cast_succ' [AddMonoidWithOne α] (n) : (succ' n : α) = n 
+ 1
-/
theorem cast_succ [AddMonoidWithOne α] (n) : (succ n : α) = n + 1 :=
  cast_succ' n

@[simp, norm_cast]
/-
**Num.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_add [AddMonoidWithOne α] (m n) : ((m + n : Num) : α) = m + n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
· 使用定理 `Num.add_to_nat`：∀ (m n : Num), ↑(m + n) = ↑m + ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : Num) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]

@[simp, norm_cast]
/-
**Num.cast_bit0** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) = 2 * (n : α)
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.bit0_of_bit0`：∀ (n : Num), n + n = n.bit0
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Num.cast_add`：cast_add [AddMonoidWithOne α] (m n) : ((m + n : Num) : α) 
= m + n
-/
theorem cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) = 2 * (n : α) := by
  rw [← bit0_of_bit0, two_mul, cast_add]

@[simp, norm_cast]
/-
**Num.cast_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_bit1 [NonAssocSemiring α] (n : Num) : (n.bit1 : α) = 2 * (n : α) + 1
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.bit1_of_bit1`：∀ (n : Num), n + n + 1 = n.bit1
· 使用定理 `Num.bit0_of_bit0`：∀ (n : Num), n + n = n.bit0
· 使用定理 `Num.cast_add`：cast_add [AddMonoidWithOne α] (m n) : ((m + n : Num) : α) 
= m + n
· 使用定理 `Num.cast_bit0`：cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) =
 2 * (n : α)
-/
theorem cast_bit1 [NonAssocSemiring α] (n : Num) : (n.bit1 : α) = 2 * (n : α) + 1 := by
  rw [← bit1_of_bit1, bit0_of_bit0, cast_add, cast_bit0]; rfl

@[simp, norm_cast]
/-
**Num.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : Num), ↑(m * n) = ↑m * 
↑n
参数：m n : Num；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PosNum.cast_mul`：cast_mul [NonAssocSemiring α] (m n) : ((m * n : PosNum)
 : α) = m * n
-/
theorem cast_mul [NonAssocSemiring α] : ∀ m n, ((m * n : Num) : α) = m * n
  | 0, 0 => (zero_mul _).symm
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => (mul_zero _).symm
  | pos _p, pos _q => PosNum.cast_mul _ _
/-
**Num.size_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), ↑n.size = (↑n).size
参数：n : Num；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.size_zero`：size_zero : size 0 = 0
· 使用定理 `PosNum.size_to_nat`：size_to_nat : forall n, (size n : Nat) = Nat.size n 
| 1 => Nat.size_one.symm | bit0 n => by rw [size]; rw [succ_to_nat]; rw [size_to
_nat n];…
-/
theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 0 => Nat.size_zero.symm
  | pos p => p.size_to_nat
/-
**Num.size_eq_natSize** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), ↑n.size = n.natSize
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.size_eq_natSize`：∀ (n : PosNum), ↑n.size = n.natSize
-/
theorem size_eq_natSize : ∀ n, (size n : ℕ) = natSize n
  | 0 => rfl
  | pos p => p.size_eq_natSize
/-
**Num.natSize_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：natSize_to_nat (n) : natSize n = Nat.size n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.size_eq_natSize`：∀ (n : Num), ↑n.size = n.natSize
· 使用定理 `Num.size_to_nat`：∀ (n : Num), ↑n.size = (↑n).size
-/
theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]

@[simp 999]
/-
**Num.ofNat'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : ℕ), Num.ofNat' n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.ofNat'_zero`：Num.ofNat' 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofNat'_eq : ∀ n, Num.ofNat' n = n :=
  Nat.binaryRec (by simp) fun b n IH => by tauto
/-
**Num.zneg_toZNum** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg := by cases n <;> rfl
/-
**Num.zneg_toZNumNeg** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum
参数：n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum := by cases n <;> rfl
/-
**Num.toZNum_inj** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：toZNum_inj {m n : Num} : m.toZNum = n.toZNum ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toZNum_inj {m n : Num} : m.toZNum = n.toZNum ↔ m = n :=
  ⟨fun h => by cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩

@[simp]
/-
**Num.cast_toZNum** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Add α] [inst_3
 : Neg α] (n : Num), ↑n.toZNum = ↑n
参数：n : Num。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_toZNum [Zero α] [One α] [Add α] [Neg α] : ∀ n : Num, (n.toZNum : α) = n
  | 0 => rfl
  | Num.pos _p => rfl

@[simp]
/-
**Num.cast_toZNumNeg** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ {α : Type u_1} [inst : SubtractionMonoid α] [inst_1 : One α] (n : Num), 
↑n.toZNumNeg = -↑n
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem cast_toZNumNeg [SubtractionMonoid α] [One α] : ∀ n : Num, (n.toZNumNeg : α) = -n
  | 0 => neg_zero.symm
  | Num.pos _p => rfl

@[simp]
/-
**Num.add_toZNum** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：add_toZNum (m n : Num) : Num.toZNum (m + n) = m.toZNum + n.toZNum
参数：m n : Num。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_toZNum (m n : Num) : Num.toZNum (m + n) = m.toZNum + n.toZNum := by
  cases m <;> cases n <;> rfl

end Num

namespace PosNum

open Num

/-
**PosNum.pred_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：pred_to_nat {n : PosNum} (h : 1 < n) : (pred n : Nat) = Nat.pred n
参数：h : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Nat.pred_le_pred`：∀ {n m : ℕ}, n ≤ m → n.pred ≤ m.pred
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PosNum.cast_lt`：cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRi
ng α] {m n : PosNum} : (m : α) < n ↔ m < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.pred'_to_nat`：∀ (n : PosNum), ↑n.pred' = (↑n).pred
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem pred_to_nat {n : PosNum} (h : 1 < n) : (pred n : ℕ) = Nat.pred n := by
  unfold pred
  cases e : pred' n
  · have : (1 : ℕ) ≤ Nat.pred n := Nat.pred_le_pred ((@cast_lt ℕ _ _ _).2 h)
    rw [← pred'_to_nat, e] at this
    exact absurd this (by decide)
  · rw [← pred'_to_nat, e]
    rfl
/-
**PosNum.sub'_one** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：∀ (a : PosNum), a.sub' 1 = a.pred'.toZNum
参数：a : PosNum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum := by cases a <;> rfl
/-
**PosNum.one_sub'** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZNumNeg
参数：a : PosNum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.sub'`：sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZNumNeg := by cases a <;> rfl
/-
**PosNum.lt_iff_cmp** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl
/-
**PosNum.le_iff_cmp** 是 Mathlib 中的一个定理，位于命名空间 `PosNum`。
形式化陈述：le_iff_cmp {m n} : m <= n ↔ cmp m n != Ordering.gt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PosNum.lt_iff_cmp`：lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cmp_swap`：cmp_swap (m) : forall n, (cmp m n).swap = cmp n m
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <| lt_iff_cmp.trans <| by rw [← cmp_swap]; cases cmp m n <;> decide

end PosNum

namespace Num

variable {α : Type*}

open PosNum

/-
**Num.pred_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), ↑n.pred = (↑n).pred
参数：n : Num；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.pred.eq_2`：∀ (p : PosNum), (Num.pos p).pred = p.pred'
· 使用定理 `PosNum.pred'_to_nat`：∀ (n : PosNum), ↑n.pred' = (↑n).pred
-/
theorem pred_to_nat : ∀ n : Num, (pred n : ℕ) = Nat.pred n
  | 0 => rfl
  | pos p => by rw [pred, PosNum.pred'_to_nat]; rfl
/-
**Num.ppred_to_nat** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：∀ (n : Num), castNum <$> n.ppred = (↑n).ppred
参数：n : Num；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosNum.pred'`：pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n | 1 
=> rfl | bit0 n => have : Nat.succ ↑(pred' n) = ↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Num.ppred.eq_2`：∀ (p : PosNum), (Num.pos p).ppred = some p.pred'
· 使用定理 `Option.map_eq_map`：∀ {α α_1 : Type u_1} {f : α → α_1}, Functor.map f = O
ption.map f
· 使用定理 `Option.map_some`：∀ {α : Type u_1} {β : Type u_2} (a : α) (f : α → β), Op
tion.map f (some a) = some (f a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ppred_eq_some`：∀ {m n : ℕ}, n.ppred = some m ↔ m.succ = n
· 使用定理 `PosNum.pred'_to_nat`：∀ (n : PosNum), ↑n.pred' = (↑n).pred
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `PosNum.to_nat_pos`：to_nat_pos : forall n : PosNum, 0 < (n : Nat) | 1 => 
Nat.zero_lt_one | bit0 p => let h
-/
theorem ppred_to_nat : ∀ n : Num, (↑) <$> ppred n = Nat.ppred n
  | 0 => rfl
  | pos p => by
    rw [ppred, Option.map_eq_map, Option.map_some, Nat.ppred_eq_some.2]
    rw [PosNum.pred'_to_nat, Nat.succ_pred_eq_of_pos (PosNum.to_nat_pos _)]
    rfl
/-
**Num.cmp_swap** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cmp_swap (m n) : (cmp m n).swap = cmp n m
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PosNum.cmp_swap`：cmp_swap (m) : forall n, (cmp m n).swap = cmp n m
-/
theorem cmp_swap (m n) : (cmp m n).swap = cmp n m := by
  cases m <;> cases n <;> try { rfl }; apply PosNum.cmp_swap
/-
**Num.cmp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n
参数：m n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.cmp_to_nat`：cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) ((m
 : Nat) < n) (m = n) ((n : Nat) < m) : Prop) | 0, 0 => rfl | 0, pos _ => to_nat_
pos …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]
/-
**Num.cast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} 
: (m : α) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Num.lt_to_nat`：lt_to_nat {m n : Num} : (m : Nat) < n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt (α := α), lt_to_nat]

@[simp, norm_cast]
/-
**Num.cast_le** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : Num} :
 (m : α) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Num.cast_lt`：cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing 
α] {m n : Num} : (m : α) < n ↔ m < n
-/
theorem cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]
/-
**Num.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：cast_inj [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num}
 : (m : α) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cast_to_nat`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] (n : Num),
 ↑↑n = ↑n
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Num.to_nat_inj`：to_nat_inj {m n : Num} : (m : Nat) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_inj [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]
/-
**Num.lt_iff_cmp** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl
/-
**Num.le_iff_cmp** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：le_iff_cmp {m n} : m <= n ↔ cmp m n != Ordering.gt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Num.lt_iff_cmp`：lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cmp_swap`：cmp_swap (m n) : (cmp m n).swap = cmp n m
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <| lt_iff_cmp.trans <| by rw [← cmp_swap]; cases cmp m n <;> decide
/-
**Num.castNum_eq_bitwise** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_eq_bitwise {f : Num -> Num -> Num} {g : Bool -> Bool -> Bool} (p :
 PosNum -> PosNum -> Num) (gff : g false false = false) (f00 : f 0 0 = 0) (f0n :
 forall n, f 0 (pos n) = cond (g false true) (pos n) 0) (fn0 : forall n, f (pos 
n) 0 = cond (g true false) (pos n) 0) (fnn : forall m n, f (pos m) (pos n) = p m
 n) (p11 : p 1 1 = cond (g true true) 1 0) (p1b : forall b n, p 1 (PosNum.bit b 
n) = bit (g true b) (cond (g false true) (pos n) 0)) (pb1 : forall a m, p (PosNu
m.bit a m) 1 = bit (g a tr
参数：p : PosNum -> PosNum -> Num；gff : g false false = false；f00 : f 0 0 = 0；f0n :
 forall n, f 0 (pos n) = cond (g false true) (pos n) 0；fn0 : forall n, f (pos n)
 0 = cond (g true false) (pos n) 0；fnn : forall m n, f (pos m) (pos n) = p m n；p
11 : p 1 1 = cond (g true true) 1 0；p1b : forall b n, p 1 (PosNum.bit b n) = bit
 (g true b) (cond (g false true) (pos n) 0)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.bitwise_zero`：bitwise_zero : bitwise f 0 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.bitwise_zero_left`：bitwise_zero_left (m : Nat) : bitwise f 0 m = if 
f false true then m else 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.bitwise_zero_right`：bitwise_zero_right (n : Nat) : bitwise f n 0 = i
f f true false then n else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PosNum.bit_to_nat`：bit_to_nat (b n) : (bit b n : Nat) = Nat.bit b n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.bitwise_bit`：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false fal
se = false
· 使用定理 `Bool.cond_eq_ite`：∀ {α : Sort u_1} (b : Bool) (t e : α), (bif b then t e
lse e) = if b = true then t else e
· 使用定理 `Num.bit_to_nat`：bit_to_nat (b n) : (bit b n : Nat) = Nat.bit b n
-/
theorem castNum_eq_bitwise {f : Num → Num → Num} {g : Bool → Bool → Bool}
    (p : PosNum → PosNum → Num)
    (gff : g false false = false) (f00 : f 0 0 = 0)
    (f0n : ∀ n, f 0 (pos n) = cond (g false true) (pos n) 0)
    (fn0 : ∀ n, f (pos n) 0 = cond (g true false) (pos n) 0)
    (fnn : ∀ m n, f (pos m) (pos n) = p m n) (p11 : p 1 1 = cond (g true true) 1 0)
    (p1b : ∀ b n, p 1 (PosNum.bit b n) = bit (g true b) (cond (g false true) (pos n) 0))
    (pb1 : ∀ a m, p (PosNum.bit a m) 1 = bit (g a true) (cond (g true false) (pos m) 0))
    (pbb : ∀ a b m n, p (PosNum.bit a m) (PosNum.bit b n) = bit (g a b) (p m n)) :
    ∀ m n : Num, (f m n : ℕ) = Nat.bitwise g m n := by
  intro m n
  obtain - | m := m <;> obtain - | n := n <;>
      try simp only [show zero = 0 from rfl, show ((0 : Num) : ℕ) = 0 from rfl]
  · rw [f00, Nat.bitwise_zero]; rfl
  · rw [f0n, Nat.bitwise_zero_left]
    cases g false true <;> rfl
  · rw [fn0, Nat.bitwise_zero_right]
    cases g true false <;> rfl
  · rw [fnn]
    have this b (n : PosNum) : (cond b (↑n) 0 : ℕ) = ↑(cond b (pos n) 0 : Num) := by
      cases b <;> rfl
    have this' b (n : PosNum) : ↑(pos (PosNum.bit b n)) = Nat.bit b ↑n := by
      cases b <;> simp
    induction m generalizing n with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    obtain - | n | n := n
    any_goals simp only [show one = 1 from rfl, show pos 1 = 1 from rfl,
      show PosNum.bit0 = PosNum.bit false from rfl, show PosNum.bit1 = PosNum.bit true from rfl,
      show ((1 : Num) : ℕ) = Nat.bit true 0 from rfl]
    all_goals
      repeat rw [this']
      rw [Nat.bitwise_bit gff]
    any_goals rw [Nat.bitwise_zero, p11]; cases g true true <;> rfl
    any_goals rw [Nat.bitwise_zero_left, ← Bool.cond_eq_ite, this, ← bit_to_nat, p1b]
    any_goals rw [Nat.bitwise_zero_right, ← Bool.cond_eq_ite, this, ← bit_to_nat, pb1]
    all_goals
      rw [← show ∀ n : PosNum, ↑(p m n) = Nat.bitwise g ↑m ↑n from IH]
      rw [← bit_to_nat, pbb]

@[simp, norm_cast]
/-
**Num.castNum_or** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_or : forall m n : Num, ↑(m ||| n) = (↑m ||| ↑n : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.castNum_eq_bitwise`：castNum_eq_bitwise {f : Num -> Num -> Num} {g : 
Bool -> Bool -> Bool} (p : PosNum -> PosNum -> Num) (gff : g false false = false
) (f00 : f 0…
-/
theorem castNum_or : ∀ m n : Num, ↑(m ||| n) = (↑m ||| ↑n : ℕ) := by
  apply castNum_eq_bitwise fun x y => pos (PosNum.lor x y) <;>
    (try rintro (_ | _)) <;> (try rintro (_ | _)) <;> intros <;> rfl

@[simp, norm_cast]
/-
**Num.castNum_and** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_and : forall m n : Num, ↑(m &&& n) = (↑m &&& ↑n : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.castNum_eq_bitwise`：castNum_eq_bitwise {f : Num -> Num -> Num} {g : 
Bool -> Bool -> Bool} (p : PosNum -> PosNum -> Num) (gff : g false false = false
) (f00 : f 0…
-/
theorem castNum_and : ∀ m n : Num, ↑(m &&& n) = (↑m &&& ↑n : ℕ) := by
  apply castNum_eq_bitwise PosNum.land <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
/-
**Num.castNum_ldiff** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_ldiff : forall m n : Num, (ldiff m n : Nat) = Nat.ldiff m n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.castNum_eq_bitwise`：castNum_eq_bitwise {f : Num -> Num -> Num} {g : 
Bool -> Bool -> Bool} (p : PosNum -> PosNum -> Num) (gff : g false false = false
) (f00 : f 0…
-/
theorem castNum_ldiff : ∀ m n : Num, (ldiff m n : ℕ) = Nat.ldiff m n := by
  apply castNum_eq_bitwise PosNum.ldiff <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
/-
**Num.castNum_xor** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_xor : forall m n : Num, ↑(m ^^^ n) = (↑m ^^^ ↑n : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Num.castNum_eq_bitwise`：castNum_eq_bitwise {f : Num -> Num -> Num} {g : 
Bool -> Bool -> Bool} (p : PosNum -> PosNum -> Num) (gff : g false false = false
) (f00 : f 0…
-/
theorem castNum_xor : ∀ m n : Num, ↑(m ^^^ n) = (↑m ^^^ ↑n : ℕ) := by
  apply castNum_eq_bitwise PosNum.lxor <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
/-
**Num.castNum_shiftLeft** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_shiftLeft (m : Num) (n : Nat) : ↑(m <<< n) = (m : Nat) <<< (n : Na
t)
参数：m : Num；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_shiftLeft`：∀ (n : ℕ), 0 <<< n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosNum.shiftl_succ_eq_bit0_shiftl`：∀ (p : PosNum) (n : ℕ), p <<< n.succ 
= (p <<< n).bit0
· 使用定理 `Nat.shiftLeft_succ`：∀ (m n : ℕ), m <<< (n + 1) = 2 * m <<< n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem castNum_shiftLeft (m : Num) (n : Nat) : ↑(m <<< n) = (m : ℕ) <<< (n : ℕ) := by
  cases m <;> dsimp only [← shiftl_eq_shiftLeft, shiftl]
  · symm
    apply Nat.zero_shiftLeft
  simp only [cast_pos]
  induction n with
  | zero => rfl
  | succ n IH =>
    simp [PosNum.shiftl_succ_eq_bit0_shiftl, Nat.shiftLeft_succ, IH, mul_comm,
      -shiftl_eq_shiftLeft, -PosNum.shiftl_eq_shiftLeft, mul_two]

@[simp, norm_cast]
/-
**Num.castNum_shiftRight** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_shiftRight (m : Num) (n : Nat) : ↑(m >>> n) = (m : Nat) >>> (n : N
at)
参数：m : Num；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_shiftRight`：∀ (n : ℕ), 0 >>> n = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div2_val`：div2_val (n : Nat) : div2 n = n / 2
· 使用定理 `Nat.shiftRight_eq_div_pow`：∀ (m n : ℕ), m >>> n = m / 2 ^ n
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.shiftRight_eq`：∀ (m n : ℕ), m.shiftRight n = m >>> n
· 使用定理 `Nat.shiftRight_add`：∀ (m n k : ℕ), m >>> (n + k) = m >>> n >>> k
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Nat.div2_succ`：div2_succ (n : Nat) : div2 (n + 1) = cond (bodd n) (succ 
(div2 n)) (div2 n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_add`：bodd_add (m n : Nat) : bodd (m + n) = bxor (bodd m) (bodd 
n)
· 使用定理 `bne_self_eq_false`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α)
, (a != a) = false
· 使用定理 `instLawfulBEqBool`：LawfulBEq Bool
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem castNum_shiftRight (m : Num) (n : Nat) : ↑(m >>> n) = (m : ℕ) >>> (n : ℕ) := by
  obtain - | m := m <;> dsimp only [← shiftr_eq_shiftRight, shiftr]
  · symm
    apply Nat.zero_shiftRight
  induction n generalizing m with
  | zero => cases m <;> rfl
  | succ n IH => ?_
  have hdiv2 : ∀ m, Nat.div2 (m + m) = m := by intro; rw [Nat.div2_val]; lia
  obtain - | m | m := m <;> dsimp only [PosNum.shiftr, ← PosNum.shiftr_eq_shiftRight]
  · rw [Nat.shiftRight_eq_div_pow]
    symm
    apply Nat.div_eq_of_lt
    simp
  · trans
    · apply IH
    change Nat.shiftRight m n = Nat.shiftRight (m + m + 1) (n + 1)
    rw [add_comm n 1, @Nat.shiftRight_eq _ (1 + n), Nat.shiftRight_add]
    apply congr_arg fun x => Nat.shiftRight x n
    simp [-add_assoc, Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, hdiv2]
  · trans
    · apply IH
    change Nat.shiftRight m n = Nat.shiftRight (m + m) (n + 1)
    rw [add_comm n 1, @Nat.shiftRight_eq _ (1 + n), Nat.shiftRight_add]
    apply congr_arg fun x => Nat.shiftRight x n
    simp [-add_assoc, Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, hdiv2]

@[simp]
/-
**Num.castNum_testBit** 是 Mathlib 中的一个定理，位于命名空间 `Num`。
形式化陈述：castNum_testBit (m n) : testBit m n = Nat.testBit m n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_testBit`：∀ (i : ℕ), Nat.testBit 0 i = false
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Num.cast_pos`：cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos 
n : α) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PosNum.testBit.eq_1`：PosNum.one.testBit 0 = true
· 使用定理 `PosNum.cast_bit1`：cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) 
= ((n : α) + n) + 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Nat.bit_true`：bit_true : bit true = (2 * · + 1)
· 使用定理 `Nat.testBit_bit_zero`：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
· 使用定理 `PosNum.cast_bit0`：cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) 
= (n : α) + n
· 使用定理 `Nat.bit_false`：bit_false : bit false = (2 * ·)
· 使用定理 `PosNum.testBit.eq_2`：∀ (x : ℕ), (x = 0 → False) → PosNum.one.testBit x =
 false
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.testBit_add_one`：∀ (x i : ℕ), x.testBit (i + 1) = (x / 2).testBit i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.testBit_bit_succ`：testBit_bit_succ (m b n) : testBit (bit b n) (succ
 m) = testBit n m
-/
theorem castNum_testBit (m n) : testBit m n = Nat.testBit m n := by
  cases m with dsimp only [testBit]
  | zero =>
    rw [show (Num.zero : Nat) = 0 from rfl, Nat.zero_testBit]
  | pos m =>
    rw [cast_pos]
    induction n generalizing m <;> obtain - | m | m := m
        <;> simp only [PosNum.testBit]
    · rfl
    · rw [PosNum.cast_bit1, ← two_mul, ← congr_fun Nat.bit_true, Nat.testBit_bit_zero]
    · rw [PosNum.cast_bit0, ← two_mul, ← congr_fun Nat.bit_false, Nat.testBit_bit_zero]
    · simp [Nat.testBit_add_one]
    case succ.bit1 n IH =>
      rw [PosNum.cast_bit1, ← two_mul, ← congr_fun Nat.bit_true, Nat.testBit_bit_succ, IH]
    case succ.bit0 n IH =>
      rw [PosNum.cast_bit0, ← two_mul, ← congr_fun Nat.bit_false, Nat.testBit_bit_succ, IH]

end Num

namespace Int

/-- Cast a `SNum` to the corresponding integer. -/
/-
**Int.ofSnum** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ofSnum : SNum -> Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast a `SNum` to the corresponding integer.
-/
def ofSnum : SNum → ℤ :=
  SNum.rec' (fun a => cond a (-1) 0) fun a _p IH => cond a (2 * IH + 1) (2 * IH)
/-
**Int.snumCoe** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：snumCoe : Coe SNum Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance snumCoe : Coe SNum ℤ :=
  ⟨ofSnum⟩

end Int

/-
**SNum.lt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SNum.lt : LT SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SNum.lt : LT SNum :=
  ⟨fun a b => (a : ℤ) < b⟩
/-
**SNum.le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SNum.le : LE SNum
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SNum.le : LE SNum :=
  ⟨fun a b => (a : ℤ) ≤ b⟩
