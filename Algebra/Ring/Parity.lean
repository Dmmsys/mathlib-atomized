/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Iterate

/-!
# Even and odd elements in rings

This file defines odd elements and proves some general facts about even and odd elements of rings.

As opposed to `Even`, `Odd` does not have a multiplicative counterpart.

## TODO

Try to generalize `Even` lemmas further. For example, there are still a few lemmas whose `Semiring`
assumptions I (DT) am not convinced are necessary. If that turns out to be true, they could be moved
to `Mathlib/Algebra/Group/Even.lean`.

## See also

`Mathlib/Algebra/Group/Even.lean` for the definition of even elements.
-/

@[expose] public section

assert_not_exists DenselyOrdered IsOrderedRing

open MulOpposite

variable {F α β : Type*}

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : ℕ} {a : α}

/-
**Even.neg_pow** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg α] {n : ℕ}, Eve
n n → ∀ (a : α), (-a) ^ n = a ^ n
参数：a : α；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma Even.neg_pow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]
/-
**Even.neg_one_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
参数：h : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]

end Monoid

/-
**IsSquare.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsSquare`。
形式化陈述：∀ {α : Type u_2} [inst : MulZeroClass α], IsSquare 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] lemma IsSquare.zero [MulZeroClass α] : IsSquare (0 : α) := ⟨0, (mul_zero _).symm⟩

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/-
**even_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
-/
@[simp] lemma even_two : Even (2 : α) := ⟨1, by rw [one_add_one_eq_two]⟩

end AddMonoidWithOne

section Distrib
variable [Add α] [Mul α] {a : α}

/-
**Even.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_2} [inst : Add α] [inst_1 : Mul α] {a : α} [LeftDistribClass
 α], Even a → ∀ (b : α), Even (b * a)
参数：b : α；b * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma Even.mul_left [LeftDistribClass α] (ha : Even a) (b : α) : Even (b * a) := by
  rcases ha with ⟨k, rfl⟩
  use b * k
  rw [mul_add]
/-
**Even.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_2} [inst : Add α] [inst_1 : Mul α] {a : α} [RightDistribClas
s α], Even a → ∀ (b : α), Even (a * b)
参数：b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma Even.mul_right [RightDistribClass α] (ha : Even a) (b : α) : Even (a * b) := by
  rcases ha with ⟨k, rfl⟩
  use k * b
  rw [add_mul]

end Distrib

section Semiring
variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

/-
**even_iff_exists_two_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_iff_exists_two_mul : Even a ↔ exists b, a = 2 * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma even_iff_exists_two_mul : Even a ↔ ∃ b, a = 2 * b := by simp [even_iff_exists_two_nsmul]
/-
**even_iff_two_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_iff_two_dvd : Even a ↔ 2 ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma even_iff_two_dvd : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd
/-
**Even.trans_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b
参数：ha : Even a；hab : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
-/
lemma Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b :=
  even_iff_two_dvd.2 <| ha.two_dvd.trans hab
/-
**Dvd.dvd.even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b
参数：hab : a ∣ b；ha : Even a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.trans_dvd`：Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b
-/
lemma Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b := ha.trans_dvd hab
/-
**range_two_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_4) [inst : NonAssocSemiring α], (Set.range fun x => 2 * x) =
 {a | Even a}
参数：α : Type u_4；Set.range fun x => 2 * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma range_two_mul (α) [NonAssocSemiring α] :
    Set.range (fun x : α ↦ 2 * x) = {a | Even a} := by
  ext x
  simp [eq_comm, two_mul, Even]
/-
**even_two_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_two_mul (a : α) : Even (2 * a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
lemma even_two_mul (a : α) : Even (2 * a) := ⟨a, two_mul _⟩
/-
**Even.pow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → ∀ {n : ℕ}, n ≠ 0 → 
Even (a ^ n)
参数：a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Even.mul_left`：∀ {α : Type u_2} [inst : Add α] [inst_1 : Mul α] {a : α} 
[LeftDistribClass α], Even a → ∀ (b : α), Even (b * a)
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
lemma Even.pow_of_ne_zero (ha : Even a) : ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
  | n + 1, _ => by rw [pow_succ]; exact ha.mul_left _

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
/-
**Odd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Odd (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`.
-/
def Odd (a : α) : Prop := ∃ k, a = 2 * k + 1
/-
**odd_iff_exists_bit1** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_iff_exists_bit1 : Odd a ↔ exists b, a = 2 * b + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma odd_iff_exists_bit1 : Odd a ↔ ∃ b, a = 2 * b + 1 := exists_congr fun b ↦ by rw [two_mul]

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1
/-
**range_two_mul_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_4) [inst : Semiring α], (Set.range fun x => 2 * x + 1) = {a 
| Odd a}
参数：α : Type u_4；Set.range fun x => 2 * x + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma range_two_mul_add_one (α : Type*) [Semiring α] :
    Set.range (fun x : α ↦ 2 * x + 1) = {a | Odd a} := by ext x; simp [Odd, eq_comm]
/-
**Even.add_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.add_odd : Even a -> Odd b -> Odd (a + b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma Even.add_odd : Even a → Odd b → Odd (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩
/-
**Even.odd_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a)
参数：ha : Even a；hb : Odd b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a) := add_comm a b ▸ ha.add_odd hb
/-
**Odd.add_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b)
参数：ha : Odd a；hb : Even b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b) := add_comm a b ▸ hb.add_odd ha
/-
**Odd.add_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `IsAddCommutative.is_comm`：∀ {M : Type u_2} {inst : Add M} [self : IsAddC
ommutative M], Std.Commutative fun x1 x2 => x1 + x2
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Odd.add_odd : Odd a → Odd b → Even (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨a + b + 1, ?_⟩
  rw [two_mul, two_mul]
  ac_rfl
/-
**odd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α], Odd 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] lemma odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
/-
**Even.add_one** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd (a + 1)
参数：a + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
-/
@[simp] lemma Even.add_one (h : Even a) : Odd (a + 1) := h.add_odd odd_one
/-
**Even.one_add** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd (1 + a)
参数：1 + a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.odd_add`：Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
-/
@[simp] lemma Even.one_add (h : Even a) : Odd (1 + a) := h.odd_add odd_one
/-
**Odd.add_one** 是 Mathlib 中的一个定理，位于命名空间 `Odd`。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd a → Even (a + 1)
参数：a + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.add_odd`：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
-/
@[simp] lemma Odd.add_one (h : Odd a) : Even (a + 1) := h.add_odd odd_one
/-
**Odd.one_add** 是 Mathlib 中的一个定理，位于命名空间 `Odd`。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd a → Even (1 + a)
参数：1 + a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.add_odd`：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
-/
@[simp] lemma Odd.one_add (h : Odd a) : Even (1 + a) := odd_one.add_odd h
/-
**odd_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_two_mul_add_one (a : α) : Odd (2 * a + 1)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma odd_two_mul_add_one (a : α) : Odd (2 * a + 1) := ⟨_, rfl⟩
/-
**odd_add_self_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd (a + (a + 1))
参数：a + (a + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] lemma odd_add_self_one' : Odd (a + (a + 1)) := by simp [← add_assoc]
/-
**odd_add_one_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd (a + 1 + a)
参数：a + 1 + a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
@[simp] lemma odd_add_one_self : Odd (a + 1 + a) := by simp [add_comm _ a]
/-
**odd_add_one_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd (a + (1 + a))
参数：a + (1 + a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
@[simp] lemma odd_add_one_self' : Odd (a + (1 + a)) := by simp [add_comm 1 a]
/-
**Odd.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a -> Odd (f a)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a → Odd (f a) := by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩
/-
**Odd.natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.natCast {R : Type*} [Semiring R] {n : Nat} (hn : Odd n) : Odd (n : R)
参数：hn : Odd n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.map`：Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a ->
 Odd (f a)
-/
lemma Odd.natCast {R : Type*} [Semiring R] {n : ℕ} (hn : Odd n) : Odd (n : R) :=
  hn.map <| Nat.castRingHom R
/-
**Odd.mul** 是 Mathlib 中的一个定理，位于命名空间 `Odd`。
形式化陈述：∀ {α : Type u_2} [inst : Semiring α] {a b : α}, Odd a → Odd b → Odd (a * b
)
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
-/
@[simp] lemma Odd.mul : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
/-
**Odd.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.pow {n : Nat} (ha : Odd a) : Odd (a ^ n)
参数：ha : Odd a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Odd.mul`：∀ {α : Type u_2} [inst : Semiring α] {a b : α}, Odd a → Odd b →
 Odd (a * b)
-/
lemma Odd.pow {n : ℕ} (ha : Odd a) : Odd (a ^ n) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hrec => rw [pow_succ]; exact hrec.mul ha
/-
**Odd.pow_add_pow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) : a
 ^ n + b ^ n = 0
参数：hn : Odd n；hab : a + b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
lemma Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) :
    a ^ n + b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with | zero => simpa | succ k ih => ?_
  have : a ^ 2 = b ^ 2 := add_right_cancel <|
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := b ^ (2 * k + 1) * a ^ 2) ?_
  calc
    _ = (a ^ (2 * k + 1) + b ^ (2 * k + 1)) * a ^ 2 + b ^ (2 * k + 3) := by
      rw [add_mul, ← pow_add, add_right_comm]; rfl
    _ = _ := by rw [ih, zero_mul, zero_add, zero_add, this, ← pow_add]
/-
**Even.of_isUnit_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Even a
参数：h : IsUnit (2 : α)；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
theorem Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Even a :=
  let ⟨u, hu⟩ := h; ⟨u⁻¹ * a, by rw [← mul_add, ← two_mul, ← hu, Units.inv_mul_cancel_left]⟩
/-
**isUnit_two_iff_forall_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_two_iff_forall_even : IsUnit (2 : α) ↔ forall a : α, Even a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Even.of_isUnit_two`：Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Ev
en a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.ofNat_right`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (x : α
) (n : ℕ) [inst_1 : n.AtLeastTwo], Commute x (OfNat.ofNat n)
-/
theorem isUnit_two_iff_forall_even : IsUnit (2 : α) ↔ ∀ a : α, Even a := by
  refine ⟨Even.of_isUnit_two, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h 1
  rw [← two_mul, eq_comm] at ha
  exact ⟨⟨2, a, ha, .trans (Commute.ofNat_right _ _).eq ha⟩, rfl⟩

end Semiring

section Ring
variable [Ring α]

/-
**Odd.of_isUnit_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Odd.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Odd a
参数：h : IsUnit (2 : α)；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Even.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd
 (a + 1)
· 使用定理 `Even.of_isUnit_two`：Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Ev
en a
-/
theorem Odd.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Odd a := by
  rw [← sub_add_cancel a 1]
  exact (Even.of_isUnit_two h _).add_one

end Ring

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : ℕ}

/-
**Odd.neg_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
/-
**Odd.neg_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `Odd`。
形式化陈述：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg α] {n : ℕ}, Odd
 n → (-1) ^ n = -1
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
@[simp] lemma Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]

end Monoid

section Ring
variable [Ring α] {a b : α} {n : ℕ}

/-
**even_neg_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_neg_two : Even (-2 : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
/-
**Odd.neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.neg (hp : Odd a) : Odd (-a)
参数：hp : Odd a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right,
    ← neg_add, hk]
/-
**odd_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Ring α] {a : α}, Odd (-a) ↔ Odd a
参数：-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.neg`：Odd.neg (hp : Odd a) : Odd (-a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma odd_neg : Odd (-a) ↔ Odd a := ⟨fun h ↦ neg_neg a ▸ h.neg, Odd.neg⟩
/-
**odd_neg_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_neg_one : Odd (-1 : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma odd_neg_one : Odd (-1 : α) := by simp
/-
**Odd.sub_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b)
参数：ha : Odd a；hb : Even b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Odd.add_even`：Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b)
· 使用定理 `Even.neg`：∀ {α : Type u_2} [inst : SubtractionMonoid α] {a : α}, Even a 
→ Even (-a)
-/
lemma Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_even hb.neg
/-
**Even.sub_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b)
参数：ha : Even a；hb : Odd b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用引理 `Odd.neg`：Odd.neg (hp : Odd a) : Odd (-a)
-/
lemma Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg
/-
**Odd.sub_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b)
参数：ha : Odd a；hb : Odd b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Odd.add_odd`：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
· 使用引理 `Odd.neg`：Odd.neg (hp : Odd a) : Odd (-a)
-/
lemma Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

@[simp]
/-
**even_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_add_one : Even (a + 1) ↔ Odd a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用引理 `Even.sub_odd`：Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
· 使用定理 `Odd.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd a → Even 
(a + 1)
-/
lemma even_add_one : Even (a + 1) ↔ Odd a :=
  ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]
/-
**even_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_sub_one : Even (a - 1) ↔ Odd a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
· 使用引理 `Odd.sub_odd`：Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b)
-/
lemma even_sub_one : Even (a - 1) ↔ Odd a :=
  ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]
/-
**even_add_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_add_two : Even (a + 2) ↔ Even a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Even.sub`：∀ {α : Type u_2} [inst : SubtractionCommMonoid α] {a b : α}, E
ven a → Even b → Even (a - b)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
· 使用引理 `Even.add`：Even.add [Add β] {f g : α -> β} (hf : f.Even) (hg : g.Even) : 
(f + g).Even
-/
lemma even_add_two : Even (a + 2) ↔ Even a :=
  ⟨(by convert! ·.sub even_two; rw [eq_sub_iff_add_eq]), (·.add even_two)⟩

@[simp]
/-
**even_sub_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_sub_two : Even (a - 2) ↔ Even a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `Even.add`：Even.add [Add β] {f g : α -> β} (hf : f.Even) (hg : g.Even) : 
(f + g).Even
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
· 使用定理 `Even.sub`：∀ {α : Type u_2} [inst : SubtractionCommMonoid α] {a b : α}, E
ven a → Even b → Even (a - b)
-/
lemma even_sub_two : Even (a - 2) ↔ Even a :=
  ⟨(by convert! ·.add even_two; rw [sub_add_cancel]), (·.sub even_two)⟩

@[simp]
/-
**odd_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_add_one : Odd (a + 1) ↔ Even a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用引理 `Odd.sub_odd`：Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
· 使用定理 `Even.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd
 (a + 1)
-/
lemma odd_add_one : Odd (a + 1) ↔ Even a :=
  ⟨(by convert! ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

@[simp]
/-
**odd_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_sub_one : Odd (a - 1) ↔ Even a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `Odd.add_odd`：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
· 使用引理 `Even.sub_odd`：Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b)
-/
lemma odd_sub_one : Odd (a - 1) ↔ Even a :=
  ⟨(by convert! ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

@[simp]
/-
**odd_add_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_add_two : Odd (a + 2) ↔ Odd a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `odd_add_one`：odd_add_one : Odd (a + 1) ↔ Even a
· 使用引理 `even_add_one`：even_add_one : Even (a + 1) ↔ Odd a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma odd_add_two : Odd (a + 2) ↔ Odd a := by
  rw [← one_add_one_eq_two, ← add_assoc, odd_add_one, even_add_one]

@[simp]
/-
**odd_sub_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_sub_two : Odd (a - 2) ↔ Odd a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `odd_add_two`：odd_add_two : Odd (a + 2) ↔ Odd a
· 使用定理 `add_comm_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c :
 α), a - b + c = a + (c - b)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma odd_sub_two : Odd (a - 2) ↔ Odd a := by
  rw [← odd_add_two (a := a - 2), add_comm_sub, sub_self, add_zero]

end Ring

namespace Nat
variable {m n : ℕ}

@[grind =]
/-
**Nat.odd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：odd_iff : Odd n ↔ n % 2 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ ↦ by lia, fun h ↦ ⟨n / 2, by lia⟩⟩
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (Odd : ℕ → Prop) := fun _ ↦ decidable_of_iff _ odd_iff.symm
/-
**Nat.not_odd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：not_odd_iff : ¬Odd n ↔ n % 2 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind
/-
**Nat.not_odd_iff_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, ¬Odd n ↔ Even n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by grind
/-
**Nat.not_even_iff_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, ¬Even n ↔ Odd n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by grind
/-
**Nat.not_odd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：¬Odd 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_odd_zero : ¬Odd 0 := by grind
/-
**Nat._root_.Odd.not_two_dvd_nat** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Odd.not_two_dvd_nat (h : Odd n) : ¬(2 ∣ n) := by grind
/-
**Nat.even_xor_odd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_xor_odd (n : Nat) : Xor (Even n) (Odd n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_xor_odd (n : ℕ) : Xor (Even n) (Odd n) := by grind
/-
**Nat.even_or_odd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_or_odd (n : Nat) : Even n ∨ Odd n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Xor.or`：∀ {a b : Prop}, Xor a b → a ∨ b
· 使用引理 `Nat.even_xor_odd`：even_xor_odd (n : Nat) : Xor (Even n) (Odd n)
-/
lemma even_or_odd (n : ℕ) : Even n ∨ Odd n := (even_xor_odd n).or
/-
**Nat.even_or_odd'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_or_odd' (n : Nat) : exists k, n = 2 * k ∨ n = 2 * k + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
-/
lemma even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n
/-
**Nat.even_xor_odd'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_xor_odd' (n : Nat) : exists k, Xor (n = 2 * k) (n = 2 * k + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma even_xor_odd' (n : ℕ) : ∃ k, Xor (n = 2 * k) (n = 2 * k + 1) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;>
  · use k
    grind
/-
**Nat.odd_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：odd_add_one {n : Nat} : Odd (n + 1) ↔ ¬ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_add_one {n : ℕ} : Odd (n + 1) ↔ ¬ Odd n := by grind
/-
**Nat.mod_two_add_add_odd_mod_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mod_two_add_add_odd_mod_two (m : Nat) {n : Nat} (hn : Odd n) : m % 2 + (m 
+ n) % 2 = 1
参数：m : Nat；hn : Odd n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 := by grind
/-
**Nat.mod_two_add_succ_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m : ℕ), m % 2 + (m + 1) % 2 = 1
参数：m : ℕ；m + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mod_two_add_succ_mod_two (m : ℕ) : m % 2 + (m + 1) % 2 = 1 := by lia
/-
**Nat.succ_mod_two_add_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m : ℕ), (m + 1) % 2 + m % 2 = 1
参数：m : ℕ；m + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma succ_mod_two_add_mod_two (m : ℕ) : (m + 1) % 2 + m % 2 = 1 := by lia
/-
**Nat.even_add'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_add' : Even (m + n) ↔ (Odd m ↔ Odd n)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind
/-
**Nat.not_even_bit1** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), ¬Even (2 * n + 1)
参数：n : ℕ；2 * n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma not_even_bit1 (n : ℕ) : ¬Even (2 * n + 1) := by simp [parity_simps]
/-
**Nat.not_even_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：not_even_two_mul_add_one (n : Nat) : ¬ Even (2 * n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_even_two_mul_add_one (n : ℕ) : ¬ Even (2 * n + 1) := by grind
/-
**Nat.even_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_sub' (h : n <= m) : Even (m - n) ↔ (Odd m ↔ Odd n)
参数：h : n <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind
/-
**Nat.Odd.sub_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Odd`。
形式化陈述：∀ {m n : ℕ}, Odd m → Odd n → Even (m - n)
参数：m - n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) := by grind

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd
/-
**Nat.odd_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by grind
/-
**Nat.Odd.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Odd`。
形式化陈述：∀ {m n : ℕ}, Odd (m * n) → Odd m
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.odd_mul`：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
-/
lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1
/-
**Nat.Odd.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Odd`。
形式化陈述：∀ {m n : ℕ}, Odd (m * n) → Odd n
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.odd_mul`：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
-/
lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2
/-
**Nat.odd_pow_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：odd_pow_iff {e : Nat} (he : e != 0) : Odd (n ^ e) ↔ Odd n
参数：he : e != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_pow_iff {e : ℕ} (he : e ≠ 0) : Odd (n ^ e) ↔ Odd n := by grind
/-
**Nat.even_div** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_div : Even (m / n) ↔ m % (2 * n) / n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_mul_right_div_self`：∀ (m n k : ℕ), m % (n * k) / n = m / n % k
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, ← Nat.mod_mul_right_div_self, mul_comm]
/-
**Nat.odd_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, Odd (m + n) ↔ (Odd m ↔ Even n)
参数：m + n；Odd m ↔ Even n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by grind
/-
**Nat.odd_add'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind
/-
**Nat.ne_of_odd_add** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ne_of_odd_add (h : Odd (m + n)) : m != n
参数：h : Odd (m + n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by grind
/-
**Nat.odd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, n ≤ m → (Odd (m - n) ↔ (Odd m ↔ Even n))
参数：Odd (m - n) ↔ (Odd m ↔ Even n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma odd_sub (h : n ≤ m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by grind
/-
**Nat.Odd.sub_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Odd`。
形式化陈述：∀ {m n : ℕ}, n ≤ m → Odd m → Even n → Odd (m - n)
参数：m - n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) := by grind
/-
**Nat.odd_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：odd_sub' (h : n <= m) : Odd (m - n) ↔ (Odd n ↔ Even m)
参数：h : n <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind
/-
**Nat.Even.sub_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Even`。
形式化陈述：∀ {m n : ℕ}, n ≤ m → Even m → Odd n → Odd (m - n)
参数：m - n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) := by grind
/-
**Nat.two_mul_div_two_add_one_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n
参数：h : Odd n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by grind
/-
**Nat.div_two_mul_two_add_one_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n
参数：h : Odd n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n := by grind
/-
**Nat.one_add_div_two_mul_two_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n
参数：h : Odd n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n := by grind
/-
**Nat.two_dvd_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_dvd_mul_add_one (k : Nat) : 2 ∣ k * (k + 1)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用引理 `Nat.even_mul_succ_self`：even_mul_succ_self (n : Nat) : Even (n * (n + 1)
)
-/
lemma two_dvd_mul_add_one (k : ℕ) : 2 ∣ k * (k + 1) :=
  even_iff_two_dvd.mp (even_mul_succ_self k)
/-
**Nat.two_dvd_mul_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_dvd_mul_sub_one (k : Nat) : 2 ∣ k * (k - 1)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Nat.two_dvd_mul_add_one`：two_dvd_mul_add_one (k : Nat) : 2 ∣ k * (k + 1)
-/
lemma two_dvd_mul_sub_one (k : ℕ) : 2 ∣ k * (k - 1) := by
  rcases k with rfl | k; · simp
  simpa [mul_comm (k + 1)] using k.two_dvd_mul_add_one

-- Here are examples of how `parity_simps` can be used with `Nat`.
/-
**Nat.** 是 Mathlib 中的一个示例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, parity_simps]
/-
**Nat.** 是 Mathlib 中的一个示例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ¬Even 25394535 := by decide

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type*} {f : α → α} {n : ℕ}

/-
**Function.Involutive.iterate_two_mul** 是 Mathlib 中的一个引理，位于命名空间 `Function.Involu
tive`。
形式化陈述：iterate_two_mul (hf : Involutive f) (n : Nat) : f^[2 * n] = id
参数：hf : Involutive f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.involutive_iff_iter_2_eq_id`：involutive_iff_iter_2_eq_id {α} {f
 : α -> α} : Involutive f ↔ f^[2] = id
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id
-/
lemma iterate_two_mul (hf : Involutive f) (n : ℕ) : f^[2 * n] = id := by
  rw [iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]
/-
**Function.Involutive.iterate_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Functio
n.Involutive`。
形式化陈述：iterate_two_mul_add_one (hf : Involutive f) (n : Nat) : f^[2 * n + 1] = f
参数：hf : Involutive f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用引理 `Function.Involutive.iterate_two_mul`：iterate_two_mul (hf : Involutive f)
 (n : Nat) : f^[2 * n] = id
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
lemma iterate_two_mul_add_one (hf : Involutive f) (n : ℕ) : f^[2 * n + 1] = f := by
  rw [iterate_succ, hf.iterate_two_mul, id_comp]
/-
**Function.Involutive.iterate_even** 是 Mathlib 中的一个引理，位于命名空间 `Function.Involutiv
e`。
形式化陈述：iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id
参数：hf : Involutive f；hn : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `Function.Involutive.iterate_two_mul`：iterate_two_mul (hf : Involutive f)
 (n : Nat) : f^[2 * n] = id
-/
lemma iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, hf.iterate_two_mul]
/-
**Function.Involutive.iterate_odd** 是 Mathlib 中的一个引理，位于命名空间 `Function.Involutive
`。
形式化陈述：iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f
参数：hf : Involutive f；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用引理 `Function.Involutive.iterate_two_mul`：iterate_two_mul (hf : Involutive f)
 (n : Nat) : f^[2 * n] = id
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f := by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add, hf.iterate_two_mul, id_comp, iterate_one]
/-
**Function.Involutive.iterate_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Function.Involu
tive`。
形式化陈述：iterate_eq_self (hf : Involutive f) (hne : f != id) : f^[n] = f ↔ Odd n
参数：hf : Involutive f；hne : f != id。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Function.Involutive.iterate_even`：iterate_even (hf : Involutive f) (hn :
 Even n) : f^[n] = id
· 使用引理 `Function.Involutive.iterate_odd`：iterate_odd (hf : Involutive f) (hn : O
dd n) : f^[n] = f
-/
lemma iterate_eq_self (hf : Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n :=
  ⟨fun H ↦ not_even_iff_odd.1 fun hn ↦ hne <| by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩
/-
**Function.Involutive.iterate_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `Function.Involuti
ve`。
形式化陈述：iterate_eq_id (hf : Involutive f) (hne : f != id) : f^[n] = id ↔ Even n
参数：hf : Involutive f；hne : f != id。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.Involutive.iterate_odd`：iterate_odd (hf : Involutive f) (hn : O
dd n) : f^[n] = f
· 使用引理 `Function.Involutive.iterate_even`：iterate_even (hf : Involutive f) (hn :
 Even n) : f^[n] = id
-/
lemma iterate_eq_id (hf : Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n :=
  ⟨fun H ↦ not_odd_iff_even.1 fun hn ↦ hne <| by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

end Involutive
end Function

section DistribNeg

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : ℕ}

/-
**neg_one_pow_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1 else (-1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1 else (-1) := by
  cases even_or_odd n with
  | inl h => rw [h.neg_one_pow, if_pos h]
  | inr h => rw [h.neg_one_pow, if_neg (by simpa using h)]
/-
**neg_one_pow_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_congr (h : Even m ↔ Even n) : (-1 : R) ^ m = (-1) ^ n
参数：h : Even m ↔ Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_one_pow_eq_ite`：neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1
 else (-1)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_one_pow_congr (h : Even m ↔ Even n) : (-1 : R) ^ m = (-1) ^ n := by
  simp [h, neg_one_pow_eq_ite]
/-
**neg_one_pow_eq_one_iff_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_eq_one_iff_even (h : (-1 : R) != 1) : (-1 : R) ^ n = 1 ↔ Even 
n
参数：h : (-1 : R) != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_one_pow_eq_ite`：neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1
 else (-1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) :
    (-1 : R) ^ n = 1 ↔ Even n := by simp [neg_one_pow_eq_ite, h]
/-
**neg_one_pow_eq_neg_one_iff_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_eq_neg_one_iff_odd (h : (-1 : R) != 1) : (-1 : R) ^ n = -1 ↔ O
dd n
参数：h : (-1 : R) != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_one_pow_eq_ite`：neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1
 else (-1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma neg_one_pow_eq_neg_one_iff_odd (h : (-1 : R) ≠ 1) :
    (-1 : R) ^ n = -1 ↔ Odd n := by simp [neg_one_pow_eq_ite, h.symm]

end DistribNeg

section DivisionMonoid
variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

/-
**Even.neg_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.neg_zpow : Even n -> forall a : α, (-a) ^ n = a ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_two`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 2 = a * 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]
/-
**Even.neg_one_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1
参数：h : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Even.neg_zpow`：Even.neg_zpow : Even n -> forall a : α, (-a) ^ n = a ^ n
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
-/
lemma Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
/-
**neg_one_zpow_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_zpow_eq_ite : (-1 : α) ^ n = if Even n then 1 else -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `neg_one_pow_eq_ite`：neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1
 else (-1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma neg_one_zpow_eq_ite : (-1 : α) ^ n = if Even n then 1 else -1 := by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [neg_one_pow_eq_ite]))

end DivisionMonoid

section CharTwo

-- We state the following theorems in terms of the slightly more general `2 = 0` hypothesis.

variable {R : Type*} [AddMonoidWithOne R]

/-
**natCast_eq_zero_or_one_of_two_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem natCast_eq_zero_or_one_of_two_eq_zero' (n : ℕ) (h : (2 : R) = 0) :
    (Even n → (n : R) = 0) ∧ (Odd n → (n : R) = 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ _ => simpa [add_assoc, Nat.even_add_one, Nat.odd_add_one, h]
/-
**natCast_eq_zero_of_even_of_two_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：natCast_eq_zero_of_even_of_two_eq_zero {n : Nat} (hn : Even n) (h : (2 : R
) = 0) : (n : R) = 0
参数：hn : Even n；h : (2 : R) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.Algebra.Ring.Parity.0.natCast_eq_zero_or_one_of_two_eq_
zero'`：∀ {R : Type u_4} [inst : AddMonoidWithOne R] (n : ℕ), 2 = 0 → (Even n → ↑
n = 0) ∧ (Odd n → ↑n = 1)
-/
theorem natCast_eq_zero_of_even_of_two_eq_zero {n : ℕ} (hn : Even n) (h : (2 : R) = 0) :
    (n : R) = 0 :=
  (natCast_eq_zero_or_one_of_two_eq_zero' n h).1 hn
/-
**natCast_eq_one_of_odd_of_two_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：natCast_eq_one_of_odd_of_two_eq_zero {n : Nat} (hn : Odd n) (h : (2 : R) =
 0) : (n : R) = 1
参数：hn : Odd n；h : (2 : R) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.Ring.Parity.0.natCast_eq_zero_or_one_of_two_eq_
zero'`：∀ {R : Type u_4} [inst : AddMonoidWithOne R] (n : ℕ), 2 = 0 → (Even n → ↑
n = 0) ∧ (Odd n → ↑n = 1)
-/
theorem natCast_eq_one_of_odd_of_two_eq_zero {n : ℕ} (hn : Odd n) (h : (2 : R) = 0) :
    (n : R) = 1 :=
  (natCast_eq_zero_or_one_of_two_eq_zero' n h).2 hn
/-
**natCast_eq_zero_or_one_of_two_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：natCast_eq_zero_or_one_of_two_eq_zero (n : Nat) (h : (2 : R) = 0) : (n : R
) = 0 ∨ (n : R) = 1
参数：n : Nat；h : (2 : R) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `natCast_eq_zero_of_even_of_two_eq_zero`：natCast_eq_zero_of_even_of_two_e
q_zero {n : Nat} (hn : Even n) (h : (2 : R) = 0) : (n : R) = 0
· 使用定理 `natCast_eq_one_of_odd_of_two_eq_zero`：natCast_eq_one_of_odd_of_two_eq_ze
ro {n : Nat} (hn : Odd n) (h : (2 : R) = 0) : (n : R) = 1
-/
theorem natCast_eq_zero_or_one_of_two_eq_zero (n : ℕ) (h : (2 : R) = 0) :
    (n : R) = 0 ∨ (n : R) = 1 := by
  obtain hn | hn := Nat.even_or_odd n
  · exact Or.inl <| natCast_eq_zero_of_even_of_two_eq_zero hn h
  · exact Or.inr <| natCast_eq_one_of_odd_of_two_eq_zero hn h

end CharTwo

