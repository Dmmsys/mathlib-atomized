/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Lemmas about divisibility in rings

## Main results:
* `dvd_smul_of_dvd`: stating that `x ∣ y → x ∣ m • y` for any scalar `m`.
* `Commute.pow_dvd_add_pow_of_pow_eq_zero_right`: stating that if `y` is nilpotent then
  `x ^ m ∣ (x + y) ^ p` for sufficiently large `p` (together with many variations for convenience).
-/

public section

variable {R : Type*}

/-
**dvd_smul_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R]
 {x y : R} (m : M) (h : x ∣ y) : x ∣ m • y
参数：m : M；h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R] {x y : R}
    (m : M) (h : x ∣ y) : x ∣ m • y :=
  let ⟨k, hk⟩ := h; ⟨m • k, by rw [mul_smul_comm, ← hk]⟩
/-
**dvd_nsmul_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : Nat) (h : x ∣ y) : x
 ∣ n • y
参数：n : Nat；h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dvd_smul_of_dvd`：dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [S
MulCommClass M R R] {x y : R} (m : M) (h : x ∣ y) : x ∣ m • y
-/
lemma dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : ℕ) (h : x ∣ y) : x ∣ n • y :=
  dvd_smul_of_dvd n h
/-
**dvd_zsmul_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_zsmul_of_dvd [NonUnitalRing R] {x y : R} (z : Int) (h : x ∣ y) : x ∣ z
 • y
参数：z : Int；h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dvd_smul_of_dvd`：dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [S
MulCommClass M R R] {x y : R} (m : M) (h : x ∣ y) : x ∣ m • y
-/
lemma dvd_zsmul_of_dvd [NonUnitalRing R] {x y : R} (z : ℤ) (h : x ∣ y) : x ∣ z • y :=
  dvd_smul_of_dvd z h

namespace Commute

variable {x y : R} {n m p : ℕ}

section Semiring

variable [Semiring R]

/-
**Commute.pow_dvd_add_pow_of_pow_eq_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Commut
e`。
形式化陈述：pow_dvd_add_pow_of_pow_eq_zero_right (hp : n + m <= p + 1) (h_comm : Commu
te x y) (hy : y ^ n = 0) : x ^ m ∣ (x + y) ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；hy : y ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.add_pow'`：add_pow' (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑
 m in antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2)
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用引理 `dvd_nsmul_of_dvd`：dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : 
Nat) (h : x ∣ y) : x ∣ n • y
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma pow_dvd_add_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x + y) ^ p := by
  rw [h_comm.add_pow']
  refine Finset.dvd_sum fun ⟨i, j⟩ hij ↦ ?_
  replace hij : i + j = p := by simpa using hij
  apply dvd_nsmul_of_dvd
  rcases le_or_gt m i with (hi : m ≤ i) | (hi : i + 1 ≤ m)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow x hi) _
  · simp [pow_eq_zero_of_le (by lia : n ≤ j) hy]
/-
**Commute.pow_dvd_add_pow_of_pow_eq_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Commute
`。
形式化陈述：pow_dvd_add_pow_of_pow_eq_zero_left (hp : n + m <= p + 1) (h_comm : Commut
e x y) (hx : x ^ n = 0) : y ^ m ∣ (x + y) ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；hx : x ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.pow_dvd_add_pow_of_pow_eq_zero_right`：pow_dvd_add_pow_of_pow_eq_
zero_right (hp : n + m <= p + 1) (h_comm : Commute x y) (hy : y ^ n = 0) : x ^ m
 ∣ (x + y) ^ p
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma pow_dvd_add_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x + y) ^ p :=
  add_comm x y ▸ h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right hp hx

end Semiring

section Ring

variable [Ring R]

/-
**Commute.pow_dvd_pow_of_sub_pow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：pow_dvd_pow_of_sub_pow_eq_zero (hp : n + m <= p + 1) (h_comm : Commute x y
) (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；h : (x - y) ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `Commute.pow_dvd_add_pow_of_pow_eq_zero_left`：pow_dvd_add_pow_of_pow_eq_z
ero_left (hp : n + m <= p + 1) (h_comm : Commute x y) (hx : x ^ n = 0) : y ^ m ∣
 (x + y) ^ p
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma pow_dvd_pow_of_sub_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← sub_add_cancel y x]
  apply (h_comm.symm.sub_left rfl).pow_dvd_add_pow_of_pow_eq_zero_left hp _
  rw [← neg_sub x y, neg_pow, h, mul_zero]
/-
**Commute.pow_dvd_pow_of_add_pow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：pow_dvd_pow_of_add_pow_eq_zero (hp : n + m <= p + 1) (h_comm : Commute x y
) (h : (x + y) ^ n = 0) : x ^ m ∣ y ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；h : (x + y) ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `neg_pow'`：neg_pow' (a : R) (n : Nat) : (-a) ^ n = a ^ n * (-1) ^ n
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用引理 `Commute.pow_dvd_pow_of_sub_pow_eq_zero`：pow_dvd_pow_of_sub_pow_eq_zero (
hp : n + m <= p + 1) (h_comm : Commute x y) (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ 
p
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
lemma pow_dvd_pow_of_add_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x + y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← neg_neg y, neg_pow']
  apply dvd_mul_of_dvd_left
  apply h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero hp
  simpa
/-
**Commute.pow_dvd_sub_pow_of_pow_eq_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Commut
e`。
形式化陈述：pow_dvd_sub_pow_of_pow_eq_zero_right (hp : n + m <= p + 1) (h_comm : Commu
te x y) (hy : y ^ n = 0) : x ^ m ∣ (x - y) ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；hy : y ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.pow_dvd_pow_of_sub_pow_eq_zero`：pow_dvd_pow_of_sub_pow_eq_zero (
hp : n + m <= p + 1) (h_comm : Commute x y) (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ 
p
· 使用定理 `Commute.sub_right`：sub_right : Commute a b -> Commute a c -> Commute a (
b - c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
lemma pow_dvd_sub_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x - y) ^ p :=
  (sub_right rfl h_comm).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)
/-
**Commute.pow_dvd_sub_pow_of_pow_eq_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Commute
`。
形式化陈述：pow_dvd_sub_pow_of_pow_eq_zero_left (hp : n + m <= p + 1) (h_comm : Commut
e x y) (hx : x ^ n = 0) : y ^ m ∣ (x - y) ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；hx : x ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `neg_pow'`：neg_pow' (a : R) (n : Nat) : (-a) ^ n = a ^ n * (-1) ^ n
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用引理 `Commute.pow_dvd_sub_pow_of_pow_eq_zero_right`：pow_dvd_sub_pow_of_pow_eq_
zero_right (hp : n + m <= p + 1) (h_comm : Commute x y) (hy : y ^ n = 0) : x ^ m
 ∣ (x - y) ^ p
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
lemma pow_dvd_sub_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x - y) ^ p := by
  rw [← neg_sub y x, neg_pow']
  apply dvd_mul_of_dvd_left
  exact h_comm.symm.pow_dvd_sub_pow_of_pow_eq_zero_right hp hx
/-
**Commute.add_pow_dvd_pow_of_pow_eq_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Commut
e`。
形式化陈述：add_pow_dvd_pow_of_pow_eq_zero_right (hp : n + m <= p + 1) (h_comm : Commu
te x y) (hx : x ^ n = 0) : (x + y) ^ m ∣ y ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；hx : x ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.pow_dvd_pow_of_sub_pow_eq_zero`：pow_dvd_pow_of_sub_pow_eq_zero (
hp : n + m <= p + 1) (h_comm : Commute x y) (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ 
p
· 使用定理 `Commute.add_left`：add_left [Distrib R] {a b c : R} : Commute a c -> Comm
ute b c -> Commute (a + b) c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
lemma add_pow_dvd_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : (x + y) ^ m ∣ y ^ p :=
  (h_comm.add_left rfl).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)
/-
**Commute.add_pow_dvd_pow_of_pow_eq_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Commute
`。
形式化陈述：add_pow_dvd_pow_of_pow_eq_zero_left (hp : n + m <= p + 1) (h_comm : Commut
e x y) (hy : y ^ n = 0) : (x + y) ^ m ∣ x ^ p
参数：hp : n + m <= p + 1；h_comm : Commute x y；hy : y ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.add_pow_dvd_pow_of_pow_eq_zero_right`：add_pow_dvd_pow_of_pow_eq_
zero_right (hp : n + m <= p + 1) (h_comm : Commute x y) (hx : x ^ n = 0) : (x + 
y) ^ m ∣ y ^ p
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma add_pow_dvd_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : (x + y) ^ m ∣ x ^ p :=
  add_comm x y ▸ h_comm.symm.add_pow_dvd_pow_of_pow_eq_zero_right hp hy

end Ring

end Commute
section CommRing

variable [CommRing R]

/-
**dvd_mul_sub_mul_mul_left_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_mul_sub_mul_mul_left_of_dvd {p a b c d x y : R} (h1 : p ∣ a * x + b * 
y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * x
参数：h1 : p ∣ a * x + b * y；h2 : p ∣ c * x + d * y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dvd_mul_sub_mul_mul_left_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * x := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨d * k1 - b * k2, ?_⟩
  grind
/-
**dvd_mul_sub_mul_mul_right_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_mul_sub_mul_mul_right_of_dvd {p a b c d x y : R} (h1 : p ∣ a * x + b *
 y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * y
参数：h1 : p ∣ a * x + b * y；h2 : p ∣ c * x + d * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dvd_mul_sub_mul_mul_left_of_dvd`：dvd_mul_sub_mul_mul_left_of_dvd {p a b 
c d x y : R} (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b 
* c) * x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma dvd_mul_sub_mul_mul_right_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * y :=
  (mul_comm a _ ▸ mul_comm c _ ▸ dvd_mul_sub_mul_mul_left_of_dvd
    (add_comm (c * x) _ ▸ h2) (add_comm (a * x) _ ▸ h1))
/-
**dvd_mul_sub_mul_mul_gcd_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_mul_sub_mul_mul_gcd_of_dvd {p a b c d x y : R} [GCDMonoid R] (h1 : p ∣
 a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * gcd x y
参数：h1 : p ∣ a * x + b * y；h2 : p ∣ c * x + d * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associated.dvd_iff_dvd_right`：Associated.dvd_iff_dvd_right [Monoid M] {a
 b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c
· 使用定理 `gcd_mul_left'`：gcd_mul_left' [GCDMonoid α] (a b c : α) : Associated (gcd
 (a * b) (a * c)) (a * gcd b c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_gcd_iff`：dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b
 ∧ a ∣ c
· 使用引理 `dvd_mul_sub_mul_mul_left_of_dvd`：dvd_mul_sub_mul_mul_left_of_dvd {p a b 
c d x y : R} (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b 
* c) * x
· 使用引理 `dvd_mul_sub_mul_mul_right_of_dvd`：dvd_mul_sub_mul_mul_right_of_dvd {p a 
b c d x y : R} (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - 
b * c) * y
-/
lemma dvd_mul_sub_mul_mul_gcd_of_dvd {p a b c d x y : R} [GCDMonoid R]
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * gcd x y := by
  rw [← (gcd_mul_left' (a * d - b * c) x y).dvd_iff_dvd_right]
  exact (dvd_gcd_iff _ _ _).2 ⟨dvd_mul_sub_mul_mul_left_of_dvd h1 h2,
    dvd_mul_sub_mul_mul_right_of_dvd h1 h2⟩

end CommRing

section misc

variable [Ring R] [LinearOrder R] {x y : R}

@[simp]
/-
**associated_abs_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associated_abs_left_iff : Associated |x| y ↔ Associated x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem associated_abs_left_iff :
    Associated |x| y ↔ Associated x y := by
  obtain h | h := abs_choice x <;>
  simp [h]

@[simp]
/-
**associated_abs_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associated_abs_right_iff : Associated x |y| ↔ Associated x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associated.comm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y ↔ Associated y x
· 使用定理 `associated_abs_left_iff`：associated_abs_left_iff : Associated |x| y ↔ As
sociated x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem associated_abs_right_iff :
    Associated x |y| ↔ Associated x y := by
  rw [Associated.comm, associated_abs_left_iff, Associated.comm]

alias ⟨_, Associated.abs_left⟩ := associated_abs_left_iff

alias ⟨_, Associated.abs_right⟩ := associated_abs_right_iff

end misc

