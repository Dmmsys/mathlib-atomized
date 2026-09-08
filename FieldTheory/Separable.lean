/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.PowerBasis

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `Polynomial.Separable f`: a polynomial `f` is separable iff it is coprime with its derivative.
* `IsSeparable K x`: an element `x` is separable over `K` iff the minimal polynomial of `x`
  over `K` is separable.
* `Algebra.IsSeparable K L`: `L` is separable over `K` iff every element in `L` is separable
  over `K`.

-/

@[expose] public section


universe u v w

open Polynomial Finset

namespace Polynomial

section CommSemiring

variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
@[stacks 09H1 "first part"]
/-
**Polynomial.Separable** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：Separable (f : R[X]) : Prop
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial is separable iff it is coprime with its derivative.
-/
def Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)
/-
**Polynomial.separable_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_def (f : R[X]) : f.Separable ↔ IsCoprime f (derivative f)
参数：f : R[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem separable_def (f : R[X]) : f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl
/-
**Polynomial.separable_def'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_def' (f : R[X]) : f.Separable ↔ exists a b : R[X], a * f + b * (
derivative f) = 1
参数：f : R[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem separable_def' (f : R[X]) : f.Separable ↔ ∃ a b : R[X], a * f + b * (derivative f) = 1 :=
  Iff.rfl
/-
**Polynomial.not_separable_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_separable_zero [Nontrivial R] : ¬Separable (0 : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.derivative_zero`：derivative_zero : derivative (0 : R[X]) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem not_separable_zero [Nontrivial R] : ¬Separable (0 : R[X]) := by
  rintro ⟨x, y, h⟩
  simp only [derivative_zero, mul_zero, add_zero, zero_ne_one] at h
/-
**Polynomial.Separable.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [Nontrivial R] {f : Polynomial R}, 
f.Separable → f ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.not_separable_zero`：not_separable_zero [Nontrivial R] : ¬Sepa
rable (0 : R[X])
-/
theorem Separable.ne_zero [Nontrivial R] {f : R[X]} (h : f.Separable) : f ≠ 0 :=
  (not_separable_zero <| · ▸ h)

@[simp]
/-
**Polynomial.separable_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_one : (1 : R[X]).Separable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
-/
theorem separable_one : (1 : R[X]).Separable :=
  isCoprime_one_left

@[nontriviality]
/-
**Polynomial.separable_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_of_subsingleton [Subsingleton R] (f : R[X]) : f.Separable
参数：f : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem separable_of_subsingleton [Subsingleton R] (f : R[X]) : f.Separable := by
  simp [Separable, IsCoprime, eq_iff_true_of_subsingleton]
/-
**Polynomial.separable_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_X_add_C (a : R) : (X + C a).Separable
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `Polynomial.derivative_add`：derivative_add {f g : R[X]} : derivative (f +
 g) = derivative f + derivative g
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `isCoprime_one_right`：isCoprime_one_right : IsCoprime x 1
-/
theorem separable_X_add_C (a : R) : (X + C a).Separable := by
  rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero]
  exact isCoprime_one_right
/-
**Polynomial.separable_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_X : (X : R[X]).Separable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `isCoprime_one_right`：isCoprime_one_right : IsCoprime x 1
-/
theorem separable_X : (X : R[X]).Separable := by
  rw [separable_def, derivative_X]
  exact isCoprime_one_right
/-
**Polynomial.separable_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_C (r : R) : (C r).Separable ↔ IsUnit r
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `isCoprime_zero_right`：isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem separable_C (r : R) : (C r).Separable ↔ IsUnit r := by
  rw [separable_def, derivative_C, isCoprime_zero_right, isUnit_C]
/-
**Polynomial.Separable.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separab
le`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R}, (f * g).Separ
able → f.Separable
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_left_left`：IsCoprime.of_mul_left_left (H : IsCoprime (x
 * y) z) : IsCoprime x z
· 使用定理 `IsCoprime.of_mul_right_left`：IsCoprime.of_mul_right_left (H : IsCoprime 
x (y * z)) : IsCoprime x y
· 使用定理 `IsCoprime.of_add_mul_left_right`：IsCoprime.of_add_mul_left_right (h : Is
Coprime x (y + x * z)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
-/
theorem Separable.of_mul_left {f g : R[X]} (h : (f * g).Separable) : f.Separable := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_left (IsCoprime.of_add_mul_left_right this)
/-
**Polynomial.Separable.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separa
ble`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R}, (f * g).Separ
able → g.Separable
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_mul_left`：∀ {R : Type u} [inst : CommSemiring R]
 {f g : Polynomial R}, (f * g).Separable → f.Separable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Separable.of_mul_right {f g : R[X]} (h : (f * g).Separable) : g.Separable := by
  rw [mul_comm] at h
  exact h.of_mul_left
/-
**Polynomial.Separable.of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R}, f.Separable →
 g ∣ f → g.Separable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_mul_left`：∀ {R : Type u} [inst : CommSemiring R]
 {f g : Polynomial R}, (f * g).Separable → f.Separable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Separable.of_dvd {f g : R[X]} (hf : f.Separable) (hfg : g ∣ f) : g.Separable := by
  rcases hfg with ⟨f', rfl⟩
  exact Separable.of_mul_left hf
/-
**Polynomial.separable_gcd_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_gcd_left {F : Type*} [Field F] [DecidableEq F[X]] {f : F[X]} (hf
 : f.Separable) (g : F[X]) : (EuclideanDomain.gcd f g).Separable
参数：hf : f.Separable；g : F[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `EuclideanDomain.gcd_dvd_left`：gcd_dvd_left (a b : R) : gcd a b ∣ a
-/
theorem separable_gcd_left {F : Type*} [Field F] [DecidableEq F[X]]
    {f : F[X]} (hf : f.Separable) (g : F[X]) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)
/-
**Polynomial.separable_gcd_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_gcd_right {F : Type*} [Field F] [DecidableEq F[X]] {g : F[X]} (f
 : F[X]) (hg : g.Separable) : (EuclideanDomain.gcd f g).Separable
参数：f : F[X]；hg : g.Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `EuclideanDomain.gcd_dvd_right`：gcd_dvd_right (a b : R) : gcd a b ∣ b
-/
theorem separable_gcd_right {F : Type*} [Field F] [DecidableEq F[X]]
    {g : F[X]} (f : F[X]) (hg : g.Separable) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)
/-
**Polynomial.Separable.isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable
`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R}, (f * g).Separ
able → IsCoprime f g
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_left_left`：IsCoprime.of_mul_left_left (H : IsCoprime (x
 * y) z) : IsCoprime x z
· 使用定理 `IsCoprime.of_mul_right_right`：IsCoprime.of_mul_right_right (H : IsCoprim
e x (y * z)) : IsCoprime x z
· 使用定理 `IsCoprime.of_add_mul_left_right`：IsCoprime.of_add_mul_left_right (h : Is
Coprime x (y + x * z)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
-/
theorem Separable.isCoprime {f g : R[X]} (h : (f * g).Separable) : IsCoprime f g := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_right (IsCoprime.of_add_mul_left_right this)
/-
**Polynomial.Separable.of_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f : Polynomial R} {n : ℕ},   (f ^ 
n).Separable → IsUnit f ∨ f.Separable ∧ n = 1 ∨ n = 0
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_self`：isCoprime_self : IsCoprime x x ↔ IsUnit x
· 使用定理 `IsCoprime.of_mul_left_right`：IsCoprime.of_mul_left_right (H : IsCoprime 
(x * y) z) : IsCoprime y z
· 使用定理 `Polynomial.Separable.isCoprime`：∀ {R : Type u} [inst : CommSemiring R] {
f g : Polynomial R}, (f * g).Separable → IsCoprime f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem Separable.of_pow' {f : R[X]} :
    ∀ {n : ℕ} (_h : (f ^ n).Separable), IsUnit f ∨ f.Separable ∧ n = 1 ∨ n = 0
  | 0 => fun _h => Or.inr <| Or.inr rfl
  | 1 => fun h => Or.inr <| Or.inl ⟨pow_one f ▸ h, rfl⟩
  | n + 2 => fun h => by
    rw [pow_succ, pow_succ] at h
    exact Or.inl (isCoprime_self.1 h.isCoprime.of_mul_left_right)
/-
**Polynomial.Separable.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f : Polynomial R},   ¬IsUnit f → ∀
 {n : ℕ}, n ≠ 0 → (f ^ n).Separable → f.Separable ∧ n = 1
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Polynomial.Separable.of_pow'`：∀ {R : Type u} [inst : CommSemiring R] {f 
: Polynomial R} {n : ℕ},   (f ^ n).Separable → IsUnit f ∨ f.Separable ∧ n = 1 ∨ 
n = 0
-/
theorem Separable.of_pow {f : R[X]} (hf : ¬IsUnit f) {n : ℕ} (hn : n ≠ 0)
    (hfs : (f ^ n).Separable) : f.Separable ∧ n = 1 :=
  (hfs.of_pow'.resolve_left hf).resolve_right hn
/-
**Polynomial.Separable.map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {S : Type v} [inst_1 : CommSemiring
 S] {p : Polynomial R},   p.Separable → ∀ {f : R →+* S}, (Polynomial.map f p).Se
parable
参数：Polynomial.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
-/
theorem Separable.map {p : R[X]} (h : p.Separable) {f : R →+* S} : (p.map f).Separable :=
  let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f, by
    rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, H,
      Polynomial.map_one]⟩
/-
**Polynomial._root_.Associated.separable** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.separable {f g : R[X]}
    (ha : Associated f g) (h : f.Separable) : g.Separable := by
  grind [Separable.of_dvd, Associated.dvd']
/-
**Polynomial._root_.Associated.separable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.separable_iff {f g : R[X]}
    (ha : Associated f g) : f.Separable ↔ g.Separable := ⟨ha.separable, ha.symm.separable⟩
/-
**Polynomial.Separable.mul_unit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`
。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R}, f.Separable →
 IsUnit g → (f * g).Separable
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.separable`：∀ {R : Type u} [inst : CommSemiring R] {f g : Poly
nomial R}, Associated f g → f.Separable → g.Separable
· 使用定理 `associated_mul_unit_right`：associated_mul_unit_right {N : Type*} [Monoid
 N] (a u : N) (hu : IsUnit u) : Associated a (a * u)
-/
theorem Separable.mul_unit {f g : R[X]} (hf : f.Separable) (hg : IsUnit g) : (f * g).Separable :=
  (associated_mul_unit_right f g hg).separable hf
/-
**Polynomial.Separable.unit_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`
。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R}, IsUnit f → g.
Separable → (f * g).Separable
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.separable`：∀ {R : Type u} [inst : CommSemiring R] {f g : Poly
nomial R}, Associated f g → f.Separable → g.Separable
· 使用定理 `associated_unit_mul_right`：associated_unit_mul_right {N : Type*} [CommMo
noid N] (a u : N) (hu : IsUnit u) : Associated a (u * a)
-/
theorem Separable.unit_mul {f g : R[X]} (hf : IsUnit f) (hg : g.Separable) : (f * g).Separable :=
  (associated_unit_mul_right g f hf).separable hg
/-
**Polynomial.Separable.eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Separable.eval₂_derivative_ne_zero [Nontrivial S] (f : R →+* S) {p : R[X]}
    (h : p.Separable) {x : S} (hx : p.eval₂ f x = 0) :
    (derivative p).eval₂ f x ≠ 0 := by
  intro hx'
  obtain ⟨a, b, e⟩ := h
  apply_fun Polynomial.eval₂ f x at e
  simp only [eval₂_add, eval₂_mul, hx, mul_zero, hx', add_zero, eval₂_one, zero_ne_one] at e
/-
**Polynomial.Separable.aeval_derivative_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {S : Type v} [inst_1 : CommSemiring
 S] [Nontrivial S] [inst_3 : Algebra R S]   {p : Polynomial R},   p.Separable → 
∀ {x : S}, (Polynomial.aeval x) p = 0 → (Polynomial.aeval x) (Polynomial.derivat
ive p) ≠ 0
参数：Polynomial.aeval x；Polynomial.aeval x；Polynomial.derivative p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.eval₂_derivative_ne_zero`：∀ {R : Type u} [inst : Co
mmSemiring R] {S : Type v} [inst_1 : CommSemiring S] [Nontrivial S] (f : R →+* S
)   {p : Polynomial R},   p.Separab…
-/
theorem Separable.aeval_derivative_ne_zero [Nontrivial S] [Algebra R S] {p : R[X]}
    (h : p.Separable) {x : S} (hx : aeval x p = 0) :
    aeval x (derivative p) ≠ 0 :=
  h.eval₂_derivative_ne_zero (algebraMap R S) hx

variable (p q : ℕ)
/-
**Polynomial.isUnit_of_self_mul_dvd_separable** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：isUnit_of_self_mul_dvd_separable {p q : R[X]} (hp : p.Separable) (hq : q *
 q ∣ p) : IsUnit q
参数：hp : p.Separable；hq : q * q ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_self`：isCoprime_self : IsCoprime x x ↔ IsUnit x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 32 条，此处仅展示前 30 条）
-/
theorem isUnit_of_self_mul_dvd_separable {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p) :
    IsUnit q := by
  obtain ⟨p, rfl⟩ := hq
  apply isCoprime_self.mp
  have : IsCoprime (q * (q * p))
      (q * (derivative q * p + derivative q * p + q * derivative p)) := by
    simp only [← mul_assoc, mul_add]
    dsimp only [Separable] at hp
    convert! hp using 1
    rw [derivative_mul, derivative_mul]
    ring
  exact IsCoprime.of_mul_right_left (IsCoprime.of_mul_left_left this)
/-
**Polynomial.emultiplicity_le_one_of_separable** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：emultiplicity_le_one_of_separable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Se
parable p) : emultiplicity q p <= 1
参数：hq : ¬IsUnit q；hsep : Separable p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.isUnit_of_self_mul_dvd_separable`：isUnit_of_self_mul_dvd_sepa
rable {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p) : IsUnit q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
-/
theorem emultiplicity_le_one_of_separable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) :
    emultiplicity q p ≤ 1 := by
  contrapose! hq
  apply isUnit_of_self_mul_dvd_separable hsep
  rw [← sq]
  apply pow_dvd_of_le_emultiplicity
  exact Order.add_one_le_of_lt hq

/-- A separable polynomial is square-free.

See `PerfectField.separable_iff_squarefree` for the converse when the coefficients are a perfect
field. -/
/-
**Polynomial.Separable.squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separabl
e`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {p : Polynomial R}, p.Separable → S
quarefree p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `squarefree_iff_emultiplicity_le_one`：squarefree_iff_emultiplicity_le_one
 [CommMonoid R] (r : R) : Squarefree r ↔ forall x : R, emultiplicity x r <= 1 ∨ 
IsUnit x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Polynomial.emultiplicity_le_one_of_separable`：emultiplicity_le_one_of_se
parable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) : emultiplicity q p <
= 1

--- 原说明 ---
A separable polynomial is square-free.

See `PerfectField.separable_iff_squarefree` for the converse when the coefficien
ts are a perfect
field.
-/
theorem Separable.squarefree {p : R[X]} (hsep : Separable p) : Squarefree p := by
  rw [squarefree_iff_emultiplicity_le_one p]
  exact fun f => or_iff_not_imp_right.mpr fun hunit => emultiplicity_le_one_of_separable hunit hsep

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-
**Polynomial.separable_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_X_sub_C {x : R} : Separable (X - C x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.separable_X_add_C`：separable_X_add_C (a : R) : (X + C a).Sepa
rable
-/
theorem separable_X_sub_C {x : R} : Separable (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)
/-
**Polynomial.Separable.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {f g : Polynomial R}, f.Separable → g.S
eparable → IsCoprime f g → (f * g).Separable
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `IsCoprime.mul_left`：IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCopr
ime y z) : IsCoprime (x * y) z
· 使用定理 `IsCoprime.add_mul_left_right`：add_mul_left_right {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime x (y + x * z)
· 使用定理 `IsCoprime.mul_right`：IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCo
prime x z) : IsCoprime x (y * z)
· 使用定理 `IsCoprime.mul_add_right_right`：mul_add_right_right {x y : R} (h : IsCopr
ime x y) (z : R) : IsCoprime x (z * x + y)
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
-/
theorem Separable.mul {f g : R[X]} (hf : f.Separable) (hg : g.Separable) (h : IsCoprime f g) :
    (f * g).Separable := by
  rw [separable_def, derivative_mul]
  exact
    ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)
/-
**Polynomial.separable_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_prod' {ι : Sort _} {f : ι -> R[X]} {s : Finset ι} : (forall x in
 s, forall y in s, x != y -> IsCoprime (f x) (f y)) -> (forall x in s, (f x).Sep
arable) -> (∏ x in s, f x).Separable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Polynomial.separable_one`：separable_one : (1 : R[X]).Separable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Polynomial.Separable.mul`：∀ {R : Type u} [inst : CommRing R] {f g : Poly
nomial R}, f.Separable → g.Separable → IsCoprime f g → (f * g).Separable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCoprime.prod_right`：IsCoprime.prod_right : (forall i in t, IsCoprime x
 (s i)) -> IsCoprime x (∏ i in t, s i)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem separable_prod' {ι : Sort _} {f : ι → R[X]} {s : Finset ι} :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsCoprime (f x) (f y)) →
      (∀ x ∈ s, (f x).Separable) → (∏ x ∈ s, f x).Separable := by
  classical
  exact Finset.induction_on s (fun _ _ => separable_one) fun a s has ih h1 h2 => by
    simp_rw [Finset.forall_mem_insert, forall_and] at h1 h2; rw [prod_insert has]
    exact
      h2.1.mul (ih h1.2.2 h2.2)
        (IsCoprime.prod_right fun i his => h1.1.2 i his <| Ne.symm <| ne_of_mem_of_not_mem his has)

open scoped Function in -- required for scoped `on` notation
/-
**Polynomial.separable_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_prod {ι : Sort _} [Fintype ι] {f : ι -> R[X]} (h1 : Pairwise (Is
Coprime on f)) (h2 : forall x, (f x).Separable) : (∏ x, f x).Separable
参数：h1 : Pairwise (IsCoprime on f)；h2 : forall x, (f x).Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.separable_prod'`：separable_prod' {ι : Sort _} {f : ι -> R[X]}
 {s : Finset ι} : (forall x in s, forall y in s, x != y -> IsCoprime (f x) (f y)
) -> (forall x i…
-/
theorem separable_prod {ι : Sort _} [Fintype ι] {f : ι → R[X]} (h1 : Pairwise (IsCoprime on f))
    (h2 : ∀ x, (f x).Separable) : (∏ x, f x).Separable :=
  separable_prod' (fun _x _hx _y _hy hxy => h1 hxy) fun x _hx => h2 x
/-
**Polynomial.Separable.inj_of_prod_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [Nontrivial R] {ι : Type u_1} {f : ι → 
R} {s : Finset ι},   (∏ i ∈ s, (Polynomial.X - Polynomial.C (f i))).Separable → 
∀ {x y : ι}, x ∈ s → y ∈ s → f x = f y → x = y
参数：∏ i ∈ s, (Polynomial.X - Polynomial.C (f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.Separable.of_pow`：∀ {R : Type u} [inst : CommSemiring R] {f :
 Polynomial R},   ¬IsUnit f → ∀ {n : ℕ}, n ≠ 0 → (f ^ n).Separable → f.Separable
 ∧ n = 1
· 使用定理 `Polynomial.not_isUnit_X_sub_C`：not_isUnit_X_sub_C [Nontrivial R] (r : R)
 : ¬IsUnit (X - C r)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Separable.of_mul_left`：∀ {R : Type u} [inst : CommSemiring R]
 {f g : Polynomial R}, (f * g).Separable → f.Separable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.mem_erase_of_ne_of_mem`：mem_erase_of_ne_of_mem : a != b -> a in s
 -> a in erase s b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem Separable.inj_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} {f : ι → R} {s : Finset ι}
    (hfs : (∏ i ∈ s, (X - C (f i))).Separable) {x y : ι} (hx : x ∈ s) (hy : y ∈ s)
    (hfxy : f x = f y) : x = y := by
  classical
  by_contra hxy
  rw [← insert_erase hx, prod_insert (notMem_erase _ _), ←
    insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy), prod_insert (notMem_erase _ _), ←
    mul_assoc, hfxy, ← sq] at hfs
  cases (hfs.of_mul_left.of_pow (not_isUnit_X_sub_C _) two_ne_zero).2
/-
**Polynomial.Separable.injective_of_prod_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.Separable`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [Nontrivial R] {ι : Type u_1} [inst_2 :
 Fintype ι] {f : ι → R},   (∏ i, (Polynomial.X - Polynomial.C (f i))).Separable 
→ Function.Injective f
参数：∏ i, (Polynomial.X - Polynomial.C (f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.inj_of_prod_X_sub_C`：∀ {R : Type u} [inst : CommRin
g R] [Nontrivial R] {ι : Type u_1} {f : ι → R} {s : Finset ι},   (∏ i ∈ s, (Poly
nomial.X - Polynomial.C (f i))…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem Separable.injective_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} [Fintype ι] {f : ι → R}
    (hfs : (∏ i, (X - C (f i))).Separable) : Function.Injective f := fun _x _y hfxy =>
  hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy
/-
**Polynomial.nodup_of_separable_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nodup_of_separable_prod [Nontrivial R] {s : Multiset R} (hs : Separable (M
ultiset.map (fun a => X - C a) s).prod) : s.Nodup
参数：hs : Separable (Multiset.map (fun a => X - C a) s).prod。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.nodup_iff_ne_cons_cons`：nodup_iff_ne_cons_cons {s : Multiset α}
 : s.Nodup ↔ forall a t, s != a ::ₘ a ::ₘ t
· 使用定理 `Polynomial.not_isUnit_X_sub_C`：not_isUnit_X_sub_C [Nontrivial R] (r : R)
 : ¬IsUnit (X - C r)
· 使用定理 `Polynomial.isUnit_of_self_mul_dvd_separable`：isUnit_of_self_mul_dvd_sepa
rable {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p) : IsUnit q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nodup_of_separable_prod [Nontrivial R] {s : Multiset R}
    (hs : Separable (Multiset.map (fun a => X - C a) s).prod) : s.Nodup := by
  rw [Multiset.nodup_iff_ne_cons_cons]
  rintro a t rfl
  refine not_isUnit_X_sub_C a (isUnit_of_self_mul_dvd_separable hs ?_)
  simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)

/-- If `IsUnit n` in a `CommRing R`, then `X ^ n - u` is separable for any unit `u`. -/
/-
**Polynomial.separable_X_pow_sub_C_unit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_X_pow_sub_C_unit {n : Nat} (u : Rˣ) (hn : IsUnit (n : R)) : Sepa
rable (X ^ n - C (u : R))
参数：u : Rˣ；hn : IsUnit (n : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.separable_def'`：separable_def' (f : R[X]) : f.Separable ↔ exi
sts a b : R[X], a * f + b * (derivative f) = 1
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.derivative_pow`：derivative_pow (p : R[X]) (n : Nat) : derivat
ive (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If `IsUnit n` in a `CommRing R`, then `X ^ n - u` is separable for any unit `u`.
-/
theorem separable_X_pow_sub_C_unit {n : ℕ} (u : Rˣ) (hn : IsUnit (n : R)) :
    Separable (X ^ n - C (u : R)) := by
  nontriviality R
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp at hn
  apply (separable_def' (X ^ n - C (u : R))).2
  obtain ⟨n', hn'⟩ := hn.exists_left_inv
  refine ⟨-C ↑u⁻¹, C (↑u⁻¹ : R) * C n' * X, ?_⟩
  rw [derivative_sub, derivative_C, sub_zero, derivative_pow X n, derivative_X, mul_one]
  calc
    -C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1)) =
        C (↑u⁻¹ * ↑u) - C ↑u⁻¹ * X ^ n + C ↑u⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) := by
      simp only [C.map_mul, C_eq_natCast]
      ring
    _ = 1 := by
      simp only [Units.inv_mul, hn', C.map_one, mul_one, ← pow_succ',
        Nat.sub_add_cancel (show 1 ≤ n from hpos), sub_add_cancel]

/-- If `n = 0` in `R` and `b` is a unit, then `a * X ^ n + b * X + c` is separable. -/
/-
**Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：separable_C_mul_X_pow_add_C_mul_X_add_C {n : Nat} (a b c : R) (hn : (n : R
) = 0) (hb : IsUnit b) : (C a * X ^ n + C b * X + C c).Separable
参数：a b c : R；hn : (n : R) = 0；hb : IsUnit b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.derivative_X_pow`：derivative_X_pow (n : Nat) : derivative (X 
^ n : R[X]) = C (n : R) * X ^ (n - 1)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `n = 0` in `R` and `b` is a unit, then `a * X ^ n + b * X + c` is separable.
-/
theorem separable_C_mul_X_pow_add_C_mul_X_add_C
    {n : ℕ} (a b c : R) (hn : (n : R) = 0) (hb : IsUnit b) :
    (C a * X ^ n + C b * X + C c).Separable := by
  set f := C a * X ^ n + C b * X + C c
  obtain ⟨e, hb⟩ := hb.exists_left_inv
  refine ⟨-derivative f, f + C e, ?_⟩
  have hderiv : derivative f = C b := by
    simp [hn, f, map_add derivative, derivative_C, derivative_X_pow]
  rw [hderiv, right_distrib, ← add_assoc, neg_mul, mul_comm, neg_add_cancel, zero_add,
    ← map_mul, hb, map_one]

/-- If `R` is of characteristic `p`, `p ∣ n` and `b` is a unit,
then `a * X ^ n + b * X + c` is separable. -/
/-
**Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C'** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：separable_C_mul_X_pow_add_C_mul_X_add_C' (p n : Nat) (a b c : R) [CharP R 
p] (hn : p ∣ n) (hb : IsUnit b) : (C a * X ^ n + C b * X + C c).Separable
参数：p n : Nat；a b c : R；hn : p ∣ n；hb : IsUnit b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C`：separable_C_mul_X_po
w_add_C_mul_X_add_C {n : Nat} (a b c : R) (hn : (n : R) = 0) (hb : IsUnit b) : (
C a * X ^ n + C b * X + C c).Separable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x

--- 原说明 ---
If `R` is of characteristic `p`, `p ∣ n` and `b` is a unit,
then `a * X ^ n + b * X + c` is separable.
-/
theorem separable_C_mul_X_pow_add_C_mul_X_add_C'
    (p n : ℕ) (a b c : R) [CharP R p] (hn : p ∣ n) (hb : IsUnit b) :
    (C a * X ^ n + C b * X + C c).Separable :=
  separable_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff R p n).2 hn) hb
/-
**Polynomial.rootMultiplicity_le_one_of_separable** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：rootMultiplicity_le_one_of_separable [Nontrivial R] {p : R[X]} (hsep : Sep
arable p) (x : R) : rootMultiplicity x p <= 1
参数：hsep : Separable p；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
· 使用定理 `Polynomial.emultiplicity_le_one_of_separable`：emultiplicity_le_one_of_se
parable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) : emultiplicity q p <
= 1
· 使用定理 `Polynomial.not_isUnit_X_sub_C`：not_isUnit_X_sub_C [Nontrivial R] (r : R)
 : ¬IsUnit (X - C r)
-/
theorem rootMultiplicity_le_one_of_separable [Nontrivial R] {p : R[X]} (hsep : Separable p)
    (x : R) : rootMultiplicity x p ≤ 1 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [rootMultiplicity_eq_multiplicity, if_neg hp, ← Nat.cast_le (α := ℕ∞),
    Nat.cast_one, ← (finiteMultiplicity_X_sub_C x hp).emultiplicity_eq_multiplicity]
  apply emultiplicity_le_one_of_separable (not_isUnit_X_sub_C _) hsep

end CommRing

section IsDomain

variable {R : Type u} [CommRing R] [IsDomain R]

/-
**Polynomial.count_roots_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：count_roots_le_one [DecidableEq R] {p : R[X]} (hsep : Separable p) (x : R)
 : p.roots.count x <= 1
参数：hsep : Separable p；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.rootMultiplicity_le_one_of_separable`：rootMultiplicity_le_one
_of_separable [Nontrivial R] {p : R[X]} (hsep : Separable p) (x : R) : rootMulti
plicity x p <= 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem count_roots_le_one [DecidableEq R] {p : R[X]} (hsep : Separable p) (x : R) :
    p.roots.count x ≤ 1 := by
  rw [count_roots p]
  exact rootMultiplicity_le_one_of_separable hsep x
/-
**Polynomial.nodup_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nodup_roots {p : R[X]} (hsep : Separable p) : p.roots.Nodup
参数：hsep : Separable p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
· 使用定理 `Polynomial.count_roots_le_one`：count_roots_le_one [DecidableEq R] {p : R
[X]} (hsep : Separable p) (x : R) : p.roots.count x <= 1
-/
theorem nodup_roots {p : R[X]} (hsep : Separable p) : p.roots.Nodup := by
  classical
  exact Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

end IsDomain

section Field

variable {F : Type u} [Field F] {K : Type v} [Field K]

/-
**Polynomial.separable_iff_derivative_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：separable_iff_derivative_ne_zero {f : F[X]} (hf : Irreducible f) : f.Separ
able ↔ derivative f != 0
参数：hf : Irreducible f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_zero_right`：isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x
· 使用定理 `EuclideanDomain.isCoprime_of_dvd`：isCoprime_of_dvd {x y : α} (nonzero : 
¬(x = 0 ∧ y = 0)) (H : forall z in nonunits α, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCo
prime x y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_right_dvd`：mul_right_dvd : a * u ∣ b ↔ a ∣ b
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_derivative_lt`：natDegree_derivative_lt {p : R[X]} (
hp : p.natDegree != 0) : p.derivative.natDegree < p.natDegree
· 使用定理 `Polynomial.derivative_of_natDegree_zero`：derivative_of_natDegree_zero {p
 : R[X]} (hp : p.natDegree = 0) : derivative p = 0
-/
theorem separable_iff_derivative_ne_zero {f : F[X]} (hf : Irreducible f) :
    f.Separable ↔ derivative f ≠ 0 :=
  ⟨fun h1 h2 => hf.not_isUnit <| isCoprime_zero_right.1 <| h2 ▸ h1, fun h =>
    EuclideanDomain.isCoprime_of_dvd (mt And.right h) fun g hg1 _hg2 ⟨p, hg3⟩ hg4 =>
      let ⟨u, hu⟩ := (hf.isUnit_or_isUnit hg3).resolve_left hg1
      have : f ∣ derivative f := by
        conv_lhs => rw [hg3, ← hu]
        rwa [Units.mul_right_dvd]
      not_lt_of_ge (natDegree_le_of_dvd this h) <|
        natDegree_derivative_lt <| mt derivative_of_natDegree_zero h⟩

attribute [local instance] Ideal.Quotient.field in
/-
**Polynomial.separable_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_map {S} [CommRing S] [Nontrivial S] (f : F ->+* S) {p : F[X]} : 
(p.map f).Separable ↔ p.Separable
参数：f : F ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_maximal`：exists_maximal [Nontrivial α] : exists M : Ideal α
, M.IsMaximal
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isCoprime_map`：isCoprime_map [Field k] (f : R ->+* k) : IsCop
rime (p.map f) (q.map f) ↔ IsCoprime p q
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
-/
theorem separable_map {S} [CommRing S] [Nontrivial S] (f : F →+* S) {p : F[X]} :
    (p.map f).Separable ↔ p.Separable := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.map⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := Separable.map H (f := Ideal.Quotient.mk m)
  rwa [map_map, separable_def, derivative_map, isCoprime_map] at this
/-
**Polynomial.separable_prod_X_sub_C_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι -> F} {s : Finset ι} : (∏ 
i in s, (X - C (f i))).Separable ↔ forall x in s, forall y in s, f x = f y -> x 
= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.inj_of_prod_X_sub_C`：∀ {R : Type u} [inst : CommRin
g R] [Nontrivial R] {ι : Type u_1} {f : ι → R} {s : Finset ι},   (∏ i ∈ s, (Poly
nomial.X - Polynomial.C (f i))…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `Polynomial.separable_prod'`：separable_prod' {ι : Sort _} {f : ι -> R[X]}
 {s : Finset ι} : (forall x in s, forall y in s, x != y -> IsCoprime (f x) (f y)
) -> (forall x i…
· 使用定理 `Polynomial.pairwise_coprime_X_sub_C`：pairwise_coprime_X_sub_C {K} [Field
 K] {I : Type v} {s : I -> K} (H : Function.Injective s) : Pairwise (IsCoprime o
n fun i : I => X - C (s i…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Polynomial.separable_X_sub_C`：separable_X_sub_C {x : R} : Separable (X -
 C x)
-/
theorem separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι → F} {s : Finset ι} :
    (∏ i ∈ s, (X - C (f i))).Separable ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨fun hfs _ hx _ hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy, fun H => by
    rw [← prod_attach]
    exact
      separable_prod'
        (fun x _hx y _hy hxy =>
          @pairwise_coprime_X_sub_C _ _ { x // x ∈ s } (fun x => f x)
            (fun x y hxy => Subtype.ext <| H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
        fun _ _ => separable_X_sub_C⟩
/-
**Polynomial.separable_prod_X_sub_C_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_prod_X_sub_C_iff {ι : Sort _} [Fintype ι] {f : ι -> F} : (∏ i, (
X - C (f i))).Separable ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.separable_prod_X_sub_C_iff'`：separable_prod_X_sub_C_iff' {ι :
 Sort _} {f : ι -> F} {s : Finset ι} : (∏ i in s, (X - C (f i))).Separable ↔ for
all x in s, forall y in s, f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem separable_prod_X_sub_C_iff {ι : Sort _} [Fintype ι] {f : ι → F} :
    (∏ i, (X - C (f i))).Separable ↔ Function.Injective f :=
  separable_prod_X_sub_C_iff'.trans <| by simp_rw [mem_univ, true_imp_iff, Function.Injective]

section CharP

variable (p : ℕ) [HF : CharP F p]

/-
**Polynomial.separable_or** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_or {f : F[X]} (hf : Irreducible f) : f.Separable ∨ ¬f.Separable 
∧ exists g : F[X], Irreducible g ∧ expand F p g = f
参数：hf : Irreducible f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.derivative_eq_zero`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R} [IsAddTorsionFree R],   Polynomial.derivative p = 0 ↔ p.natDegree =
 0
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.isLocalHom_expand`：isLocalHom_expand {p : Nat} (hp : 0 < p) :
 IsLocalHom (expand R p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.separable_iff_derivative_ne_zero`：separable_iff_derivative_ne
_zero {f : F[X]} (hf : Irreducible f) : f.Separable ↔ derivative f != 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `Irreducible.of_map`：Irreducible.of_map [FunLike F M N] [MonoidHomClass F
 M N] [IsLocalHom f] (hfx : Irreducible (f x)) : Irreducible x where not_isUnit 
hu
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.expand_contract`：expand_contract [CharP R p] [NoZeroDivisors 
R] {f : R[X]} (hf : Polynomial.derivative f = 0) (hp : p != 0) : expand R p (con
tract p f) = f
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem separable_or {f : F[X]} (hf : Irreducible f) :
    f.Separable ∨ ¬f.Separable ∧ ∃ g : F[X], Irreducible g ∧ expand F p g = f := by
  classical
  exact if H : derivative f = 0 then by
    rcases p.eq_zero_or_pos with (rfl | hp)
    · have := CharP.charP_to_charZero F
      have := derivative_eq_zero.1 H
      have := (natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf).ne'
      contradiction
    have := isLocalHom_expand F hp
    exact
      Or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, Classical.not_not, H], contract p f,
          Irreducible.of_map (by rwa [← expand_contract p H hp.ne'] at hf),
          expand_contract p H hp.ne'⟩
  else Or.inl <| (separable_iff_derivative_ne_zero hf).2 H
/-
**Polynomial.exists_separable_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：exists_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : p !=
 0) : exists (n : Nat) (g : F[X]), g.Separable ∧ expand F (p ^ n) g = f
参数：hf : Irreducible f；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Polynomial.separable_or`：separable_or {f : F[X]} (hf : Irreducible f) : 
f.Separable ∨ ¬f.Separable ∧ exists g : F[X], Irreducible g ∧ expand F p g = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Polynomial.separable_C`：separable_C (r : R) : (C r).Separable ↔ IsUnit r
· 使用定理 `Polynomial.degree_le_zero_iff`：degree_le_zero_iff : degree p <= 0 ↔ p = 
C (coeff p 0)
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_expand`：natDegree_expand (p : Nat) (f : R[X]) : (ex
pand R p f).natDegree = f.natDegree * p
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.mul_lt_mul_of_pos_left`：∀ {n m k : ℕ}, n < m → k > 0 → k * n < k * m
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Polynomial.expand_expand`：expand_expand (f : R[X]) : expand R p (expand 
R q f) = expand R (p * q) f
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem exists_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : p ≠ 0) :
    ∃ (n : ℕ) (g : F[X]), g.Separable ∧ expand F (p ^ n) g = f := by
  replace hp : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ N ih
  rcases separable_or p hf with (h | ⟨h1, g, hg, hgf⟩)
  · refine ⟨0, f, h, ?_⟩
    rw [pow_zero, expand_one]
  · rcases N with - | N
    · rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn
      rw [hn, separable_C, isUnit_iff_ne_zero, Classical.not_not] at h1
      have hf0 : f ≠ 0 := hf.ne_zero
      rw [h1, C_0] at hn
      exact absurd hn hf0
    have hg1 : g.natDegree * p = N.succ := by rwa [← natDegree_expand, hgf]
    have hg2 : g.natDegree ≠ 0 := by
      intro this
      rw [this, zero_mul] at hg1
      cases hg1
    have hg3 : g.natDegree < N.succ := by
      rw [← mul_one g.natDegree, ← hg1]
      exact Nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩
    refine ⟨n + 1, g, hg4, ?_⟩
    rw [← hgf, expand_expand, pow_succ']
/-
**Polynomial.isUnit_or_eq_zero_of_separable_expand** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：isUnit_or_eq_zero_of_separable_expand {f : F[X]} (n : Nat) (hp : 0 < p) (h
f : (expand F (p ^ n) f).Separable) : IsUnit f ∨ n = 0
参数：n : Nat；hp : 0 < p；hf : (expand F (p ^ n) f).Separable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Polynomial.derivative_expand`：derivative_expand (f : R[X]) : Polynomial.
derivative (expand R p f) = expand R p (Polynomial.derivative f) * (p * (X ^ (p 
- 1) : R[X]))
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `isCoprime_zero_right`：isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `Polynomial.expand_eq_C`：expand_eq_C {p : Nat} (hp : 0 < p) {f : R[X]} {r
 : R} : expand R p f = C r ↔ f = C r
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
-/
theorem isUnit_or_eq_zero_of_separable_expand {f : F[X]} (n : ℕ) (hp : 0 < p)
    (hf : (expand F (p ^ n) f).Separable) : IsUnit f ∨ n = 0 := by
  rw [or_iff_not_imp_right]
  rintro hn : n ≠ 0
  have hf2 : derivative (expand F (p ^ n) f) = 0 := by
    rw [derivative_expand, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn, zero_mul, mul_zero]
  rw [separable_def, hf2, isCoprime_zero_right, isUnit_iff] at hf
  rcases hf with ⟨r, hr, hrf⟩
  rw [eq_comm, expand_eq_C (pow_pos hp _)] at hrf
  rwa [hrf, isUnit_C]
/-
**Polynomial.unique_separable_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：unique_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : 0 < 
p) (n₁ : Nat) (g₁ : F[X]) (hg₁ : g₁.Separable) (hgf₁ : expand F (p ^ n₁) g₁ = f)
 (n₂ : Nat) (g₂ : F[X]) (hg₂ : g₂.Separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) :
 n₁ = n₂ ∧ g₁ = g₂
参数：hf : Irreducible f；hp : 0 < p；n₁ : Nat；g₁ : F[X]；hg₁ : g₁.Separable；hgf₁ : ex
pand F (p ^ n₁) g₁ = f；n₂ : Nat；g₂ : F[X]；hg₂ : g₂.Separable；hgf₂ : expand F (p 
^ n₂) g₂ = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Polynomial.isUnit_or_eq_zero_of_separable_expand`：isUnit_or_eq_zero_of_s
eparable_expand {f : F[X]} (n : Nat) (hp : 0 < p) (hf : (expand F (p ^ n) f).Sep
arable) : IsUnit f ∨ n = 0
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.expand_inj`：expand_inj {p : Nat} (hp : 0 < p) {f g : R[X]} : 
expand R p f = expand R p g ↔ f = g
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Polynomial.expand_mul`：expand_mul (f : R[X]) : expand R (p * q) f = expa
nd R p (expand R q f)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem unique_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : 0 < p) (n₁ : ℕ)
    (g₁ : F[X]) (hg₁ : g₁.Separable) (hgf₁ : expand F (p ^ n₁) g₁ = f) (n₂ : ℕ) (g₂ : F[X])
    (hg₂ : g₂.Separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) : n₁ = n₂ ∧ g₁ = g₂ := by
  revert g₁ g₂
  wlog hn : n₁ ≤ n₂
  · intro g₁ hg₁ Hg₁ g₂ hg₂ Hg₂
    simpa only [eq_comm] using this p hf hp n₂ n₁ (le_of_not_ge hn) g₂ hg₂ Hg₂ g₁ hg₁ Hg₁
  intro g₁ hg₁ hgf₁ g₂ hg₂ hgf₂
  rw [le_iff_exists_add] at hn
  rcases hn with ⟨k, rfl⟩
  rw [← hgf₁, pow_add, expand_mul, expand_inj (pow_pos hp n₁)] at hgf₂
  subst hgf₂
  subst hgf₁
  rcases isUnit_or_eq_zero_of_separable_expand p k hp hg₁ with (h | rfl)
  · rw [isUnit_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    simp_rw [expand_C] at hf
    exact absurd (isUnit_C.2 hr) hf.1
  · rw [add_zero, pow_zero, expand_one]
    constructor <;> rfl

end CharP

/-- If `n ≠ 0` in `F`, then `X ^ n - a` is separable for any `a ≠ 0`. -/
/-
**Polynomial.separable_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_X_pow_sub_C {n : Nat} (a : F) (hn : (n : F) != 0) (ha : a != 0) 
: Separable (X ^ n - C a)
参数：a : F；hn : (n : F) != 0；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.separable_X_pow_sub_C_unit`：separable_X_pow_sub_C_unit {n : N
at} (u : Rˣ) (hn : IsUnit (n : R)) : Separable (X ^ n - C (u : R))
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x

--- 原说明 ---
If `n ≠ 0` in `F`, then `X ^ n - a` is separable for any `a ≠ 0`.
-/
theorem separable_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 (n : F) hn)

/-- If `F` is of characteristic `p` and `p ∤ n`, then `X ^ n - a` is separable for any `a ≠ 0`. -/
/-
**Polynomial.separable_X_pow_sub_C'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_X_pow_sub_C' (p n : Nat) (a : F) [CharP F p] (hn : ¬p ∣ n) (ha :
 a != 0) : Separable (X ^ n - C a)
参数：p n : Nat；a : F；hn : ¬p ∣ n；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.separable_X_pow_sub_C`：separable_X_pow_sub_C {n : Nat} (a : F
) (hn : (n : F) != 0) (ha : a != 0) : Separable (X ^ n - C a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x

--- 原说明 ---
If `F` is of characteristic `p` and `p ∤ n`, then `X ^ n - a` is separable for a
ny `a ≠ 0`.
-/
theorem separable_X_pow_sub_C' (p n : ℕ) (a : F) [CharP F p] (hn : ¬p ∣ n) (ha : a ≠ 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C a (by rwa [← CharP.cast_eq_zero_iff F p n] at hn) ha

/-- In a field `F`, for any `t ∈ F` and `n > 0`, the polynomial `X ^ n - t` is separable
iff `↑n ≠ 0`. The assumption `n > 0` is needed, since for `n = 0` the polynomial `X ^ n - t`
is separable iff `t ≠ 1`. -/
/-
**Polynomial.X_pow_sub_C_separable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_C_separable_iff {n : Nat} {x : F} (hn : 0 < n) (hx : x != 0) : (
X ^ n - C x : F[X]).Separable ↔ (n : F) != 0
参数：hn : 0 < n；hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.not_isUnit_of_natDegree_pos`：not_isUnit_of_natDegree_pos (p :
 R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.derivative_X_pow`：derivative_X_pow (n : Nat) : derivative (X 
^ n : R[X]) = C (n : R) * X ^ (n - 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.separable_X_pow_sub_C`：separable_X_pow_sub_C {n : Nat} (a : F
) (hn : (n : F) != 0) (ha : a != 0) : Separable (X ^ n - C a)

--- 原说明 ---
In a field `F`, for any `t ∈ F` and `n > 0`, the polynomial `X ^ n - t` is separ
able
iff `↑n ≠ 0`. The assumption `n > 0` is needed, since for `n = 0` the polynomial
 `X ^ n - t`
is separable iff `t ≠ 1`.
-/
theorem X_pow_sub_C_separable_iff {n : ℕ} {x : F} (hn : 0 < n) (hx : x ≠ 0) :
    (X ^ n - C x : F[X]).Separable ↔ (n : F) ≠ 0 := by
  refine ⟨fun h hn' ↦ ?_, fun h => separable_X_pow_sub_C x h hx⟩
  exact not_isUnit_of_natDegree_pos (X ^ n - C x) (by simp [hn]) <| by
    simpa [separable_def, derivative_X_pow, hn', isCoprime_zero_right] using h

-- this can possibly be strengthened to making `separable_X_pow_sub_C_unit` a
-- bi-implication, but it is nontrivial!
/-- In a field `F`, `X ^ n - 1` is separable iff `↑n ≠ 0`. -/
/-
**Polynomial.X_pow_sub_one_separable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_one_separable_iff {n : Nat} : (X ^ n - 1 : F[X]).Separable ↔ (n 
: F) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Polynomial.X_pow_sub_C_separable_iff`：X_pow_sub_C_separable_iff {n : Nat
} {x : F} (hn : 0 < n) (hx : x != 0) : (X ^ n - C x : F[X]).Separable ↔ (n : F) 
!= 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
In a field `F`, `X ^ n - 1` is separable iff `↑n ≠ 0`.
-/
theorem X_pow_sub_one_separable_iff {n : ℕ} : (X ^ n - 1 : F[X]).Separable ↔ (n : F) ≠ 0 := by
  rcases (Nat.eq_zero_or_pos n) with (hz | hpos)
  · simp_all [not_separable_zero]
  · exact X_pow_sub_C_separable_iff hpos one_ne_zero

section Splits

/-
**Polynomial.card_rootSet_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_rootSet_eq_natDegree [Algebra F K] {p : F[X]} (hsep : p.Separable) (h
split : Splits (p.map (algebraMap F K))) : Fintype.card (p.rootSet K) = p.natDeg
ree
参数：hsep : p.Separable；hsplit : Splits (p.map (algebraMap F K))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Multiset.toFinset_card_of_nodup`：Multiset.toFinset_card_of_nodup {m : Mu
ltiset α} (h : m.Nodup) : #m.toFinset = Multiset.card m
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem card_rootSet_eq_natDegree [Algebra F K] {p : F[X]} (hsep : p.Separable)
    (hsplit : Splits (p.map (algebraMap F K))) : Fintype.card (p.rootSet K) = p.natDegree := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map), ← hsplit.natDegree_eq_card_roots,
    natDegree_map]

/-- If a non-zero polynomial splits, then it has no repeated roots on that field
if and only if it is separable. -/
/-
**Polynomial.nodup_roots_iff_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nodup_roots_iff_of_splits {f : F[X]} (hf : f != 0) (h : f.Splits) : f.root
s.Nodup ↔ f.Separable
参数：hf : f != 0；h : f.Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isUnit_iff_degree_eq_zero`：isUnit_iff_degree_eq_zero : IsUnit
 p ↔ degree p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gcd_isUnit_iff`：gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime 
x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `Polynomial.Separable.eq_1`：∀ {R : Type u} [inst : CommSemiring R] (f : P
olynomial R), f.Separable = IsCoprime f (Polynomial.derivative f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.one_lt_rootMultiplicity_iff_isRoot_gcd`：one_lt_rootMultiplici
ty_iff_isRoot_gcd [GCDMonoid R[X]] {p : R[X]} {t : R} (h : p != 0) : 1 < p.rootM
ultiplicity t ↔ (gcd p (derivative p)).…
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup

--- 原说明 ---
If a non-zero polynomial splits, then it has no repeated roots on that field
if and only if it is separable.
-/
theorem nodup_roots_iff_of_splits {f : F[X]} (hf : f ≠ 0) (h : f.Splits) :
    f.roots.Nodup ↔ f.Separable := by
  classical
  refine ⟨(fun hnsep ↦ ?_).mtr, nodup_roots⟩
  rw [Separable, ← gcd_isUnit_iff, isUnit_iff_degree_eq_zero] at hnsep
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero (Splits.of_dvd h hf (gcd_dvd_left f _)) hnsep
  simp_rw [Multiset.nodup_iff_count_le_one, not_forall, not_le]
  exact ⟨x, ((one_lt_rootMultiplicity_iff_isRoot_gcd hf).2 hx).trans_eq f.count_roots.symm⟩

/-- If a non-zero polynomial over `F` splits in `K`, then it has no repeated roots on `K`
if and only if it is separable. -/
@[stacks 09H3 "Here we only require `f` splits instead of `K` is algebraically closed."]
/-
**Polynomial.nodup_aroots_iff_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nodup_aroots_iff_of_splits [Algebra F K] {f : F[X]} (hf : f != 0) (h : (f.
map (algebraMap F K)).Splits) : (f.aroots K).Nodup ↔ f.Separable
参数：hf : f != 0；h : (f.map (algebraMap F K)).Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nodup_roots_iff_of_splits`：nodup_roots_iff_of_splits {f : F[X
]} (hf : f != 0) (h : f.Splits) : f.roots.Nodup ↔ f.Separable
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.separable_map`：separable_map {S} [CommRing S] [Nontrivial S] 
(f : F ->+* S) {p : F[X]} : (p.map f).Separable ↔ p.Separable
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If a non-zero polynomial over `F` splits in `K`, then it has no repeated roots o
n `K`
if and only if it is separable.
-/
theorem nodup_aroots_iff_of_splits [Algebra F K] {f : F[X]} (hf : f ≠ 0)
    (h : (f.map (algebraMap F K)).Splits) : (f.aroots K).Nodup ↔ f.Separable := by
  rw [nodup_roots_iff_of_splits (map_ne_zero hf) h, separable_map]
/-
**Polynomial.card_rootSet_eq_natDegree_iff_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：card_rootSet_eq_natDegree_iff_of_splits [Algebra F K] {f : F[X]} (hf : f !
= 0) (h : (f.map (algebraMap F K)).Splits) : Fintype.card (f.rootSet K) = f.natD
egree ↔ f.Separable
参数：hf : f != 0；h : (f.map (algebraMap F K)).Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.nodup_aroots_iff_of_splits`：nodup_aroots_iff_of_splits [Algeb
ra F K] {f : F[X]} (hf : f != 0) (h : (f.map (algebraMap F K)).Splits) : (f.aroo
ts K).Nodup ↔ f.Separable
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_rootSet_eq_natDegree_iff_of_splits [Algebra F K] {f : F[X]} (hf : f ≠ 0)
    (h : (f.map (algebraMap F K)).Splits) :
    Fintype.card (f.rootSet K) = f.natDegree ↔ f.Separable := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe,
    ← natDegree_map (algebraMap F K), h.natDegree_eq_card_roots,
    Multiset.toFinset_card_eq_card_iff_nodup, nodup_aroots_iff_of_splits hf h]

variable {i : F →+* K}
/-
**Polynomial.eq_X_sub_C_of_separable_of_root_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：eq_X_sub_C_of_separable_of_root_eq {x : F} {h : F[X]} (h_sep : h.Separable
) (h_root : h.eval x = 0) (h_splits : Splits (h.map i)) (h_roots : forall y in (
h.map i).roots, y = i x) : h = C (leadingCoeff h) * (X - C x)
参数：h_sep : h.Separable；h_root : h.eval x = 0；h_splits : Splits (h.map i)；h_roots
 : forall y in (h.map i).roots, y = i x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.not_separable_zero`：not_separable_zero [Nontrivial R] : ¬Sepa
rable (0 : R[X])
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mk.inj`：∀ {α : Type u_4} {val : Multiset α} {nodup : val.Nodup} {
val_1 : Multiset α} {nodup_1 : val_1.Nodup},   { val := val, nodup := nodup } = 
{ v…
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem {s : Fin
set α} {a : α} : s = {a} ↔ a in s ∧ forall x in s, x = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_mk`：mem_mk {a : α} {s nd} : a in @Finset.mk α s nd ↔ a in s
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）
-/
theorem eq_X_sub_C_of_separable_of_root_eq {x : F} {h : F[X]} (h_sep : h.Separable)
    (h_root : h.eval x = 0) (h_splits : Splits (h.map i))
    (h_roots : ∀ y ∈ (h.map i).roots, y = i x) : h = C (leadingCoeff h) * (X - C x) := by
  have h_ne_zero : h ≠ 0 := by
    rintro rfl
    exact not_separable_zero h_sep
  suffices (map i h).roots = {i x} from
    map_injective i i.injective (by simpa using h_splits.eq_X_sub_C_of_single_root this)
  apply Finset.mk.inj
  · change _ = {i x}
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · apply Finset.mem_mk.mpr
      · rw [mem_roots (show h.map i ≠ 0 from map_ne_zero h_ne_zero)]
        rw [IsRoot.def, ← eval₂_eq_eval_map, eval₂_hom, h_root]
        exact map_zero i
      · exact nodup_roots (Separable.map h_sep)
    · exact h_roots
/-
**Polynomial.exists_finset_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_finset_of_splits (i : F ->+* K) {f : F[X]} (sep : Separable f) (sp 
: Splits (f.map i)) : exists s : Finset K, f.map i = C (i f.leadingCoeff) * s.pr
od fun a : K => X - C a
参数：i : F ->+* K；sep : Separable f；sp : Splits (f.map i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_multiset_prod`：prod_eq_multiset_prod [CommMonoid M] (s : 
Finset ι) (f : ι -> M) : ∏ x in s, f x = (s.1.map f).prod
· 使用定理 `Polynomial.nodup_of_separable_prod`：nodup_of_separable_prod [Nontrivial 
R] {s : Multiset R} (hs : Separable (Multiset.map (fun a => X - C a) s).prod) : 
s.Nodup
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.Separable.of_mul_right`：∀ {R : Type u} [inst : CommSemiring R
] {f g : Polynomial R}, (f * g).Separable → g.Separable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `Multiset.toFinset_eq`：toFinset_eq {s : Multiset α} (n : Nodup s) : Finse
t.mk s n = s.toFinset
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
-/
theorem exists_finset_of_splits (i : F →+* K) {f : F[X]} (sep : Separable f)
    (sp : Splits (f.map i)) :
    ∃ s : Finset K, f.map i = C (i f.leadingCoeff) * s.prod fun a : K => X - C a := by
  classical
  obtain ⟨s, h⟩ := splits_iff_exists_multiset.1 sp
  use s.toFinset
  rw [h, Finset.prod_eq_multiset_prod, ← Multiset.toFinset_eq, leadingCoeff_map]
  apply nodup_of_separable_prod
  apply Separable.of_mul_right
  rw [← h]
  exact sep.map

end Splits

/-
**Polynomial._root_.Irreducible.separable** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable := by
  rw [separable_iff_derivative_ne_zero hf, Ne, ← degree_eq_bot, degree_derivative]
  · rintro ⟨⟩
  exact hf.natDegree_pos.ne'

end Field

end Polynomial

open Polynomial

section CommRing

variable (F L K : Type*) [CommRing F] [Ring K] [Algebra F K]

-- TODO: refactor to allow transcendental extensions?
-- See: https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions
-- Note that right now a Galois extension (class `IsGalois`) is defined to be an extension which
-- is separable and normal, so if the definition of separable changes here at some point
-- to allow non-algebraic extensions, then the definition of `IsGalois` must also be changed.

variable {K} in
/--
An element `x` of an algebra `K` over a commutative ring `F` is said to be *separable*, if its
minimal polynomial over `K` is separable. Note that the minimal polynomial of any element not
integral over `F` is defined to be `0`, which is not a separable polynomial.
-/
@[stacks 09H1 "second part"]
/-
**IsSeparable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSeparable (x : K) : Prop
参数：x : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `x` of an algebra `K` over a commutative ring `F` is said to be *sepa
rable*, if its
minimal polynomial over `K` is separable. Note that the minimal polynomial of an
y element not
integral over `F` is defined to be `0`, which is not a separable polynomial.
-/
def IsSeparable (x : K) : Prop := Polynomial.Separable (minpoly F x)

/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable. This implies that `K/F` is an algebraic
extension, because the minimal polynomial of a non-integral element is `0`, which is not
separable.

We define this for general (commutative) rings and only assume `F` and `K` are fields if this
is needed for a proof. -/
@[mk_iff isSeparable_def, stacks 09H1 "third part"]
/-
**Algebra.IsSeparable** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(F : Type u_1) → (K : Type u_3) → [inst : CommRing F] → [inst_1 : Ring K] 
→ [Algebra F K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for separable field extension: `K` is a separable field extension of `
F` iff
the minimal polynomial of every `x : K` is separable. This implies that `K/F` is
 an algebraic
extension, because the minimal polynomial of a non-integral element is `0`, whic
h is not
separable.

We define this for general (commutative) rings and only assume `F` and `K` are f
ields if this
is needed for a proof.
-/
protected class Algebra.IsSeparable : Prop where
  isSeparable' : ∀ x : K, IsSeparable F x

variable {K}
/-
**Algebra.IsSeparable.isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.isSeparable [Algebra.IsSeparable F K] : forall x : K, 
IsSeparable F x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.isSeparable'`：∀ {F : Type u_1} {K : Type u_3} {inst 
: CommRing F} {inst_1 : Ring K} {inst_2 : Algebra F K}   [self : Algebra.IsSepar
able F K] (x : K), IsS…
-/
theorem Algebra.IsSeparable.isSeparable [Algebra.IsSeparable F K] : ∀ x : K, IsSeparable F x :=
  Algebra.IsSeparable.isSeparable'

variable {F} in
/-- If the minimal polynomial of `x : K` over `F` is separable, then `x` is integral over `F`,
because the minimal polynomial of a non-integral element is `0`, which is not separable. -/
/-
**IsSeparable.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparable.isIntegral {x : K} (h : IsSeparable F x) : IsIntegral F x
参数：h : IsSeparable F x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Polynomial.monic_one`：monic_one : Monic (1 : R[X])
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Polynomial.Separable.ne_zero`：∀ {R : Type u} [inst : CommSemiring R] [No
ntrivial R] {f : Polynomial R}, f.Separable → f ≠ 0
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0

--- 原说明 ---
If the minimal polynomial of `x : K` over `F` is separable, then `x` is integral
 over `F`,
because the minimal polynomial of a non-integral element is `0`, which is not se
parable.
-/
theorem IsSeparable.isIntegral {x : K} (h : IsSeparable F x) : IsIntegral F x := by
  cases subsingleton_or_nontrivial F
  · have := Module.subsingleton F K
    exact ⟨1, monic_one, Subsingleton.elim _ _⟩
  · exact of_not_not (h.ne_zero <| minpoly.eq_zero ·)
/-
**Algebra.IsSeparable.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.isIntegral [Algebra.IsSeparable F K] : forall x : K, I
sIntegral F x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
-/
theorem Algebra.IsSeparable.isIntegral [Algebra.IsSeparable F K] : ∀ x : K, IsIntegral F x :=
  fun x ↦ _root_.IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F x)

variable (K) in
/-
**Algebra.IsSeparable.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.isAlgebraic [Nontrivial F] [Algebra.IsSeparable F K] :
 Algebra.IsAlgebraic F K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
-/
instance Algebra.IsSeparable.isAlgebraic [Nontrivial F] [Algebra.IsSeparable F K] :
    Algebra.IsAlgebraic F K :=
  ⟨fun x ↦ (Algebra.IsSeparable.isIntegral F x).isAlgebraic⟩

variable {F}
/-
**Algebra.isSeparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isSeparable_iff : Algebra.IsSeparable F K ↔ forall x : K, IsIntegr
al F x ∧ IsSeparable F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Algebra.isSeparable_iff :
    Algebra.IsSeparable F K ↔ ∀ x : K, IsIntegral F x ∧ IsSeparable F x :=
  ⟨fun _ x => ⟨Algebra.IsSeparable.isIntegral F x, Algebra.IsSeparable.isSeparable F x⟩,
    fun h => ⟨fun x => (h x).2⟩⟩

variable {L}
/-
**isSeparable_map_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSeparable_map_iff [Ring L] [Algebra F L] {x : K} (f : K ->ₐ[F] L) (hf : 
Function.Injective f) : IsSeparable F (f x) ↔ IsSeparable F x
参数：f : K ->ₐ[F] L；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSeparable_map_iff [Ring L] [Algebra F L] {x : K} (f : K →ₐ[F] L)
    (hf : Function.Injective f) : IsSeparable F (f x) ↔ IsSeparable F x := by
  simp_rw [IsSeparable, minpoly.algHom_eq _ hf]
/-
**IsSeparable.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSeparable.map [Ring L] [Algebra F L] {x : K} (f : K ->ₐ[F] L) (hf : Func
tion.Injective f) (H : IsSeparable F x) : IsSeparable F (f x)
参数：f : K ->ₐ[F] L；hf : Function.Injective f；H : IsSeparable F x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSeparable_map_iff`：isSeparable_map_iff [Ring L] [Algebra F L] {x : K} 
(f : K ->ₐ[F] L) (hf : Function.Injective f) : IsSeparable F (f x) ↔ IsSeparable
 F x
-/
lemma IsSeparable.map [Ring L] [Algebra F L] {x : K} (f : K →ₐ[F] L) (hf : Function.Injective f)
    (H : IsSeparable F x) : IsSeparable F (f x) :=
  (isSeparable_map_iff f hf).mpr H
/-
**Subalgebra.isSeparable_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.isSeparable_iff [Ring L] [Algebra F L] {S : Subalgebra F L} : A
lgebra.IsSeparable F S ↔ forall x in S, IsSeparable F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isSeparable_map_iff`：isSeparable_map_iff [Ring L] [Algebra F L] {x : K} 
(f : K ->ₐ[F] L) (hf : Function.Injective f) : IsSeparable F (f x) ↔ IsSeparable
 F x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Subalgebra.isSeparable_iff [Ring L] [Algebra F L] {S : Subalgebra F L} :
    Algebra.IsSeparable F S ↔ ∀ x ∈ S, IsSeparable F x := by
  simp_rw [Algebra.isSeparable_def, Subtype.forall,
    ← isSeparable_map_iff S.val Subtype.val_injective, coe_val]

variable (L) {E : Type*}

section AlgEquiv

variable [Ring E] [Algebra F E] (e : K ≃ₐ[F] E)
include e

/-- Transfer `IsSeparable` across an `AlgEquiv`. -/
/-
**AlgEquiv.isSeparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isSeparable_iff {x : K} : IsSeparable F (e x) ↔ IsSeparable F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Transfer `IsSeparable` across an `AlgEquiv`.
-/
theorem AlgEquiv.isSeparable_iff {x : K} : IsSeparable F (e x) ↔ IsSeparable F x := by
  simp only [IsSeparable, minpoly.algEquiv_eq e x]

/-- Transfer `Algebra.IsSeparable` across an `AlgEquiv`. -/
/-
**AlgEquiv.Algebra.isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.Algebra.isSeparable [Algebra.IsSeparable F K] : Algebra.IsSeparab
le F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.isSeparable_iff`：AlgEquiv.isSeparable_iff {x : K} : IsSeparable
 F (e x) ↔ IsSeparable F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x

--- 原说明 ---
Transfer `Algebra.IsSeparable` across an `AlgEquiv`.
-/
theorem AlgEquiv.Algebra.isSeparable [Algebra.IsSeparable F K] : Algebra.IsSeparable F E :=
  ⟨fun _ ↦ e.symm.isSeparable_iff.mp (Algebra.IsSeparable.isSeparable _ _)⟩
/-
**AlgEquiv.Algebra.isSeparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.Algebra.isSeparable_iff : Algebra.IsSeparable F K ↔ Algebra.IsSep
arable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.Algebra.isSeparable`：AlgEquiv.Algebra.isSeparable [Algebra.IsSe
parable F K] : Algebra.IsSeparable F E
-/
theorem AlgEquiv.Algebra.isSeparable_iff : Algebra.IsSeparable F K ↔ Algebra.IsSeparable F E :=
  ⟨fun _ ↦ AlgEquiv.Algebra.isSeparable e, fun _ ↦ AlgEquiv.Algebra.isSeparable e.symm⟩

end AlgEquiv

section IsScalarTower

variable [Field L] [Ring E] [Algebra F L]
    [Algebra F E] [Algebra L E] [IsScalarTower F L E]

/-- If `E / L / F` is a scalar tower and `x : E` is separable over `F`, then it's also separable
over `L`. -/
@[stacks 09H2 "first part"]
/-
**IsSeparable.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparable.tower_top {x : E} (h : IsSeparable F x) : IsSeparable L x
参数：h : IsSeparable F x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `minpoly.dvd_map_of_isScalarTower`：dvd_map_of_isScalarTower (A K : Type*)
 {R : Type*} [CommRing A] [Field K] [Ring R] [Algebra A K] [Algebra A R] [Algebr
a K R] [IsScalarTower …

--- 原说明 ---
If `E / L / F` is a scalar tower and `x : E` is separable over `F`, then it's al
so separable
over `L`.
-/
theorem IsSeparable.tower_top
    {x : E} (h : IsSeparable F x) : IsSeparable L x :=
  .of_dvd (.map h) (minpoly.dvd_map_of_isScalarTower ..)

variable (F E) in
/-- If `E / K / F` is an extension tower, `E` is separable over `F`, then it's also separable
over `K`. -/
@[stacks 09H2 "second part"]
/-
**Algebra.isSeparable_tower_top_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isSeparable_tower_top_of_isSeparable [Algebra.IsSeparable F E] : A
lgebra.IsSeparable L E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x

--- 原说明 ---
If `E / K / F` is an extension tower, `E` is separable over `F`, then it's also 
separable
over `K`.
-/
theorem Algebra.isSeparable_tower_top_of_isSeparable [Algebra.IsSeparable F E] :
    Algebra.IsSeparable L E :=
  ⟨fun x ↦ IsSeparable.tower_top _ (Algebra.IsSeparable.isSeparable F x)⟩

end IsScalarTower

end CommRing

section Field

variable (F : Type*) [Field F] {K E E' : Type*}

section IsIntegral

variable [Ring K] [Algebra F K]

variable {F} in
/-
**isSeparable_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeparable_algebraMap (x : F) : IsSeparable F (algebraMap F K x)
参数：x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `Polynomial.separable_X_sub_C`：separable_X_sub_C {x : R} : Separable (X -
 C x)
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSeparable_algebraMap (x : F) : IsSeparable F (algebraMap F K x) :=
  Polynomial.Separable.of_dvd (Polynomial.separable_X_sub_C (x := x))
    (minpoly.dvd F (algebraMap F K x) (by simp))
/-
**Algebra.isSeparable_self** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.isSeparable_self : Algebra.IsSeparable F F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isSeparable_algebraMap`：isSeparable_algebraMap (x : F) : IsSeparable F (
algebraMap F K x)
-/
instance Algebra.isSeparable_self : Algebra.IsSeparable F F :=
  ⟨isSeparable_algebraMap⟩

variable [IsDomain K] [Algebra.IsIntegral F K] [CharZero F]
/-
**IsSeparable.of_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparable.of_integral (x : K) : IsSeparable F x
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.separable`：∀ {F : Type u} [inst : Field F] [CharZero F] {f :
 Polynomial F}, Irreducible f → f.Separable
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem IsSeparable.of_integral (x : K) : IsSeparable F x :=
  (minpoly.irreducible <| Algebra.IsIntegral.isIntegral x).separable

-- See note [lower instance priority]
variable (K) in
/-- An integral field extension in characteristic 0 is separable. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An integral field extension in characteristic 0 is separable.
-/
protected instance (priority := 100) Algebra.IsSeparable.of_integral : Algebra.IsSeparable F K :=
  ⟨_root_.IsSeparable.of_integral _⟩

end IsIntegral

section IsScalarTower

variable [Field K] [Ring E] [Algebra F K] [Algebra F E] [Algebra K E]
  [Nontrivial E] [IsScalarTower F K E]

variable {F} in
/-- If `E / K / F` is a scalar tower and `algebraMap K E x` is separable over `F`, then `x` is
also separable over `F`. -/
/-
**IsSeparable.tower_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparable.tower_bot {x : K} (h : IsSeparable F (algebraMap K E x)) : IsS
eparable F x
参数：h : IsSeparable F (algebraMap K E x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.aeval_algebraMap_eq_zero_iff`：aeval_algebraMap_eq_zero_iff [I
sDomain A] [IsTorsionFree A B] [Nontrivial B] (x : A) (p : R[X]) : aeval (algebr
aMap A B x) p = 0 ↔ aeval x p…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Polynomial.Separable.of_mul_left`：∀ {R : Type u} [inst : CommSemiring R]
 {f g : Polynomial R}, (f * g).Separable → f.Separable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `E / K / F` is a scalar tower and `algebraMap K E x` is separable over `F`, t
hen `x` is
also separable over `F`.
-/
theorem IsSeparable.tower_bot {x : K} (h : IsSeparable F (algebraMap K E x)) : IsSeparable F x :=
    have ⟨_q, hq⟩ :=
      minpoly.dvd F x
        ((aeval_algebraMap_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebraMap K E) x)))
    (Eq.mp (congrArg Separable hq) h).of_mul_left

variable (K E) in
/-
**Algebra.isSeparable_tower_bot_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isSeparable_tower_bot_of_isSeparable [h : Algebra.IsSeparable F E]
 : Algebra.IsSeparable F K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.tower_bot`：IsSeparable.tower_bot {x : K} (h : IsSeparable F 
(algebraMap K E x)) : IsSeparable F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
-/
theorem Algebra.isSeparable_tower_bot_of_isSeparable [h : Algebra.IsSeparable F E] :
    Algebra.IsSeparable F K :=
  ⟨fun _ ↦ IsSeparable.tower_bot (h.isSeparable _ _)⟩

end IsScalarTower

section

variable [Field E] [Field E'] [Algebra F E] [Algebra F E']
    (f : E →ₐ[F] E')
include f

variable {F} in
/-
**IsSeparable.of_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparable.of_algHom {x : E} (h : IsSeparable F (f x)) : IsSeparable F x
参数：h : IsSeparable F (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IsSeparable.tower_bot`：IsSeparable.tower_bot {x : K} (h : IsSeparable F 
(algebraMap K E x)) : IsSeparable F x
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem IsSeparable.of_algHom {x : E} (h : IsSeparable F (f x)) : IsSeparable F x := by
  let _ : Algebra E E' := RingHom.toAlgebra f.toRingHom
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  exact h.tower_bot


variable (E') in
/-
**Algebra.IsSeparable.of_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.of_algHom [Algebra.IsSeparable F E'] : Algebra.IsSepar
able F E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.of_algHom`：IsSeparable.of_algHom {x : E} (h : IsSeparable F 
(f x)) : IsSeparable F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
-/
theorem Algebra.IsSeparable.of_algHom [Algebra.IsSeparable F E'] : Algebra.IsSeparable F E :=
  ⟨fun x => (Algebra.IsSeparable.isSeparable F (f x)).of_algHom⟩

end

namespace IntermediateField

variable [Field K] [Algebra F K] (M : IntermediateField F K)

/-
**IntermediateField.isSeparable_tower_bot** 是 Mathlib 中的一个实例，位于命名空间 `Intermediat
eField`。
形式化陈述：isSeparable_tower_bot [Algebra.IsSeparable F K] : Algebra.IsSeparable F M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
instance isSeparable_tower_bot [Algebra.IsSeparable F K] : Algebra.IsSeparable F M :=
  Algebra.isSeparable_tower_bot_of_isSeparable F M K
/-
**IntermediateField.isSeparable_tower_top** 是 Mathlib 中的一个实例，位于命名空间 `Intermediat
eField`。
形式化陈述：isSeparable_tower_top [Algebra.IsSeparable F K] : Algebra.IsSeparable M K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isSeparable_tower_top_of_isSeparable`：Algebra.isSeparable_tower_
top_of_isSeparable [Algebra.IsSeparable F E] : Algebra.IsSeparable L E
-/
instance isSeparable_tower_top [Algebra.IsSeparable F K] : Algebra.IsSeparable M K :=
  Algebra.isSeparable_tower_top_of_isSeparable F M K

end IntermediateField

end Field

section AlgEquiv

open RingHom RingEquiv

variable {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Ring B₁] [Field A₂] [Ring B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
include he

/-
**IsSeparable.of_equiv_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSeparable.of_equiv_equiv {x : B₁} (h : IsSeparable A₁ x) : IsSeparable A
₂ (e₂ x)
参数：h : IsSeparable A₁ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgEquiv.isSeparable_iff`：AlgEquiv.isSeparable_iff {x : K} : IsSeparable
 F (e x) ↔ IsSeparable F x
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `RingHom.congr_arg`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} (f : α →+* β) {x_2 y : α},   x_2 = y → f x_2 = f 
y
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
lemma IsSeparable.of_equiv_equiv {x : B₁} (h : IsSeparable A₁ x) : IsSeparable A₂ (e₂ x) :=
  letI := e₁.toRingHom.toAlgebra
  letI : Algebra A₂ B₁ :=
    { (algebraMap A₁ B₁).comp e₁.symm.toRingHom with
        algebraMap := (algebraMap A₁ B₁).comp e₁.symm.toRingHom
        smul := fun a b ↦ ((algebraMap A₁ B₁).comp e₁.symm.toRingHom a) * b
        commutes' := fun r x ↦ (Algebra.commutes) (e₁.symm.toRingHom r) x
        smul_def' := fun _ _ ↦ rfl }
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq <| fun x ↦
      (algebraMap A₁ B₁).congr_arg <| id ((e₁.symm_apply_apply x).symm)
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun x ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using! DFunLike.congr_fun he.symm (e₁.symm x) }
  (AlgEquiv.isSeparable_iff e).mpr <| IsSeparable.tower_top A₂ h
/-
**Algebra.IsSeparable.of_equiv_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.of_equiv_equiv [Algebra.IsSeparable A₁ B₁] : Algebra.I
sSeparable A₂ B₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `IsSeparable.of_equiv_equiv`：IsSeparable.of_equiv_equiv {x : B₁} (h : IsS
eparable A₁ x) : IsSeparable A₂ (e₂ x)
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
lemma Algebra.IsSeparable.of_equiv_equiv [Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂ :=
  ⟨fun x ↦ (e₂.apply_symm_apply x) ▸ _root_.IsSeparable.of_equiv_equiv e₁ e₂ he
    (Algebra.IsSeparable.isSeparable _ _)⟩
/-
**Algebra.IsSeparable.iff_of_equiv_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.iff_of_equiv_equiv : Algebra.IsSeparable A₁ B₁ ↔ Algeb
ra.IsSeparable A₂ B₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `Algebra.IsSeparable.of_equiv_equiv`：Algebra.IsSeparable.of_equiv_equiv [
Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
-/
lemma Algebra.IsSeparable.iff_of_equiv_equiv :
    Algebra.IsSeparable A₁ B₁ ↔ Algebra.IsSeparable A₂ B₂ :=
  ⟨fun _ ↦ Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he,
    fun _ ↦ Algebra.IsSeparable.of_equiv_equiv e₁.symm e₂.symm (by
      ext x
      simpa [RingEquiv.eq_symm_apply] using (RingHom.ext_iff.mp he (e₁.symm x)).symm)⟩

end AlgEquiv

section CardAlgHom

variable {R S T : Type*} [CommRing S]
variable {K L F : Type*} [Field K] [Field L] [Field F]
variable [Algebra K S] [Algebra K L]

/-
**AlgHom.natCard_of_powerBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.natCard_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K 
pb.gen) (h_splits : ((minpoly K pb.gen).map (algebraMap K L)).Splits) : Nat.card
 (S ->ₐ[K] L) = pb.dim
参数：pb : PowerBasis K S；h_sep : IsSeparable K pb.gen；h_splits : ((minpoly K pb.ge
n).map (algebraMap K L)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : foral
l x : α, x in s ↔ p x) : Nat.card { x // p x } = Finset.card s
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.natDegree_minpoly`：natDegree_minpoly [Nontrivial A] (pb : Pow
erBasis A S) : (minpoly A pb.gen).natDegree = pb.dim
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `Multiset.toFinset_card_of_nodup`：Multiset.toFinset_card_of_nodup {m : Mu
ltiset α} (h : m.Nodup) : #m.toFinset = Multiset.card m
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.separable_map`：separable_map {S} [CommRing S] [Nontrivial S] 
(f : F ->+* S) {p : F[X]} : (p.map f).Separable ↔ p.Separable
-/
theorem AlgHom.natCard_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
    (h_splits : ((minpoly K pb.gen).map (algebraMap K L)).Splits) :
    Nat.card (S →ₐ[K] L) = pb.dim := by
  classical
  rw [Nat.card_congr pb.liftEquiv', Nat.subtype_card _ (fun x => Multiset.mem_toFinset),
    ← pb.natDegree_minpoly, ← natDegree_map (algebraMap K L), h_splits.natDegree_eq_card_roots,
    Multiset.toFinset_card_of_nodup]
  exact nodup_roots ((separable_map (algebraMap K L)).mpr h_sep)
/-
**AlgHom.card_of_powerBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.card_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K pb.
gen) (h_splits : ((minpoly K pb.gen).map (algebraMap K L)).Splits) : @Fintype.ca
rd (S ->ₐ[K] L) (PowerBasis.AlgHom.fintype pb) = pb.dim
参数：pb : PowerBasis K S；h_sep : IsSeparable K pb.gen；h_splits : ((minpoly K pb.ge
n).map (algebraMap K L)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `AlgHom.natCard_of_powerBasis`：AlgHom.natCard_of_powerBasis (pb : PowerBa
sis K S) (h_sep : IsSeparable K pb.gen) (h_splits : ((minpoly K pb.gen).map (alg
ebraMap K L)).Spli…
-/
theorem AlgHom.card_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
    (h_splits : ((minpoly K pb.gen).map (algebraMap K L)).Splits) :
    @Fintype.card (S →ₐ[K] L) (PowerBasis.AlgHom.fintype pb) = pb.dim := by
  rw [Fintype.card_eq_nat_card, AlgHom.natCard_of_powerBasis pb h_sep h_splits]

end CardAlgHom

