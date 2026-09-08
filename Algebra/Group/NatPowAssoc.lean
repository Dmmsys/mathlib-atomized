/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `NatPowAssoc`.

## Results

- `npow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `npow_one` a defining property: `x ^ 1 = x`
- `npow_assoc` strictly positive powers of an element have associative multiplication.
- `npow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `npow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `npow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

We also produce the following instances:

- `NatPowAssoc` for Monoids, Pi types and products.

## TODO

* `to_additive`?

-/

public section

assert_not_exists DenselyOrdered

variable {M : Type*}

/-- A mixin for power-associative multiplication. -/
/-
**NatPowAssoc** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_2) → [MulOneClass M] → [Pow M ℕ] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin for power-associative multiplication.
-/
class NatPowAssoc (M : Type*) [MulOneClass M] [Pow M ℕ] : Prop where
  /-- Multiplication is power-associative. -/
  protected npow_add : ∀ (k n : ℕ) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent zero is one. -/
  protected npow_zero : ∀ (x : M), x ^ 0 = 1
  /-- Exponent one is identity. -/
  protected npow_one : ∀ (x : M), x ^ 1 = x

section MulOneClass

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

/-
**npow_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
参数：k n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NatPowAssoc.npow_add`：∀ {M : Type u_2} {inst : MulOneClass M} {inst_1 : 
Pow M ℕ} [self : NatPowAssoc M] (k n : ℕ) (x : M),   x ^ (k + n) = x ^ k * x ^ n
-/
theorem npow_add (k n : ℕ) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  NatPowAssoc.npow_add k n x

@[simp]
/-
**npow_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_zero (x : M) : x ^ 0 = 1
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NatPowAssoc.npow_zero`：∀ {M : Type u_2} {inst : MulOneClass M} {inst_1 :
 Pow M ℕ} [self : NatPowAssoc M] (x : M), x ^ 0 = 1
-/
theorem npow_zero (x : M) : x ^ 0 = 1 :=
  NatPowAssoc.npow_zero x

@[simp]
/-
**npow_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_one (x : M) : x ^ 1 = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NatPowAssoc.npow_one`：∀ {M : Type u_2} {inst : MulOneClass M} {inst_1 : 
Pow M ℕ} [self : NatPowAssoc M] (x : M), x ^ 1 = x
-/
theorem npow_one (x : M) : x ^ 1 = x :=
  NatPowAssoc.npow_one x
/-
**npow_mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_mul_assoc (k m n : Nat) (x : M) : (x ^ k * x ^ m) * x ^ n = x ^ k * (
x ^ m * x ^ n)
参数：k m n : Nat；x : M。
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
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem npow_mul_assoc (k m n : ℕ) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← npow_add, add_assoc]
/-
**npow_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_mul_comm (m n : Nat) (x : M) : x ^ m * x ^ n = x ^ n * x ^ m
参数：m n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem npow_mul_comm (m n : ℕ) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← npow_add, add_comm]
/-
**npow_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_mul (x : M) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n
参数：x : M；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
-/
theorem npow_mul (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | zero => rw [npow_zero, mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]
/-
**npow_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：npow_mul' (x : M) (m n : Nat) : x ^ (m * n) = (x ^ n) ^ m
参数：x : M；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `npow_mul`：npow_mul (x : M) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n
-/
theorem npow_mul' (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact npow_mul x n m

end MulOneClass

section Neg

/-
**neg_npow_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_npow_assoc {R : Type*} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] (a
 b : R) (k : Nat) : (-1) ^ k * a * b = (-1) ^ k * (a * b)
参数：a b : R；k : Nat。
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
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul_comm`：neg_mul_comm (a b : α) : -a * b = a * -b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem neg_npow_assoc {R : Type*} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] (a b : R) (k : ℕ) :
    (-1) ^ k * a * b = (-1) ^ k * (a * b) := by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add, npow_one, ← neg_mul_comm, mul_one]
    simp only [neg_mul, ih]

end Neg

/-
**Pi.instNatPowAssoc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instNatPowAssoc {ι : Type*} {α : ι -> Type*} [forall i, MulOneClass <| 
α i] [forall i, Pow (α i) Nat] [forall i, NatPowAssoc <| α i] : NatPowAssoc (for
all i, α i) where npow_add _ _ _
参数：α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
-/
instance Pi.instNatPowAssoc {ι : Type*} {α : ι → Type*} [∀ i, MulOneClass <| α i] [∀ i, Pow (α i) ℕ]
    [∀ i, NatPowAssoc <| α i] : NatPowAssoc (∀ i, α i) where
    npow_add _ _ _ := by ext; simp [npow_add]
    npow_zero _ := by ext; simp
    npow_one _ := by ext; simp
/-
**Prod.instNatPowAssoc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instNatPowAssoc {N : Type*} [MulOneClass M] [Pow M Nat] [NatPowAssoc 
M] [MulOneClass N] [Pow N Nat] [NatPowAssoc N] : NatPowAssoc (M × N) where npow_
add _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
-/
instance Prod.instNatPowAssoc {N : Type*} [MulOneClass M] [Pow M ℕ] [NatPowAssoc M] [MulOneClass N]
    [Pow N ℕ] [NatPowAssoc N] : NatPowAssoc (M × N) where
  npow_add _ _ _ := by ext <;> simp [npow_add]
  npow_zero _ := by ext <;> simp
  npow_one _ := by ext <;> simp

section Monoid

variable [Monoid M]

/-
**Monoid.PowAssoc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.PowAssoc : NatPowAssoc M where npow_add _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
instance Monoid.PowAssoc : NatPowAssoc M where
  npow_add _ _ _ := pow_add _ _ _
  npow_zero _ := pow_zero _
  npow_one _ := pow_one _

@[simp, norm_cast]
/-
**Nat.cast_npow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R Nat] [NatPowAssoc R]
 (n m : Nat) : (↑(n ^ m) : R) = (↑n : R) ^ m
参数：R : Type*；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
-/
theorem Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] (n m : ℕ) :
    (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

@[simp, norm_cast]
/-
**Int.cast_npow** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (R : Type u_2) [inst : NonAssocRing R] [inst_1 : Pow R ℕ] [NatPowAssoc R
] (n : ℤ) (m : ℕ), ↑(n ^ m) = ↑n ^ m
参数：R : Type u_2；n : ℤ；m : ℕ；n ^ m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Int.cast_npow (R : Type*) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]
    (n : ℤ) : ∀ (m : ℕ), @Int.cast R NonAssocRing.toIntCast (n ^ m) = (n : R) ^ m
  | 0 => by
    rw [pow_zero, npow_zero, Int.cast_one]
  | m + 1 => by
    rw [npow_add, npow_one, Int.cast_mul, Int.cast_npow R n m, npow_add, npow_one]

end Monoid

