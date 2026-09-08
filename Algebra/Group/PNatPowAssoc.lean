/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Notation.Prod

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `PNatPowAssoc`, where `PNat` means only strictly positive
powers are considered.

## Results

- `ppow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `ppow_one` a defining property: `x ^ 1 = x`
- `ppow_assoc` strictly positive powers of an element have associative multiplication.
- `ppow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `ppow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `ppow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

- PNatPowAssoc for products and Pi types

## TODO

* `NatPowAssoc` for `MulOneClass` - more or less the same flow
* It seems unlikely that anyone will want `NatSMulAssoc` and `PNatSMulAssoc` as additive versions of
  power-associativity, but we have found that it is not hard to write.

-/

public section

-- TODO:
-- assert_not_exists MonoidWithZero

variable {M : Type*}

/-- A `Prop`-valued mixin for power-associative multiplication in the non-unital setting. -/
/-
**PNatPowAssoc** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_2) → [Mul M] → [Pow M ℕ+] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Prop`-valued mixin for power-associative multiplication in the non-unital set
ting.
-/
class PNatPowAssoc (M : Type*) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : ∀ (k n : ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x

section Mul

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

/-
**ppow_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_add (k n : Nat+) (x : M) : x ^ (k + n) = x ^ k * x ^ n
参数：k n : Nat+；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNatPowAssoc.ppow_add`：∀ {M : Type u_2} {inst : Mul M} {inst_1 : Pow M ℕ
+} [self : PNatPowAssoc M] (k n : ℕ+) (x : M),   x ^ (k + n) = x ^ k * x ^ n
-/
theorem ppow_add (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

@[simp]
/-
**ppow_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_one (x : M) : x ^ (1 : Nat+) = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNatPowAssoc.ppow_one`：∀ {M : Type u_2} {inst : Mul M} {inst_1 : Pow M ℕ
+} [self : PNatPowAssoc M] (x : M), x ^ 1 = x
-/
theorem ppow_one (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x
/-
**ppow_mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_mul_assoc (k m n : Nat+) (x : M) : (x ^ k * x ^ m) * x ^ n = x ^ k * 
(x ^ m * x ^ n)
参数：k m n : Nat+；x : M。
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
theorem ppow_mul_assoc (k m n : ℕ+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]
/-
**ppow_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_mul_comm (m n : Nat+) (x : M) : x ^ m * x ^ n = x ^ n * x ^ m
参数：m n : Nat+；x : M。
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
theorem ppow_mul_comm (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]
/-
**ppow_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_mul (x : M) (m n : Nat+) : x ^ (m * n) = (x ^ m) ^ n
参数：x : M；m n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ppow_one`：ppow_one (x : M) : x ^ (1 : Nat+) = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ppow_add`：ppow_add (k n : Nat+) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem ppow_mul (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]
/-
**ppow_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_mul' (x : M) (m n : Nat+) : x ^ (m * n) = (x ^ n) ^ m
参数：x : M；m n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ppow_mul`：ppow_mul (x : M) (m n : Nat+) : x ^ (m * n) = (x ^ m) ^ n
-/
theorem ppow_mul' (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m

end Mul

/-
**Pi.instPNatPowAssoc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instPNatPowAssoc {ι : Type*} {α : ι -> Type*} [forall i, Mul <| α i] [f
orall i, Pow (α i) Nat+] [forall i, PNatPowAssoc <| α i] : PNatPowAssoc (forall 
i, α i) where ppow_add _ _ _
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
· 使用定理 `ppow_add`：ppow_add (k n : Nat+) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ppow_one`：ppow_one (x : M) : x ^ (1 : Nat+) = x
-/
instance Pi.instPNatPowAssoc {ι : Type*} {α : ι → Type*} [∀ i, Mul <| α i] [∀ i, Pow (α i) ℕ+]
    [∀ i, PNatPowAssoc <| α i] : PNatPowAssoc (∀ i, α i) where
  ppow_add _ _ _ := by ext; simp [ppow_add]
  ppow_one _ := by ext; simp
/-
**Prod.instPNatPowAssoc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instPNatPowAssoc {N : Type*} [Mul M] [Pow M Nat+] [PNatPowAssoc M] [M
ul N] [Pow N Nat+] [PNatPowAssoc N] : PNatPowAssoc (M × N) where ppow_add _ _ _
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
· 使用定理 `ppow_add`：ppow_add (k n : Nat+) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ppow_one`：ppow_one (x : M) : x ^ (1 : Nat+) = x
-/
instance Prod.instPNatPowAssoc {N : Type*} [Mul M] [Pow M ℕ+] [PNatPowAssoc M] [Mul N] [Pow N ℕ+]
    [PNatPowAssoc N] : PNatPowAssoc (M × N) where
  ppow_add _ _ _ := by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp
/-
**ppow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ppow_eq_pow [Monoid M] [Pow M Nat+] [PNatPowAssoc M] (x : M) (n : Nat+) : 
x ^ n = x ^ (n : Nat)
参数：x : M；n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ppow_one`：ppow_one (x : M) : x ^ (1 : Nat+) = x
· 使用定理 `PNat.one_coe`：one_coe : ((1 : Nat+) : Nat) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ppow_add`：ppow_add (k n : Nat+) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `PNat.add_coe`：add_coe (m n : Nat+) : ((m + n : Nat+) : Nat) = m + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]
