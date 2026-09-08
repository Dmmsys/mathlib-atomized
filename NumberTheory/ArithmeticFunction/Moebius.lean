/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!
# The Möbius function and Möbius inversion

## Main Definitions

* `μ` is the Möbius function (spelled `moebius` in code; the notation `μ` is available by opening
  the namespace `ArithmeticFunction.Moebius`).

## Main Results

* Several forms of Möbius inversion:
* `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
* And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
* `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

open scoped zeta

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
/-
**ArithmeticFunction.moebius** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：moebius : ArithmeticFunction Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`μ` is the Möbius function. If `n` is squarefree with an even number of distinct
 prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, 
`μ n = -1`.
  If `n` is not squarefree, `μ n = 0`.
-/
def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

open scoped Moebius

@[simp]
/-
**ArithmeticFunction.moebius_apply_of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：moebius_apply_of_squarefree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ ca
rdFactors n
参数：h : Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n :=
  if_pos h

@[simp]
/-
**ArithmeticFunction.moebius_eq_zero_of_not_squarefree** 是 Mathlib 中的一个定理，位于命名空间
 `ArithmeticFunction`。
形式化陈述：moebius_eq_zero_of_not_squarefree {n : Nat} (h : ¬Squarefree n) : μ n = 0
参数：h : ¬Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h
/-
**ArithmeticFunction.moebius_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：moebius_apply_one : μ 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.cardFactors_one`：ArithmeticFunction.cardFactors 1 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem moebius_apply_one : μ 1 = 1 := by simp
/-
**ArithmeticFunction.moebius_ne_zero_iff_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：moebius_ne_zero_iff_squarefree {n : Nat} : μ n != 0 ↔ Squarefree n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`：moebius_eq_zero_of
_not_squarefree {n : Nat} (h : ¬Squarefree n) : μ n = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n := by
  constructor <;> intro h
  · contrapose h
    simp [h]
  · simp [h]
/-
**ArithmeticFunction.moebius_eq_or** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：moebius_eq_or (n : Nat) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `neg_one_pow_eq_or`：∀ (R : Type u) [inst : Monoid R] [inst_1 : HasDistrib
Neg R] (n : ℕ), (-1) ^ n = 1 ∨ (-1) ^ n = -1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem moebius_eq_or (n : ℕ) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl
/-
**ArithmeticFunction.moebius_ne_zero_iff_eq_or** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：moebius_ne_zero_iff_eq_or {n : Nat} : μ n != 0 ↔ μ n = 1 ∨ μ n = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.moebius_eq_or`：moebius_eq_or (n : Nat) : μ n = 0 ∨ μ 
n = 1 ∨ μ n = -1
-/
theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 := by
  have := moebius_eq_or n
  lia
/-
**ArithmeticFunction.moebius_sq_eq_one_of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `
ArithmeticFunction`。
形式化陈述：moebius_sq_eq_one_of_squarefree {l : Nat} (hl : Squarefree l) : μ l ^ 2 = 
1
参数：hl : Squarefree l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
/-
**ArithmeticFunction.abs_moebius_eq_one_of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 
`ArithmeticFunction`。
形式化陈述：abs_moebius_eq_one_of_squarefree {l : Nat} (hl : Squarefree l) : |μ l| = 1
参数：hl : Squarefree l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]
/-
**ArithmeticFunction.moebius_sq** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：moebius_sq {n : Nat} : μ n ^ 2 = if Squarefree n then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ArithmeticFunction.moebius_sq_eq_one_of_squarefree`：moebius_sq_eq_one_of
_squarefree {l : Nat} (hl : Squarefree l) : μ l ^ 2 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`：moebius_eq_zero_of
_not_squarefree {n : Nat} (h : ¬Squarefree n) : μ n = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem moebius_sq {n : ℕ} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, zero_pow (show 2 ≠ 0 by simp)]
/-
**ArithmeticFunction.abs_moebius** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：abs_moebius {n : Nat} : |μ n| = if Squarefree n then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ArithmeticFunction.abs_moebius_eq_one_of_squarefree`：abs_moebius_eq_one_
of_squarefree {l : Nat} (hl : Squarefree l) : |μ l| = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`：moebius_eq_zero_of
_not_squarefree {n : Nat} (h : ¬Squarefree n) : μ n = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_moebius {n : ℕ} :
    |μ n| = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]
/-
**ArithmeticFunction.abs_moebius_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFun
ction`。
形式化陈述：abs_moebius_le_one {n : Nat} : |μ n| <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.abs_moebius`：abs_moebius {n : Nat} : |μ n| = if Squar
efree n then 1 else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem abs_moebius_le_one {n : ℕ} : |μ n| ≤ 1 := by
  rw [abs_moebius, apply_ite (· ≤ 1)]
  simp
/-
**ArithmeticFunction.moebius_apply_prime** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：moebius_apply_prime {p : Nat} (hp : p.Prime) : μ p = -1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用定理 `Irreducible.squarefree`：Irreducible.squarefree [CommMonoid R] {x : R} (h
 : Irreducible x) : Squarefree x
· 使用定理 `ArithmeticFunction.cardFactors_apply_prime`：cardFactors_apply_prime {p :
 Nat} (hp : p.Prime) : Ω p = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem moebius_apply_prime {p : ℕ} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree, cardFactors_apply_prime hp, pow_one]
/-
**ArithmeticFunction.moebius_apply_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：moebius_apply_prime_pow {p k : Nat} (hp : p.Prime) (hk : k != 0) : μ (p ^ 
k) = if k = 1 then -1 else 0
参数：hp : p.Prime；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ArithmeticFunction.moebius_apply_prime`：moebius_apply_prime {p : Nat} (h
p : p.Prime) : μ p = -1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`：moebius_eq_zero_of
_not_squarefree {n : Nat} (h : ¬Squarefree n) : μ n = 0
· 使用定理 `Nat.squarefree_pow_iff`：squarefree_pow_iff {n k : Nat} (hn : n != 1) (hk
 : k != 0) : Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
-/
theorem moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk, not_and_or]
  exact Or.inr h
/-
**ArithmeticFunction.moebius_apply_isPrimePow_not_prime** 是 Mathlib 中的一个定理，位于命名空
间 `ArithmeticFunction`。
形式化陈述：moebius_apply_isPrimePow_not_prime {n : Nat} (hn : IsPrimePow n) (hn' : ¬n
.Prime) : μ n = 0
参数：hn : IsPrimePow n；hn' : ¬n.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.moebius_apply_prime_pow`：moebius_apply_prime_pow {p k
 : Nat} (hp : p.Prime) (hk : k != 0) : μ (p ^ k) = if k = 1 then -1 else 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem moebius_apply_isPrimePow_not_prime {n : ℕ} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne', if_neg]
  rintro rfl
  exact hn' (by simpa)

@[arith_mult]
/-
**ArithmeticFunction.isMultiplicative_moebius** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：isMultiplicative_moebius : IsMultiplicative μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.iff_ne_zero`：iff_ne_zero [MonoidWith
Zero R] {f : ArithmeticFunction R} : IsMultiplicative f ↔ f 1 = 1 ∧ forall {m n 
: Nat}, m != 0 -> n != 0 -> m.Coprime…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.cardFactors_one`：ArithmeticFunction.cardFactors 1 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.squarefree_mul`：squarefree_mul {m n : Nat} (hmn : m.Coprime n) : Squ
arefree (m * n) ↔ Squarefree m ∧ Squarefree n
· 使用定理 `ArithmeticFunction.cardFactors_mul`：cardFactors_mul {m n : Nat} (m0 : m 
!= 0) (n0 : n != 0) : Ω (m * n) = Ω m + Ω n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `ite_zero_mul_ite_zero`：ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = i
te (P ∧ Q) (a * b) 0
-/
theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, coe_mk, squarefree_mul hnm, ite_zero_mul_ite_zero, cardFactors_mul hn hm,
    pow_add]
/-
**ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree** 是
 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : ArithmeticFunction R},   f.I
sMultiplicative → ∀ {n : ℕ}, Squarefree n → ∏ p ∈ n.primeFactors, (1 + f p) = ∑ 
d ∈ n.divisors, f d
参数：1 + f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.prodPrimeFactors_apply`：prodPrimeFactors_apply [CommM
onoidWithZero R] {f : Nat -> R} {n : Nat} (hn : n != 0) : ∏ᵖ p ∣ n, f p = ∏ p in
 n.primeFactors, f p
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ArithmeticFunction.zeta_apply_ne`：zeta_apply_ne {x : Nat} (h : x != 0) :
 ζ x = 1
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree`：
prodPrimeFactors_add_of_squarefree [CommSemiring R] {f g : ArithmeticFunction R}
 (hf : IsMultiplicative f) (hg : IsMultiplicative g) {n : Na…
· 使用定理 `ArithmeticFunction.IsMultiplicative.natCast`：natCast {f : ArithmeticFunc
tion Nat} [Semiring R] (h : f.IsMultiplicative) : IsMultiplicative (f : Arithmet
icFunction R)
· 使用定理 `ArithmeticFunction.isMultiplicative_zeta`：isMultiplicative_zeta : IsMult
iplicative ζ
· 使用定理 `ArithmeticFunction.coe_zeta_mul_apply`：coe_zeta_mul_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (ζ * f) x = ∑ i in divisors x, f i
-/
theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree [CommSemiring R]
    {f : ArithmeticFunction R} (h_mult : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 + f p) = ∑ d ∈ n.divisors, f d := by
  trans (∏ᵖ p ∣ n, ((ζ : ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply prod_congr rfl; intro p hp
    rw [zeta_apply_ne (prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_zero, cast_one]
  rw [isMultiplicative_zeta.natCast.prodPrimeFactors_add_of_squarefree h_mult hn,
    coe_zeta_mul_apply]
/-
**ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree** 是
 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (f : ArithmeticFunction R),   f.IsMul
tiplicative →     ∀ {n : ℕ}, Squarefree n → ∏ p ∈ n.primeFactors, (1 - f p) = ∑ 
d ∈ n.divisors, ↑(ArithmeticFunction.moebius d) * f d
参数：f : ArithmeticFunction R；1 - f p；ArithmeticFunction.moebius d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.pmul_apply`：pmul_apply [MulZeroClass R] {f g : Arithm
eticFunction R} {x : Nat} : f.pmul g x = f x * g x
· 使用定理 `ArithmeticFunction.intCoe_apply`：intCoe_apply [AddGroupWithOne R] {f : A
rithmeticFunction Int} {x : Nat} : (f : ArithmeticFunction R) x = f x
· 使用定理 `ArithmeticFunction.moebius_apply_prime`：moebius_apply_prime {p : Nat} (h
p : p.Prime) : μ p = -1
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_neg`：∀ {n : ℕ} {R : Type u_2} [inst : Ring R] {
a : R},   Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n) → a = (Int.negOfNat n).r
awCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isintCast`：isintCast {R} [Ring R] (n m : Int) : IsI
nt n m -> IsInt (n : R) m
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 43 条，此处仅展示前 30 条）
-/
theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree [CommRing R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d := by
  trans (∏ p ∈ n.primeFactors, (1 + (ArithmeticFunction.pmul (μ : ArithmeticFunction R) f) p))
  · apply prod_congr rfl; intro p hp
    rw [pmul_apply, intCoe_apply, ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp))]
    ring
  · rw [(isMultiplicative_moebius.intCast.pmul hf).prodPrimeFactors_one_add_of_squarefree hn]
    simp_rw [pmul_apply, intCoe_apply]

open UniqueFactorizationMonoid

@[simp]
/-
**ArithmeticFunction.moebius_mul_coe_zeta** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction Int) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.coe_mul_zeta_apply`：coe_mul_zeta_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (f * ζ) x = ∑ i in divisors x, f i
· 使用定理 `Nat.sum_divisors_prime_pow`：∀ {α : Type u_1} [inst : AddCommMonoid α] {k
 p : ℕ} {f : ℕ → α},   Nat.Prime p → ∑ x ∈ (p ^ k).divisors, f x = ∑ x ∈ Finset.
range (k + 1), f…
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ArithmeticFunction.moebius_apply_prime_pow`：moebius_apply_prime_pow {p k
 : Nat} (hp : p.Prime) (hk : k != 0) : μ (p ^ k) = if k = 1 then -1 else 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ArithmeticFunction.moebius_apply_of_squarefree`：moebius_apply_of_squaref
ree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.cardFactors_one`：ArithmeticFunction.cardFactors 1 = 0
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `ArithmeticFunction.one_apply_ne`：one_apply_ne {x : Nat} (h : x != 1) : (
1 : ArithmeticFunction R) x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Nat.divisorsAntidiagonal_one`：divisorsAntidiagonal_one : divisorsAntidia
gonal 1 = {(1, 1)}
（共 45 条，此处仅展示前 30 条）
-/
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    simp [moebius_apply_prime_pow, hp.ne_one, hn.ne', hp, hn]
  | coprime a b _ha _hb hab ha' hb' =>
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.natCast

@[simp]
/-
**ArithmeticFunction.coe_zeta_mul_moebius** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction Int) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ArithmeticFunction.moebius_mul_coe_zeta`：moebius_mul_coe_zeta : (μ * ζ :
 ArithmeticFunction Int) = 1
-/
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_coe_zeta]

@[simp]
/-
**ArithmeticFunction.coe_moebius_mul_coe_zeta** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.coe_coe`：coe_coe [AddGroupWithOne R] {f : ArithmeticF
unction Nat} : ((f : ArithmeticFunction Int) : ArithmeticFunction R) = (f : Arit
hmeticFunction R…
· 使用定理 `ArithmeticFunction.intCoe_mul`：intCoe_mul [Ring R] {f g : ArithmeticFunc
tion Int} : (↑(f * g) : ArithmeticFunction R) = ↑f * g
· 使用定理 `ArithmeticFunction.moebius_mul_coe_zeta`：moebius_mul_coe_zeta : (μ * ζ :
 ArithmeticFunction Int) = 1
· 使用定理 `ArithmeticFunction.intCoe_one`：intCoe_one [AddGroupWithOne R] : ((1 : Ar
ithmeticFunction Int) : ArithmeticFunction R) = 1
-/
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]

@[simp]
/-
**ArithmeticFunction.coe_zeta_mul_coe_moebius** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.coe_coe`：coe_coe [AddGroupWithOne R] {f : ArithmeticF
unction Nat} : ((f : ArithmeticFunction Int) : ArithmeticFunction R) = (f : Arit
hmeticFunction R…
· 使用定理 `ArithmeticFunction.intCoe_mul`：intCoe_mul [Ring R] {f g : ArithmeticFunc
tion Int} : (↑(f * g) : ArithmeticFunction R) = ↑f * g
· 使用定理 `ArithmeticFunction.coe_zeta_mul_moebius`：coe_zeta_mul_moebius : (ζ * μ :
 ArithmeticFunction Int) = 1
· 使用定理 `ArithmeticFunction.intCoe_one`：intCoe_one [AddGroupWithOne R] : ((1 : Ar
ithmeticFunction Int) : ArithmeticFunction R) = 1
-/
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, coe_zeta_mul_moebius, intCoe_one]

section CommRing

variable [CommRing R]

/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Invertible (ζ : ArithmeticFunction R) where
  invOf := μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

/-- A unit in `ArithmeticFunction R` that evaluates to `ζ`, with inverse `μ`. -/
/-
**ArithmeticFunction.zetaUnit** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：zetaUnit : (ArithmeticFunction R)ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unit in `ArithmeticFunction R` that evaluates to `ζ`, with inverse `μ`.
-/
def zetaUnit : (ArithmeticFunction R)ˣ :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]
/-
**ArithmeticFunction.coe_zetaUnit** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction 
R) = ζ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ :=
  rfl

@[simp]
/-
**ArithmeticFunction.inv_zetaUnit** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunctio
n R) = μ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ :=
  rfl

end CommRing

set_option backward.isDefEq.respectTransparency false in
/-- Möbius inversion for functions to an `AddCommGroup`. -/
/-
**ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : Nat -> R} : (forall
 n > 0, ∑ i in n.divisors, f i = g n) ↔ forall n > 0, ∑ x in n.divisorsAntidiago
nal, μ x.fst • g x.snd = f n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ext_iff`：∀ {R : Type u_1} [inst : Zero R] {f g : Arit
hmeticFunction R}, f = g ↔ ∀ (x : ℕ), f x = g x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.coe_zeta_smul_apply`：coe_zeta_smul_apply {M} [Semirin
g R] [AddCommMonoid M] [MulAction R M] {f : ArithmeticFunction M} {x : Nat} : ((
↑ζ : ArithmeticFunction R) •…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.pos_of_mem_divisors`：pos_of_mem_divisors {m : Nat} (h : m in n.divis
ors) : 0 < m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `ArithmeticFunction.moebius_mul_coe_zeta`：moebius_mul_coe_zeta : (μ * ζ :
 ArithmeticFunction Int) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ArithmeticFunction.coe_zeta_mul_moebius`：coe_zeta_mul_moebius : (ζ * μ :
 ArithmeticFunction Int) = 1
· 使用定理 `Nat.divisorsAntidiagonal_zero`：divisorsAntidiagonal_zero : divisorsAntid
iagonal 0 = ∅
· 使用定理 `Nat.snd_mem_divisors_of_mem_antidiagonal`：snd_mem_divisors_of_mem_antidi
agonal {x : Nat × Nat} (h : x in divisorsAntidiagonal n) : x.snd in divisors n

--- 原说明 ---
Möbius inversion for functions to an `AddCommGroup`.
-/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd = f n := by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction ℤ) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [coe_zeta_smul_apply]
      simp only [forall_prop_of_true, succ_pos', f', g', coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => if_neg (pos_of_mem_divisors hx).ne']
  trans μ • g' = f'
  · constructor <;> intro h <;>
      simp only [← h, ← mul_smul, moebius_mul_coe_zeta, coe_zeta_mul_moebius, one_smul]
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp only [forall_prop_of_true, succ_pos', smul_apply, f', g', coe_mk, succ_ne_zero,
        ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)).ne']

/-- Möbius inversion for functions to a `Ring`. -/
/-
**ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ar
ithmeticFunction`。
形式化陈述：sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : Nat -> R} : (forall 
n > 0, ∑ i in n.divisors, f i = g n) ↔ forall n > 0, ∑ x in n.divisorsAntidiagon
al, (μ x.fst : R) * g x.snd = f n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`：sum_eq_iff_sum_smul_m
oebius_eq [AddCommGroup R] {f g : Nat -> R} : (forall n > 0, ∑ i in n.divisors, 
f i = g n) ↔ forall n > 0, ∑ x in n.div…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `Eq.congr_left`：∀ {α : Sort u_1} {x y z : α}, x = y → (x = z ↔ y = z)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a

--- 原说明 ---
Möbius inversion for functions to a `Ring`.
-/
theorem sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`. -/
/-
**ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq** 是 Mathlib 中的一个定理，位于命名空间 `
ArithmeticFunction`。
形式化陈述：prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : Nat -> R} : (forall n
 > 0, ∏ i in n.divisors, f i = g n) ↔ forall n > 0, ∏ x in n.divisorsAntidiagona
l, g x.snd ^ μ x.fst = f n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`：sum_eq_iff_sum_smul_m
oebius_eq [AddCommGroup R] {f g : Nat -> R} : (forall n > 0, ∑ i in n.divisors, 
f i = g n) ↔ forall n > 0, ∑ x in n.div…

--- 原说明 ---
Möbius inversion for functions to a `CommGroup`.
-/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

/-- Möbius inversion for functions to a `CommGroupWithZero`. -/
/-
**ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero** 是 Mathlib 中的一个
定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : Na
t -> R} (hf : forall n : Nat, 0 < n -> f n != 0) (hg : forall n : Nat, 0 < n -> 
g n != 0) : (forall n > 0, ∏ i in n.divisors, f i = g n) ↔ forall n > 0, ∏ x in 
n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n
参数：hf : forall n : Nat, 0 < n -> f n != 0；hg : forall n : Nat, 0 < n -> g n != 0
。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `Units.coeHom_apply`：coeHom_apply (x : Mˣ) : coeHom M x = ↑x
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.pos_of_mem_divisors`：pos_of_mem_divisors {m : Nat} (h : m in n.divis
ors) : 0 < m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq`：prod_eq_iff_prod_pow
_moebius_eq [CommGroup R] {f g : Nat -> R} : (forall n > 0, ∏ i in n.divisors, f
 i = g n) ↔ forall n > 0, ∏ x in n.divis…
· 使用定理 `Nat.snd_mem_divisors_of_mem_antidiagonal`：snd_mem_divisors_of_mem_antidi
agonal {x : Nat × Nat} (h : x in divisorsAntidiagonal n) : x.snd in divisors n
· 使用定理 `Units.val_zpow_eq_zpow_val`：val_zpow_eq_zpow_val : forall (u : αˣ) (n : 
Int), ((u ^ n : αˣ) : α) = (u : α) ^ n

--- 原说明 ---
Möbius inversion for functions to a `CommGroupWithZero`.
-/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : ℕ → R}
    (hf : ∀ n : ℕ, 0 < n → f n ≠ 0) (hg : ∀ n : ℕ, 0 < n → g n ≠ 0) :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)), Units.coeHom_apply,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Möbius inversion for functions to an `AddCommGroup`, where the equalities only hold on a
well-behaved set. -/
/-
**ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on** 是 Mathlib 中的一个定理，位于命名空间
 `ArithmeticFunction`。
形式化陈述：sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : Nat -> R} (s : S
et Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) : (forall n > 0, n in s -> 
(∑ i in n.divisors, f i) = g n) ↔ forall n > 0, n in s -> (∑ x in n.divisorsAnti
diagonal, μ x.fst • g x.snd) = f n
参数：s : Set Nat；hs : forall m n, m ∣ n -> n in s -> m in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sum_divisorsAntidiagonal'`：∀ {M : Type u_1} [inst : AddCommMonoid M]
 (f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.di
visors, f (n / i) i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`：sum_eq_iff_sum_smul_m
oebius_eq [AddCommGroup R] {f g : Nat -> R} : (forall n > 0, ∑ i in n.divisors, 
f i = g n) ↔ forall n > 0, ∑ x in n.div…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.pos_of_mem_divisors`：pos_of_mem_divisors {m : Nat} (h : m in n.divis
ors) : 0 < m
· 使用定理 `Nat.dvd_of_mem_divisors`：dvd_of_mem_divisors {m : Nat} (h : n in divisor
s m) : n ∣ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Möbius inversion for functions to an `AddCommGroup`, where the equalities only h
old on a
well-behaved set.
-/
theorem sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n : ℕ) => (∑ i ∈ n.divisors, f i)
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, μ (n / d) • G d = f n by
      rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • g y), ← this, sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    rw [← sum_divisorsAntidiagonal' (f := fun x y => μ x • G y)]
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n : ℕ) => ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, F d = g n by
      rw [← this, sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl
/-
**ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on'** 是 Mathlib 中的一个定理，位于命名空
间 `ArithmeticFunction`。
形式化陈述：sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : Nat -> R} (s : 
Set Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) (hs₀ : 0 ∉ s) : (forall n 
in s, (∑ i in n.divisors, f i) = g n) ↔ forall n in s, (∑ x in n.divisorsAntidia
gonal, μ x.fst • g x.snd) = f n
参数：s : Set Nat；hs : forall m n, m ∣ n -> n in s -> m in s；hs₀ : 0 ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on`：sum_eq_iff_sum_smu
l_moebius_eq_on [AddCommGroup R] {f g : Nat -> R} (s : Set Nat) (hs : forall m n
, m ∣ n -> n in s -> m in s) : (forall n >…
-/
theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) (hs₀ : 0 ∉ s) :
    (∀ n ∈ s, (∑ i ∈ n.divisors, f i) = g n) ↔
     ∀ n ∈ s, (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : ∀ P : ℕ → Prop, ((∀ n ∈ s, P n) ↔ (∀ n > 0, n ∈ s → P n)) := fun P ↦ by
    refine forall_congr' (fun n ↦ ⟨fun h _ ↦ h, fun h hn ↦ h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs

/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on a well-behaved
set. -/
/-
**ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on** 是 Mathlib 中的一个定理，位于命名空间 
`ArithmeticFunction`。
形式化陈述：sum_eq_iff_sum_mul_moebius_eq_on [NonAssocRing R] {f g : Nat -> R} (s : Se
t Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) : (forall n > 0, n in s -> (
∑ i in n.divisors, f i) = g n) ↔ forall n > 0, n in s -> (∑ x in n.divisorsAntid
iagonal, (μ x.fst : R) * g x.snd) = f n
参数：s : Set Nat；hs : forall m n, m ∣ n -> n in s -> m in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on`：sum_eq_iff_sum_smu
l_moebius_eq_on [AddCommGroup R] {f g : Nat -> R} (s : Set Nat) (hs : forall m n
, m ∣ n -> n in s -> m in s) : (forall n >…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `Eq.congr_left`：∀ {α : Sort u_1} {x y z : α}, x = y → (x = z ↔ y = z)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a

--- 原说明 ---
Möbius inversion for functions to a `Ring`, where the equalities only hold on a 
well-behaved
set.
-/
theorem sum_eq_iff_sum_mul_moebius_eq_on [NonAssocRing R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s →
        (∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`, where the equalities only hold on a
well-behaved set. -/
/-
**ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_on** 是 Mathlib 中的一个定理，位于命名空
间 `ArithmeticFunction`。
形式化陈述：prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : Nat -> R} (s : Set
 Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) : (forall n > 0, n in s -> (∏
 i in n.divisors, f i) = g n) ↔ forall n > 0, n in s -> (∏ x in n.divisorsAntidi
agonal, g x.snd ^ μ x.fst) = f n
参数：s : Set Nat；hs : forall m n, m ∣ n -> n in s -> m in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on`：sum_eq_iff_sum_smu
l_moebius_eq_on [AddCommGroup R] {f g : Nat -> R} (s : Set Nat) (hs : forall m n
, m ∣ n -> n in s -> m in s) : (forall n >…

--- 原说明 ---
Möbius inversion for functions to a `CommGroup`, where the equalities only hold 
on a
well-behaved set.
-/
theorem prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

/-- Möbius inversion for functions to a `CommGroupWithZero`, where the equalities only hold on
a well-behaved set. -/
/-
**ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero** 是 Mathlib 中
的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R] (s : S
et Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) {f g : Nat -> R} (hf : fora
ll n > 0, f n != 0) (hg : forall n > 0, g n != 0) : (forall n > 0, n in s -> (∏ 
i in n.divisors, f i) = g n) ↔ forall n > 0, n in s -> (∏ x in n.divisorsAntidia
gonal, g x.snd ^ μ x.fst) = f n
参数：s : Set Nat；hs : forall m n, m ∣ n -> n in s -> m in s；hf : forall n > 0, f n
 != 0；hg : forall n > 0, g n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `Units.coeHom_apply`：coeHom_apply (x : Mˣ) : coeHom M x = ↑x
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.pos_of_mem_divisors`：pos_of_mem_divisors {m : Nat} (h : m in n.divis
ors) : 0 < m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_on`：prod_eq_iff_prod_
pow_moebius_eq_on [CommGroup R] {f g : Nat -> R} (s : Set Nat) (hs : forall m n,
 m ∣ n -> n in s -> m in s) : (forall n > 0…
· 使用定理 `Nat.snd_mem_divisors_of_mem_antidiagonal`：snd_mem_divisors_of_mem_antidi
agonal {x : Nat × Nat} (h : x in divisorsAntidiagonal n) : x.snd in divisors n
· 使用定理 `Units.val_zpow_eq_zpow_val`：val_zpow_eq_zpow_val : forall (u : αˣ) (n : 
Int), ((u ^ n : αˣ) : α) = (u : α) ^ n

--- 原说明 ---
Möbius inversion for functions to a `CommGroupWithZero`, where the equalities on
ly hold on
a well-behaved set.
-/
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R]
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) {f g : ℕ → R}
    (hf : ∀ n > 0, f n ≠ 0) (hg : ∀ n > 0, g n ≠ 0) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)),
      Units.coeHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end ArithmeticFunction

