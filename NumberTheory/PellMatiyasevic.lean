/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Pell's equation and Matiyasevic's theorem

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1`
*in the special case that `d = a ^ 2 - 1`*.
This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `NumberTheory.Dioph`.

For results on Pell's equation for arbitrary (positive, non-square) `d`, see
`NumberTheory.Pell`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
  constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
  the first variable is the `x`-component in a solution to Pell's equation - the key step towards
  Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

-/

@[expose] public section


namespace Pell

open Nat

section

variable {d : ℤ}

/-- The property of being a solution to the Pell equation, expressed
  as a property of elements of `ℤ√d`. -/
/-
**Pell.IsPell** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：{d : ℤ} → ℤ√d → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of being a solution to the Pell equation, expressed
  as a property of elements of `ℤ√d`.
-/
def IsPell : ℤ√d → Prop
  | ⟨x, y⟩ => x * x - d * y * y = 1
/-
**Pell.isPell_norm** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {d : ℤ} {b : ℤ√d}, Pell.IsPell b ↔ b * star b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 49 条，此处仅展示前 30 条）
-/
theorem isPell_norm : ∀ {b : ℤ√d}, IsPell b ↔ b * star b = 1
  | ⟨x, y⟩ => by simp [Zsqrtd.ext_iff, IsPell, mul_comm]; ring_nf
/-
**Pell.isPell_iff_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {d : ℤ} {b : ℤ√d}, Pell.IsPell b ↔ b ∈ unitary (ℤ√d)
参数：ℤ√d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.mem_iff`：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U *
 star U = 1
· 使用定理 `Pell.isPell_norm`：∀ {d : ℤ} {b : ℤ√d}, Pell.IsPell b ↔ b * star b = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPell_iff_mem_unitary : ∀ {b : ℤ√d}, IsPell b ↔ b ∈ unitary (ℤ√d)
  | ⟨x, y⟩ => by rw [Unitary.mem_iff, isPell_norm, mul_comm (star _), and_self_iff]
/-
**Pell.isPell_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：isPell_mul {b c : Int√d} (hb : IsPell b) (hc : IsPell c) : IsPell (b * c)
参数：hb : IsPell b；hc : IsPell c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pell.isPell_norm`：∀ {d : ℤ} {b : ℤ√d}, Pell.IsPell b ↔ b * star b = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isPell_mul {b c : ℤ√d} (hb : IsPell b) (hc : IsPell c) : IsPell (b * c) :=
  isPell_norm.2 (by simp [mul_comm, mul_left_comm c, mul_assoc,
    star_mul, isPell_norm.1 hb, isPell_norm.1 hc])
/-
**Pell.isPell_star** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {d : ℤ} {b : ℤ√d}, Pell.IsPell b ↔ Pell.IsPell (star b)
参数：star b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPell_star : ∀ {b : ℤ√d}, IsPell b ↔ IsPell (star b)
  | ⟨x, y⟩ => by simp [IsPell]

end

section

variable {a : ℕ} (a1 : 1 < a)

set_option backward.privateInPublic true in
/-
**Pell.d** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def d (_a1 : 1 < a) :=
  a * a - 1

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Pell.d_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：d_pos : 0 < d a1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem d_pos : 0 < d a1 :=
  tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (by decide) (Nat.zero_le _) : 1 * 1 < a * a)

-- TODO(lint): Fix double namespace issue
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Pell sequences, i.e. the sequence of integer solutions to `x ^ 2 - d * y ^ 2 = 1`, where
`d = a ^ 2 - 1`, defined together in mutual recursion. -/
--@[nolint dup_namespace]
/-
**Pell.pell** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：{a : ℕ} → 1 < a → ℕ → ℕ × ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pell : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => ((pell n).1 * a + d a1 * (pell n).2, (pell n).1 + (pell n).2 * a)

/-- The Pell `x` sequence. -/
/-
**Pell.xn** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：xn (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Pell `x` sequence.
-/
def xn (n : ℕ) : ℕ :=
  (pell a1 n).1

/-- The Pell `y` sequence. -/
/-
**Pell.yn** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：yn (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Pell `y` sequence.
-/
def yn (n : ℕ) : ℕ :=
  (pell a1 n).2

@[simp]
/-
**Pell.pell_val** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pell_val (n : Nat) : pell a1 n = (xn a1 n, yn a1 n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pell_val (n : ℕ) : pell a1 n = (xn a1 n, yn a1 n) :=
  show pell a1 n = ((pell a1 n).1, (pell a1 n).2) from
    match pell a1 n with
    | (_, _) => rfl

@[simp]
/-
**Pell.xn_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_zero : xn a1 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xn_zero : xn a1 0 = 1 :=
  rfl

@[simp]
/-
**Pell.yn_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yn_zero : yn a1 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yn_zero : yn a1 0 = 0 :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Pell.xn_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_succ (n : Nat) : xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xn_succ (n : ℕ) : xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n :=
  rfl

@[simp]
/-
**Pell.yn_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yn_succ (n : Nat) : yn a1 (n + 1) = xn a1 n + yn a1 n * a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yn_succ (n : ℕ) : yn a1 (n + 1) = xn a1 n + yn a1 n * a :=
  rfl
/-
**Pell.xn_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_one : xn a1 1 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem xn_one : xn a1 1 = a := by simp
/-
**Pell.yn_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yn_one : yn a1 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem yn_one : yn a1 1 = 1 := by simp

/-- The Pell `x` sequence, considered as an integer sequence. -/
/-
**Pell.xz** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：xz (n : Nat) : Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Pell `x` sequence, considered as an integer sequence.
-/
def xz (n : ℕ) : ℤ :=
  xn a1 n

/-- The Pell `y` sequence, considered as an integer sequence. -/
/-
**Pell.yz** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：yz (n : Nat) : Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Pell `y` sequence, considered as an integer sequence.
-/
def yz (n : ℕ) : ℤ :=
  yn a1 n

section

/-- The element `a` such that `d = a ^ 2 - 1`, considered as an integer. -/
/-
**Pell.az** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：az (a : Nat) : Int
参数：a : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element `a` such that `d = a ^ 2 - 1`, considered as an integer.
-/
def az (a : ℕ) : ℤ :=
  a

end

include a1 in
/-
**Pell.asq_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：asq_pos : 0 < a * a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem asq_pos : 0 < a * a :=
  le_trans (le_of_lt a1)
    (by have := @Nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa [mul_one] at this)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.dz_val** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：dz_val : ↑(d a1) = az a * az a - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.asq_pos`：asq_pos : 0 < a * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.PellMatiyasevic.0.Pell.d.eq_1`：∀ {a : ℕ} (
_a1 : 1 < a), Pell.d✝ _a1 = a * a - 1
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
-/
theorem dz_val : ↑(d a1) = az a * az a - 1 :=
  have : 1 ≤ a * a := asq_pos a1
  by rw [Pell.d, Int.ofNat_sub this]; rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Pell.xz_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xz_succ (n : Nat) : (xz a1 (n + 1)) = xz a1 n * az a + d a1 * yz a1 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xz_succ (n : ℕ) : (xz a1 (n + 1)) = xz a1 n * az a + d a1 * yz a1 n :=
  rfl

@[simp]
/-
**Pell.yz_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yz_succ (n : Nat) : yz a1 (n + 1) = xz a1 n + yz a1 n * az a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yz_succ (n : ℕ) : yz a1 (n + 1) = xz a1 n + yz a1 n * az a :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Pell sequence can also be viewed as an element of `ℤ√d` -/
/-
**Pell.pellZd** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：pellZd (n : Nat) : Int√(d a1)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Pell sequence can also be viewed as an element of `ℤ√d`
-/
def pellZd (n : ℕ) : ℤ√(d a1) :=
  ⟨xn a1 n, yn a1 n⟩

@[simp]
/-
**Pell.re_pellZd** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：re_pellZd (n : Nat) : (pellZd a1 n).re = xn a1 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_pellZd (n : ℕ) : (pellZd a1 n).re = xn a1 n :=
  rfl

@[simp]
/-
**Pell.im_pellZd** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：im_pellZd (n : Nat) : (pellZd a1 n).im = yn a1 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_pellZd (n : ℕ) : (pellZd a1 n).im = yn a1 n :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.isPell_nat** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：isPell_nat {x y : Nat} : IsPell (⟨x, y⟩ : Int√(d a1)) ↔ x * x - d a1 * y *
 y = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `Int.le_of_ofNat_le_ofNat`：∀ {m n : ℕ}, ↑m ≤ ↑n → m ≤ n
· 使用定理 `Int.le.intro_sub`：∀ {a b : ℤ} (n : ℕ), b - a = ↑n → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
-/
theorem isPell_nat {x y : ℕ} : IsPell (⟨x, y⟩ : ℤ√(d a1)) ↔ x * x - d a1 * y * y = 1 :=
  ⟨fun h =>
    (Nat.cast_inj (R := ℤ)).1
      (by rw [Int.ofNat_sub (Int.le_of_ofNat_le_ofNat <| Int.le.intro_sub _ h)]; exact h),
    fun h =>
    show ((x * x : ℕ) - (d a1 * y * y : ℕ) : ℤ) = 1 by
      rw [← Int.ofNat_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ h, h]; rfl⟩

@[simp]
/-
**Pell.pellZd_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pellZd_succ (n : Nat) : pellZd a1 (n + 1) = pellZd a1 n * ⟨a, 1⟩
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem pellZd_succ (n : ℕ) : pellZd a1 (n + 1) = pellZd a1 n * ⟨a, 1⟩ := by ext <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.isPell_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：isPell_one : IsPell (⟨a, 1⟩ : Int√(d a1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.dz_val`：dz_val : ↑(d a1) = az a * az a - 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isPell_one : IsPell (⟨a, 1⟩ : ℤ√(d a1)) :=
  show az a * az a - d a1 * 1 * 1 = 1 by simp [dz_val]
/-
**Pell.isPell_pellZd** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：isPell_pellZd : forall n : Nat, IsPell (pellZd a1 n) | 0 => rfl | n + 1 =>
 by let o
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isPell_pellZd : ∀ n : ℕ, IsPell (pellZd a1 n)
  | 0 => rfl
  | n + 1 => by
    let o := isPell_one a1
    simpa using Pell.isPell_mul (isPell_pellZd n) o

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Pell.pell_eqz** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pell_eqz (n : Nat) : xz a1 n * xz a1 n - d a1 * yz a1 n * yz a1 n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.isPell_pellZd`：isPell_pellZd : forall n : Nat, IsPell (pellZd a1 n)
 | 0 => rfl | n + 1 => by let o
-/
theorem pell_eqz (n : ℕ) : xz a1 n * xz a1 n - d a1 * yz a1 n * yz a1 n = 1 :=
  isPell_pellZd a1 n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Pell.pell_eq** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pell_eq (n : Nat) : xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.pell_eqz`：pell_eqz (n : Nat) : xz a1 n * xz a1 n - d a1 * yz a1 n *
 yz a1 n = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Int.le.intro`：∀ {a b : ℤ} (n : ℕ), a + ↑n = b → a ≤ b
· 使用定理 `add_eq_of_eq_sub'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 b = c - a → a + b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
-/
theorem pell_eq (n : ℕ) : xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1 :=
  let pn := pell_eqz a1 n
  have h : (↑(xn a1 n * xn a1 n) : ℤ) - ↑(d a1 * yn a1 n * yn a1 n) = 1 := by
    repeat' rw [Int.natCast_mul]; exact pn
  have hl : d a1 * yn a1 n * yn a1 n ≤ xn a1 n * xn a1 n :=
    Nat.cast_le.1 <| Int.le.intro _ <| add_eq_of_eq_sub' <| Eq.symm h
  (Nat.cast_inj (R := ℤ)).1 (by rw [Int.ofNat_sub hl]; exact h)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.dnsq** 是 Mathlib 中的一个实例，位于命名空间 `Pell`。
形式化陈述：dnsq : Zsqrtd.Nonsquare (d a1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Pell.asq_pos`：asq_pos : 0 < a * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_self_lt_mul_self_iff`：∀ {m n : ℕ}, m * m < n * n ↔ m < n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.mul_self_le_mul_self`：∀ {m n : ℕ}, m ≤ n → m * m ≤ n * n
· 使用定理 `Nat.le_of_add_le_add_right`：∀ {a b c : ℕ}, a + b ≤ c + b → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 47 条，此处仅展示前 30 条）
-/
instance dnsq : Zsqrtd.Nonsquare (d a1) :=
  ⟨fun n h =>
    have : n * n + 1 = a * a := by rw [← h]; exact Nat.succ_pred_eq_of_pos (asq_pos a1)
    have na : n < a := Nat.mul_self_lt_mul_self_iff.1 (by rw [← this]; exact Nat.lt_succ_self _)
    have : (n + 1) * (n + 1) ≤ n * n + 1 := by rw [this]; exact Nat.mul_self_le_mul_self na
    have : n + n ≤ 0 :=
      @Nat.le_of_add_le_add_right _ (n * n + 1) _ (by ring_nf at this ⊢; assumption)
    Nat.ne_of_gt (d_pos a1) <| by
      rwa [Nat.eq_zero_of_le_zero ((Nat.le_add_left _ _).trans this)] at h⟩
/-
**Pell.xn_ge_a_pow** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), a ^ n ≤ Pell.xn a1 n
参数：a1 : 1 < a；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xn_ge_a_pow : ∀ n : ℕ, a ^ n ≤ xn a1 n
  | 0 => le_refl 1
  | n + 1 => by
    simp only [_root_.pow_succ, xn_succ]
    exact le_trans (Nat.mul_le_mul_right _ (xn_ge_a_pow n)) (Nat.le_add_right _ _)
/-
**Pell.n_lt_xn** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：n_lt_xn (n) : n < xn a1 n
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `Pell.xn_ge_a_pow`：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), a ^ n ≤ Pell.xn a1 n
-/
theorem n_lt_xn (n) : n < xn a1 n :=
  lt_of_lt_of_le (Nat.lt_pow_self a1) (xn_ge_a_pow a1 n)
/-
**Pell.x_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：x_pos (n) : 0 < xn a1 n
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Pell.n_lt_xn`：n_lt_xn (n) : n < xn a1 n
-/
theorem x_pos (n) : 0 < xn a1 n :=
  lt_of_le_of_lt (Nat.zero_le n) (n_lt_xn a1 n)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.eq_pell_lem** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_pell_lem : forall (n) (b : Int√(d a1)), 1 <= b -> IsPell b -> b <= pell
Zd a1 n -> exists n, b = pellZd a1 n | 0, _ => fun h1 _ hl => ⟨0, le_antisymm hl
 h1⟩ | n + 1, b => fun h1 hp h => have a1p : (0 : Int√(d a1)) <= ⟨a, 1⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_pell_lem : ∀ (n) (b : ℤ√(d a1)), 1 ≤ b → IsPell b →
    b ≤ pellZd a1 n → ∃ n, b = pellZd a1 n
  | 0, _ => fun h1 _ hl => ⟨0, le_antisymm hl h1⟩
  | n + 1, b => fun h1 hp h =>
    have a1p : (0 : ℤ√(d a1)) ≤ ⟨a, 1⟩ := trivial
    have am1p : (0 : ℤ√(d a1)) ≤ ⟨a, -1⟩ := show (_ : Nat) ≤ _ by simp [d]
    have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : ℤ√(d a1)) = 1 := isPell_norm.1 (isPell_one a1)
    if ha : (⟨↑a, 1⟩ : ℤ√(d a1)) ≤ b then
      let ⟨m, e⟩ :=
        eq_pell_lem n (b * ⟨a, -1⟩) (by rw [← a1m]; exact mul_le_mul_of_nonneg_right ha am1p)
          (isPell_mul hp (isPell_star.1 (isPell_one a1)))
          (by
            have t := mul_le_mul_of_nonneg_right h am1p
            rwa [pellZd_succ, mul_assoc, a1m, mul_one] at t)
      ⟨m + 1, by
        rw [show b = b * ⟨a, -1⟩ * ⟨a, 1⟩ by rw [mul_assoc, Eq.trans (mul_comm _ _) a1m]; simp,
          pellZd_succ, e]⟩
    else
      suffices ¬1 < b from ⟨0, show b = 1 from (Or.resolve_left (lt_or_eq_of_le h1) this).symm⟩
      fun h1l => by
      obtain ⟨x, y⟩ := b
      exact by
        have bm : (_ * ⟨_, _⟩ : ℤ√d a1) = 1 := Pell.isPell_norm.1 hp
        have y0l : (0 : ℤ√d a1) < ⟨x - x, y - -y⟩ :=
          sub_lt_sub h1l fun hn : (1 : ℤ√d a1) ≤ ⟨x, -y⟩ => by
            have t := mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)
            rw [bm, mul_one] at t
            exact h1l t
        have yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩ :=
          show (⟨x, y⟩ - ⟨x, -y⟩ : ℤ√d a1) < ⟨a, 1⟩ - ⟨a, -1⟩ from
            sub_lt_sub ha fun hn : (⟨x, -y⟩ : ℤ√d a1) ≤ ⟨a, -1⟩ => by
              have t := mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)) a1p
              rw [bm, one_mul, mul_assoc, Eq.trans (mul_comm _ _) a1m, mul_one] at t
              exact ha t
        simp only [sub_self, sub_neg_eq_add] at y0l; simp only [Zsqrtd.re_neg, add_neg_cancel,
          Zsqrtd.im_neg, neg_neg] at yl2
        exact
          match y, y0l, (yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩) with
          | 0, y0l, _ => y0l (le_refl 0)
          | (y + 1 : ℕ), _, yl2 =>
            yl2
              (Zsqrtd.le_of_le_le (by simp)
                (let t := Int.ofNat_le_ofNat_of_le (Nat.succ_pos y)
                add_le_add t t))
          | Int.negSucc _, y0l, _ => y0l trivial

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.eq_pellZd** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_pellZd (b : Int√(d a1)) (b1 : 1 <= b) (hp : IsPell b) : exists n, b = p
ellZd a1 n
参数：b : Int√(d a1)；b1 : 1 <= b；hp : IsPell b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.le_arch`：le_arch (a : Int√d) : exists n : Nat, a <= n
· 使用定理 `Pell.eq_pell_lem`：eq_pell_lem : forall (n) (b : Int√(d a1)), 1 <= b -> I
sPell b -> b <= pellZd a1 n -> exists n, b = pellZd a1 n | 0, _ => fun h1 _ hl =
> ⟨0, …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.natCast_val`：natCast_val (n : Nat) : (n : Int√d) = ⟨n, 0⟩
· 使用定理 `Zsqrtd.le_of_le_le`：le_of_le_le {x y z w : Int} (xz : x <= z) (yw : y <=
 w) : (⟨x, y⟩ : Int√d) <= ⟨z, w⟩
· 使用定理 `Int.ofNat_le_ofNat_of_le`：∀ {m n : ℕ}, m ≤ n → ↑m ≤ ↑n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Pell.n_lt_xn`：n_lt_xn (n) : n < xn a1 n
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
theorem eq_pellZd (b : ℤ√(d a1)) (b1 : 1 ≤ b) (hp : IsPell b) : ∃ n, b = pellZd a1 n :=
  let ⟨n, h⟩ := @Zsqrtd.le_arch (d a1) b
  eq_pell_lem a1 n b b1 hp <|
    h.trans <| by
      rw [Zsqrtd.natCast_val]
      exact
        Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| le_of_lt <| n_lt_xn _ _)
          (Int.natCast_nonneg _)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Every solution to **Pell's equation** is recursively obtained from the initial solution
`(1,0)` using the recursion `pell`. -/
/-
**Pell.eq_pell** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_pell {x y : Nat} (hp : x * x - d a1 * y * y = 1) : exists n, x = xn a1 
n ∧ y = yn a1 n
参数：hp : x * x - d a1 * y * y = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Zsqrtd.le_of_le_le`：le_of_le_le {x y z w : Int} (xz : x <= z) (yw : y <=
 w) : (⟨x, y⟩ : Int√d) <= ⟨z, w⟩
· 使用定理 `Int.ofNat_le_ofNat_of_le`：∀ {m n : ℕ}, m ≤ n → ↑m ≤ ↑n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Pell.eq_pellZd`：eq_pellZd (b : Int√(d a1)) (b1 : 1 <= b) (hp : IsPell b)
 : exists n, b = pellZd a1 n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pell.isPell_nat`：isPell_nat {x y : Nat} : IsPell (⟨x, y⟩ : Int√(d a1)) ↔
 x * x - d a1 * y * y = 1

--- 原说明 ---
Every solution to **Pell's equation** is recursively obtained from the initial s
olution
`(1,0)` using the recursion `pell`.
-/
theorem eq_pell {x y : ℕ} (hp : x * x - d a1 * y * y = 1) : ∃ n, x = xn a1 n ∧ y = yn a1 n :=
  have : (1 : ℤ√(d a1)) ≤ ⟨x, y⟩ :=
    match x, hp with
    | 0, (hp : 0 - _ = 1) => by rw [zero_tsub] at hp; contradiction
    | x + 1, _hp =>
      Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| Nat.succ_pos x) (Int.natCast_nonneg _)
  let ⟨m, e⟩ := eq_pellZd a1 ⟨x, y⟩ this ((isPell_nat a1).2 hp)
  ⟨m,
    match x, y, e with
    | _, _, rfl => ⟨rfl, rfl⟩⟩
/-
**Pell.pellZd_add** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) (m n : ℕ), Pell.pellZd a1 (m + n) = Pell.pellZd a1 
m * Pell.pellZd a1 n
参数：a1 : 1 < a；m n : ℕ；m + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pellZd_add (m) : ∀ n, pellZd a1 (m + n) = pellZd a1 m * pellZd a1 n
  | 0 => (mul_one _).symm
  | n + 1 => by rw [← add_assoc, pellZd_succ, pellZd_succ, pellZd_add _ n, ← mul_assoc]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.xn_add** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_add (m n) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 
n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.pellZd_add`：∀ {a : ℕ} (a1 : 1 < a) (m n : ℕ), Pell.pellZd a1 (m + n
) = Pell.pellZd a1 m * Pell.pellZd a1 n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem xn_add (m n) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 n := by
  injection pellZd_add a1 m n with h _
  zify
  rw [h]
  simp [pellZd]
/-
**Pell.yn_add** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yn_add (m n) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n
参数：m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.pellZd_add`：∀ {a : ℕ} (a1 : 1 < a) (m n : ℕ), Pell.pellZd a1 (m + n
) = Pell.pellZd a1 m * Pell.pellZd a1 n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem yn_add (m n) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n := by
  injection pellZd_add a1 m n with _ h
  zify
  rw [h]
  simp [pellZd]
/-
**Pell.pellZd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pellZd_sub {m n} (h : n <= m) : pellZd a1 (m - n) = pellZd a1 m * star (pe
llZd a1 n)
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.pellZd_add`：∀ {a : ℕ} (a1 : 1 < a) (m n : ℕ), Pell.pellZd a1 (m + n
) = Pell.pellZd a1 m * Pell.pellZd a1 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pell.isPell_norm`：∀ {d : ℤ} {b : ℤ√d}, Pell.IsPell b ↔ b * star b = 1
· 使用定理 `Pell.isPell_pellZd`：isPell_pellZd : forall n : Nat, IsPell (pellZd a1 n)
 | 0 => rfl | n + 1 => by let o
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem pellZd_sub {m n} (h : n ≤ m) : pellZd a1 (m - n) = pellZd a1 m * star (pellZd a1 n) := by
  let t := pellZd_add a1 n (m - n)
  rw [add_tsub_cancel_of_le h] at t
  rw [t, mul_comm (pellZd _ n) _, mul_assoc, isPell_norm.1 (isPell_pellZd _ _), mul_one]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.xz_sub** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xz_sub {m n} (h : n <= m) : xz a1 (m - n) = xz a1 m * xz a1 n - d a1 * yz 
a1 m * yz a1 n
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Pell.pellZd_sub`：pellZd_sub {m n} (h : n <= m) : pellZd a1 (m - n) = pel
lZd a1 m * star (pellZd a1 n)
-/
theorem xz_sub {m n} (h : n ≤ m) :
    xz a1 (m - n) = xz a1 m * xz a1 n - d a1 * yz a1 m * yz a1 n := by
  rw [sub_eq_add_neg, ← mul_neg]
  exact congr_arg Zsqrtd.re (pellZd_sub a1 h)
/-
**Pell.yz_sub** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yz_sub {m n} (h : n <= m) : yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * 
yz a1 n
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Pell.pellZd_sub`：pellZd_sub {m n} (h : n <= m) : pellZd a1 (m - n) = pel
lZd a1 m * star (pellZd a1 n)
-/
theorem yz_sub {m n} (h : n ≤ m) : yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * yz a1 n := by
  rw [sub_eq_add_neg, ← mul_neg, mul_comm, add_comm]
  exact congr_arg Zsqrtd.im (pellZd_sub a1 h)
/-
**Pell.xy_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xy_coprime (n) : (xn a1 n).Coprime (yn a1 n)
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_of_dvd'`：coprime_of_dvd' {m n : Nat} (H : forall k, Prime k 
-> k ∣ m -> k ∣ n -> k ∣ 1) : Coprime m n
· 使用定理 `Pell.pell_eq`：pell_eq (n : Nat) : xn a1 n * xn a1 n - d a1 * yn a1 n * y
n a1 n = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_sub`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m - n
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
-/
theorem xy_coprime (n) : (xn a1 n).Coprime (yn a1 n) :=
  Nat.coprime_of_dvd' fun k _ kx ky => by
    let p := pell_eq a1 n
    rw [← p]
    exact Nat.dvd_sub (kx.mul_left _) (ky.mul_left _)
/-
**Pell.strictMono_y** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：strictMono_y : StrictMono (yn a1) | _, 0, h => absurd h Nat.not_lt_zero _ 
| m, n + 1, h => by have : yn a1 m <= yn a1 n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem strictMono_y : StrictMono (yn a1)
  | _, 0, h => absurd h <| Nat.not_lt_zero _
  | m, n + 1, h => by
    have : yn a1 m ≤ yn a1 n :=
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_y hl)
        fun e => by rw [e]
    simp only [yn_succ, gt_iff_lt]; refine lt_of_le_of_lt ?_ (Nat.lt_add_of_pos_left <| x_pos a1 n)
    rw [← mul_one (yn a1 m)]
    exact mul_le_mul this (le_of_lt a1) (Nat.zero_le _) (Nat.zero_le _)
/-
**Pell.strictMono_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：strictMono_x : StrictMono (xn a1) | _, 0, h => absurd h Nat.not_lt_zero _ 
| m, n + 1, h => by have : xn a1 m <= xn a1 n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem strictMono_x : StrictMono (xn a1)
  | _, 0, h => absurd h <| Nat.not_lt_zero _
  | m, n + 1, h => by
    have : xn a1 m ≤ xn a1 n :=
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strictMono_x hl)
        fun e => by rw [e]
    simp only [xn_succ, gt_iff_lt]
    refine lt_of_lt_of_le (lt_of_le_of_lt this ?_) (Nat.le_add_right _ _)
    have t := Nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n)
    rwa [mul_one] at t
/-
**Pell.yn_ge_n** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), n ≤ Pell.yn a1 n
参数：a1 : 1 < a；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yn_ge_n : ∀ n, n ≤ yn a1 n
  | 0 => Nat.zero_le _
  | n + 1 =>
    show n < yn a1 (n + 1) from lt_of_le_of_lt (yn_ge_n n) (strictMono_y a1 <| Nat.lt_succ_self n)
/-
**Pell.y_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) (n k : ℕ), Pell.yn a1 n ∣ Pell.yn a1 (n * k)
参数：a1 : 1 < a；n k : ℕ；n * k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem y_mul_dvd (n) : ∀ k, yn a1 n ∣ yn a1 (n * k)
  | 0 => dvd_zero _
  | k + 1 => by
    rw [Nat.mul_succ, yn_add]; exact dvd_add (dvd_mul_left _ _) ((y_mul_dvd _ k).mul_right _)
/-
**Pell.y_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：y_dvd_iff (m n) : yn a1 m ∣ yn a1 n ↔ m ∣ n
参数：m n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.Coprime.coprime_dvd_right`：∀ {n m k : ℕ}, n ∣ m → k.Coprime m → k.Co
prime n
· 使用定理 `Pell.y_mul_dvd`：∀ {a : ℕ} (a1 : 1 < a) (n k : ℕ), Pell.yn a1 n ∣ Pell.yn
 a1 (n * k)
· 使用定理 `Pell.xy_coprime`：xy_coprime (n) : (xn a1 n).Coprime (yn a1 n)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Pell.strictMono_y`：strictMono_y : StrictMono (yn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : yn a1 m <= yn a1 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_add_iff_right`：∀ {k m n : ℕ}, k ∣ m → (k ∣ n ↔ k ∣ m + n)
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
· 使用定理 `Pell.yn_add`：yn_add (m n) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m 
* xn a1 n
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
theorem y_dvd_iff (m n) : yn a1 m ∣ yn a1 n ↔ m ∣ n :=
  ⟨fun h =>
    Nat.dvd_of_mod_eq_zero <|
      (Nat.eq_zero_or_pos _).resolve_right fun hp => by
        have co : Nat.Coprime (yn a1 m) (xn a1 (m * (n / m))) :=
          Nat.Coprime.symm <| (xy_coprime a1 _).coprime_dvd_right (y_mul_dvd a1 m (n / m))
        have m0 : 0 < m :=
          m.eq_zero_or_pos.resolve_left fun e => by
            rw [e, Nat.mod_zero] at hp;rw [e] at h
            exact _root_.ne_of_lt (strictMono_y a1 hp) (eq_zero_of_zero_dvd h).symm
        rw [← Nat.mod_add_div n m, yn_add] at h
        exact
          not_le_of_gt (strictMono_y _ <| Nat.mod_lt n m0)
            (Nat.le_of_dvd (strictMono_y _ hp) <|
              co.dvd_of_dvd_mul_right <|
                (Nat.dvd_add_iff_right <| (y_mul_dvd _ _ _).mul_left _).2 h),
    fun ⟨k, e⟩ => by rw [e]; apply y_mul_dvd⟩
/-
**Pell.xy_modEq_yn** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xy_modEq_yn (n) : forall k, xn a1 (n * k) ≡ xn a1 n ^ k [MOD yn a1 n ^ 2] 
∧ yn a1 (n * k) ≡ k * xn a1 n ^ (k - 1) * yn a1 n [MOD yn a1 n ^ 3] | 0 => by si
mp [Nat.ModEq.refl] | k + 1 => by let ⟨hx, hy⟩
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xy_modEq_yn (n) :
    ∀ k, xn a1 (n * k) ≡ xn a1 n ^ k [MOD yn a1 n ^ 2] ∧ yn a1 (n * k) ≡
        k * xn a1 n ^ (k - 1) * yn a1 n [MOD yn a1 n ^ 3]
  | 0 => by simp [Nat.ModEq.refl]
  | k + 1 => by
    let ⟨hx, hy⟩ := xy_modEq_yn n k
    have L : xn a1 (n * k) * xn a1 n + d a1 * yn a1 (n * k) * yn a1 n ≡
        xn a1 n ^ k * xn a1 n + 0 [MOD yn a1 n ^ 2] := by
      gcongr
      rw [modEq_zero_iff_dvd, sq]
      gcongr
      apply dvd_mul_of_dvd_right
      rw [← modEq_zero_iff_dvd]
      refine (hy.of_dvd <| dvd_pow_self _ <| by decide).trans ?_
      simp [modEq_zero_iff_dvd]
    have R : xn a1 (n * k) * yn a1 n + yn a1 (n * k) * xn a1 n ≡
        xn a1 n ^ k * yn a1 n + k * xn a1 n ^ k * yn a1 n [MOD yn a1 n ^ 3] := by
      gcongr ?_ + ?_
      · rw [_root_.pow_succ]
        exact hx.mul_right' _
      · have : k * xn a1 n ^ (k - 1) * yn a1 n * xn a1 n = k * xn a1 n ^ k * yn a1 n := by
          rcases k with - | k <;> simp [_root_.pow_succ]; ring_nf
        rw [← this]
        gcongr
    rw [add_tsub_cancel_right, Nat.mul_succ, xn_add, yn_add, pow_succ (xn _ n), Nat.succ_mul,
      add_comm (k * xn _ n ^ k) (xn _ n ^ k), right_distrib]
    exact ⟨L, R⟩
/-
**Pell.ysq_dvd_yy** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：ysq_dvd_yy (n) : yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n)
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用引理 `Nat.ModEq.of_dvd`：of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Pell.xy_modEq_yn`：xy_modEq_yn (n) : forall k, xn a1 (n * k) ≡ xn a1 n ^ 
k [MOD yn a1 n ^ 2] ∧ yn a1 (n * k) ≡ k * xn a1 n ^ (k - 1) * yn a1 n [MOD yn a1
 n ^ 3…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem ysq_dvd_yy (n) : yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n) :=
  modEq_zero_iff_dvd.1 <|
    ((xy_modEq_yn a1 n (yn a1 n)).right.of_dvd <| by simp [_root_.pow_succ]).trans
      (modEq_zero_iff_dvd.2 <| by simp [mul_dvd_mul_left, mul_assoc])
/-
**Pell.dvd_of_ysq_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：dvd_of_ysq_dvd {n t} (h : yn a1 n * yn a1 n ∣ yn a1 t) : yn a1 n ∣ t
参数：h : yn a1 n * yn a1 n ∣ yn a1 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pell.y_dvd_iff`：y_dvd_iff (m n) : yn a1 m ∣ yn a1 n ↔ m ∣ n
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dvd_of_mul_dvd_mul_right`：∀ {k m n : ℕ}, 0 < k → m * k ∣ n * k → m ∣
 n
· 使用定理 `Pell.strictMono_y`：strictMono_y : StrictMono (yn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : yn a1 m <= yn a1 n
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Pell.xy_modEq_yn`：xy_modEq_yn (n) : forall k, xn a1 (n * k) ≡ xn a1 n ^ 
k [MOD yn a1 n ^ 2] ∧ yn a1 (n * k) ≡ k * xn a1 n ^ (k - 1) * yn a1 n [MOD yn a1
 n ^ 3…
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用引理 `Nat.ModEq.of_dvd`：of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Pell.xy_coprime`：xy_coprime (n) : (xn a1 n).Coprime (yn a1 n)
-/
theorem dvd_of_ysq_dvd {n t} (h : yn a1 n * yn a1 n ∣ yn a1 t) : yn a1 n ∣ t :=
  have nt : n ∣ t := (y_dvd_iff a1 n t).1 <| dvd_of_mul_left_dvd h
  n.eq_zero_or_pos.elim (fun n0 => by rwa [n0] at nt ⊢) fun n0l : 0 < n => by
    let ⟨k, ke⟩ := nt
    have : yn a1 n ∣ k * xn a1 n ^ (k - 1) :=
      Nat.dvd_of_mul_dvd_mul_right (strictMono_y a1 n0l) <|
        modEq_zero_iff_dvd.1 <| by
          have xm := (xy_modEq_yn a1 n k).right; rw [← ke] at xm
          exact (xm.of_dvd <| by simp [_root_.pow_succ]).symm.trans h.modEq_zero_nat
    rw [ke]
    exact dvd_mul_of_dvd_right (((xy_coprime _ _).pow_left _).symm.dvd_of_dvd_mul_right this) _
/-
**Pell.pellZd_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pellZd_succ_succ (n) : pellZd a1 (n + 2) + pellZd a1 n = (2 * a : Nat) * p
ellZd a1 (n + 1)
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pell.pellZd_succ`：pellZd_succ (n : Nat) : pellZd a1 (n + 1) = pellZd a1 
n * ⟨a, 1⟩
· 使用定理 `Pell.dz_val`：dz_val : ↑(d a1) = az a * az a - 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 59 条，此处仅展示前 30 条）
-/
theorem pellZd_succ_succ (n) :
    pellZd a1 (n + 2) + pellZd a1 n = (2 * a : ℕ) * pellZd a1 (n + 1) := by
  ext <;> simp [dz_val, az] <;> ring_nf
/-
**Pell.xy_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xy_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1) ∧ yn a1
 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1)
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.pellZd_succ_succ`：pellZd_succ_succ (n) : pellZd a1 (n + 2) + pellZd
 a1 n = (2 * a : Nat) * pellZd a1 (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.nsmul_val`：nsmul_val (n : Nat) (x y : Int) : (n : Int√d) * ⟨x, y⟩
 = ⟨n * x, n * y⟩
-/
theorem xy_succ_succ (n) :
    xn a1 (n + 2) + xn a1 n =
      2 * a * xn a1 (n + 1) ∧ yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1) := by
  have := pellZd_succ_succ a1 n; unfold pellZd at this
  rw [Zsqrtd.nsmul_val (2 * a : ℕ)] at this
  injection this with h₁ h₂
  grind
/-
**Pell.xn_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1)
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Pell.xy_succ_succ`：xy_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * 
xn a1 (n + 1) ∧ yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1)
-/
theorem xn_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1) :=
  (xy_succ_succ a1 n).1
/-
**Pell.yn_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yn_succ_succ (n) : yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1)
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Pell.xy_succ_succ`：xy_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * 
xn a1 (n + 1) ∧ yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1)
-/
theorem yn_succ_succ (n) : yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1) :=
  (xy_succ_succ a1 n).2
/-
**Pell.xz_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xz_succ_succ (n) : xz a1 (n + 2) = (2 * a : Nat) * xz a1 (n + 1) - xz a1 n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Pell.xn_succ_succ`：xn_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * 
xn a1 (n + 1)
-/
theorem xz_succ_succ (n) : xz a1 (n + 2) = (2 * a : ℕ) * xz a1 (n + 1) - xz a1 n :=
  eq_sub_of_add_eq <| by delta xz; rw [← Int.natCast_add, ← Int.natCast_mul, xn_succ_succ]
/-
**Pell.yz_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：yz_succ_succ (n) : yz a1 (n + 2) = (2 * a : Nat) * yz a1 (n + 1) - yz a1 n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Pell.yn_succ_succ`：yn_succ_succ (n) : yn a1 (n + 2) + yn a1 n = 2 * a * 
yn a1 (n + 1)
-/
theorem yz_succ_succ (n) : yz a1 (n + 2) = (2 * a : ℕ) * yz a1 (n + 1) - yz a1 n :=
  eq_sub_of_add_eq <| by delta yz; rw [← Int.natCast_add, ← Int.natCast_mul, yn_succ_succ]
/-
**Pell.yn_modEq_a_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), Pell.yn a1 n ≡ n [MOD a - 1]
参数：a1 : 1 < a；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yn_modEq_a_sub_one : ∀ n, yn a1 n ≡ n [MOD a - 1]
  | 0 => by simp [Nat.ModEq.refl]
  | 1 => by simp [Nat.ModEq.refl]
  | n + 2 =>
    (yn_modEq_a_sub_one n).add_right_cancel <| by
      rw [yn_succ_succ, (by ring : n + 2 + n = 2 * (n + 1))]
      exact ((modEq_sub a1.le).mul_left 2).mul (yn_modEq_a_sub_one (n + 1))
/-
**Pell.yn_modEq_two** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), Pell.yn a1 n ≡ n [MOD 2]
参数：a1 : 1 < a；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yn_modEq_two : ∀ n, yn a1 n ≡ n [MOD 2]
  | 0 => by rfl
  | 1 => by simp [Nat.ModEq.refl]
  | n + 2 =>
    (yn_modEq_two n).add_right_cancel <| by
      rw [yn_succ_succ, mul_assoc, (by ring : n + 2 + n = 2 * (n + 1))]
      exact (dvd_mul_right 2 _).modEq_zero_nat.trans (dvd_mul_right 2 _).zero_modEq_nat

section

/-
**Pell.x_sub_y_dvd_pow_lem** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : Int) : (a2 * yn1 - y
n0) * ay + y2 - (a2 * xn1 - xn0) = y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1
) - (yn0 * ay + y0 - xn0)
参数：y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 33 条，此处仅展示前 30 条）
-/
theorem x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : ℤ) :
    (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) =
      y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) := by
  ring

end

/-
**Pell.x_sub_y_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：x_sub_y_dvd_pow (y : Nat) : forall n, (2 * a * y - y * y - 1 : Int) ∣ yz a
1 n * (a - y) + ↑(y ^ n) - xz a1 n | 0 => by simp [xz, yz] | 1 => by simp [xz, y
z] | n + 2 => by have : (2 * a * y - y * y - 1 : Int) ∣ ↑(y ^ (n + 2)) - ↑(2 * a
) * ↑(y ^ (n + 1)) + ↑(y ^ n)
参数：y : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem x_sub_y_dvd_pow (y : ℕ) :
    ∀ n, (2 * a * y - y * y - 1 : ℤ) ∣ yz a1 n * (a - y) + ↑(y ^ n) - xz a1 n
  | 0 => by simp [xz, yz]
  | 1 => by simp [xz, yz]
  | n + 2 => by
    have : (2 * a * y - y * y - 1 : ℤ) ∣ ↑(y ^ (n + 2)) - ↑(2 * a) * ↑(y ^ (n + 1)) + ↑(y ^ n) :=
      ⟨-↑(y ^ n), by
        simp [_root_.pow_succ, mul_comm, mul_left_comm]
        ring⟩
    rw [xz_succ_succ, yz_succ_succ, x_sub_y_dvd_pow_lem ↑(y ^ (n + 2)) ↑(y ^ (n + 1)) ↑(y ^ n)]
    exact _root_.dvd_sub (dvd_add this <| (x_sub_y_dvd_pow _ (n + 1)).mul_left _)
      (x_sub_y_dvd_pow _ n)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Pell.xn_modEq_x2n_add_lem** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_modEq_x2n_add_lem (n j) : xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j
) + xn a1 j
参数：n j。
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
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_eq_of_eq_sub'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 b = c - a → a + b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pell.pell_eqz`：pell_eqz (n : Nat) : xz a1 n * xz a1 n - d a1 * yz a1 n *
 yz a1 n = 1
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem xn_modEq_x2n_add_lem (n j) : xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j := by
  have h1 : d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j =
      (d a1 * yn a1 n * yn a1 n + 1) * xn a1 j := by
    simp [add_mul, mul_assoc]
  have h2 : d a1 * yn a1 n * yn a1 n + 1 = xn a1 n * xn a1 n := by
    zify at *
    apply add_eq_of_eq_sub' (Eq.symm (pell_eqz a1 n))
  rw [h2] at h1; rw [h1, mul_assoc]; exact dvd_mul_right _ _
/-
**Pell.xn_modEq_x2n_add** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_modEq_x2n_add (n j) : xn a1 (2 * n + j) + xn a1 j ≡ 0 [MOD xn a1 n]
参数：n j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Pell.xn_add`：xn_add (m n) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * y
n a1 m * yn a1 n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Pell.yn_add`：yn_add (m n) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m 
* xn a1 n
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
· 使用定理 `Pell.xn_modEq_x2n_add_lem`：xn_modEq_x2n_add_lem (n j) : xn a1 n ∣ d a1 *
 yn a1 n * (yn a1 n * xn a1 j) + xn a1 j
-/
theorem xn_modEq_x2n_add (n j) : xn a1 (2 * n + j) + xn a1 j ≡ 0 [MOD xn a1 n] := by
  rw [two_mul, add_assoc, xn_add, add_assoc, ← zero_add 0]
  refine (dvd_mul_right (xn a1 n) (xn a1 (n + j))).modEq_zero_nat.add ?_
  rw [yn_add, left_distrib, add_assoc, ← zero_add 0]
  exact
    ((dvd_mul_right _ _).mul_left _).modEq_zero_nat.add (xn_modEq_x2n_add_lem _ _ _).modEq_zero_nat
/-
**Pell.xn_modEq_x2n_sub_lem** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_modEq_x2n_sub_lem {n j} (h : j <= n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 
[MOD xn a1 n]
参数：h : j <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.yz_sub`：yz_sub {m n} (h : n <= m) : yz a1 (m - n) = xz a1 n * yz a1
 m - xz a1 m * yz a1 n
· 使用定理 `mul_sub_left_distrib`：mul_sub_left_distrib (a b c : α) : a * (b - c) = a
 * b - a * c
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `dvd_sub`：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pell.xn_modEq_x2n_add_lem`：xn_modEq_x2n_add_lem (n j) : xn a1 n ∣ d a1 *
 yn a1 n * (yn a1 n * xn a1 j) + xn a1 j
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Pell.xn_add`：xn_add (m n) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * y
n a1 m * yn a1 n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem xn_modEq_x2n_sub_lem {n j} (h : j ≤ n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n] := by
  have h1 : xz a1 n ∣ d a1 * yz a1 n * yz a1 (n - j) + xz a1 j := by
    rw [yz_sub _ h, mul_sub_left_distrib, sub_add_eq_add_sub]
    exact
      dvd_sub
        (by
          delta xz; delta yz
          rw [mul_comm (xn _ _ : ℤ)]
          exact mod_cast (xn_modEq_x2n_add_lem _ n j))
        ((dvd_mul_right _ _).mul_left _)
  rw [two_mul, add_tsub_assoc_of_le h, xn_add, add_assoc, ← zero_add 0]
  exact
    (dvd_mul_right _ _).modEq_zero_nat.add
      (Int.natCast_dvd_natCast.1 <| by simpa [xz, yz] using h1).modEq_zero_nat
/-
**Pell.xn_modEq_x2n_sub** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_modEq_x2n_sub {n j} (h : j <= 2 * n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 
[MOD xn a1 n]
参数：h : j <= 2 * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Pell.xn_modEq_x2n_sub_lem`：xn_modEq_x2n_sub_lem {n j} (h : j <= n) : xn 
a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `Nat.le_of_add_le_add_right`：∀ {a b c : ℕ}, a + b ≤ c + b → a ≤ c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem xn_modEq_x2n_sub {n j} (h : j ≤ 2 * n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n] :=
  (le_total j n).elim (xn_modEq_x2n_sub_lem a1) fun jn => by
    have : 2 * n - j + j ≤ n + j := by
      rw [tsub_add_cancel_of_le h, two_mul]; exact Nat.add_le_add_left jn _
    let t := xn_modEq_x2n_sub_lem a1 (Nat.le_of_add_le_add_right this)
    rwa [tsub_tsub_cancel_of_le h, add_comm] at t
/-
**Pell.xn_modEq_x4n_add** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_modEq_x4n_add (n j) : xn a1 (4 * n + j) ≡ xn a1 j [MOD xn a1 n]
参数：n j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add_right_cancel'`：∀ {n a b : ℕ} (c : ℕ), a + c ≡ b + c [MOD n
] → a ≡ b [MOD n]
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Pell.xn_modEq_x2n_add`：xn_modEq_x2n_add (n j) : xn a1 (2 * n + j) + xn a
1 j ≡ 0 [MOD xn a1 n]
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
-/
theorem xn_modEq_x4n_add (n j) : xn a1 (4 * n + j) ≡ xn a1 j [MOD xn a1 n] :=
  ModEq.add_right_cancel' (xn a1 (2 * n + j)) <| by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_add _ _ _).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n, add_assoc]
    apply xn_modEq_x2n_add
/-
**Pell.xn_modEq_x4n_sub** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：xn_modEq_x4n_sub {n j} (h : j <= 2 * n) : xn a1 (4 * n - j) ≡ xn a1 j [MOD
 xn a1 n]
参数：h : j <= 2 * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.ModEq.add_right_cancel'`：∀ {n a b : ℕ} (c : ℕ), a + c ≡ b + c [MOD n
] → a ≡ b [MOD n]
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Pell.xn_modEq_x2n_add`：xn_modEq_x2n_add (n j) : xn a1 (2 * n + j) + xn a
1 j ≡ 0 [MOD xn a1 n]
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Pell.xn_modEq_x2n_sub`：xn_modEq_x2n_sub {n j} (h : j <= 2 * n) : xn a1 (
2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n]
-/
theorem xn_modEq_x4n_sub {n j} (h : j ≤ 2 * n) : xn a1 (4 * n - j) ≡ xn a1 j [MOD xn a1 n] :=
  have h' : j ≤ 2 * n := le_trans h (by rw [Nat.succ_mul])
  ModEq.add_right_cancel' (xn a1 (2 * n - j)) <| by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_sub _ h).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n, add_tsub_assoc_of_le h']
    apply xn_modEq_x2n_add
/-
**Pell.eq_of_xn_modEq_lem1** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a : ℕ} (a1 : 1 < a) {i n j : ℕ}, i < j → j < n → Pell.xn a1 i % Pell.xn
 a1 n < Pell.xn a1 j % Pell.xn a1 n
参数：a1 : 1 < a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_xn_modEq_lem1 {i n} : ∀ {j}, i < j → j < n → xn a1 i % xn a1 n < xn a1 j % xn a1 n
  | 0, ij, _ => absurd ij (Nat.not_lt_zero _)
  | j + 1, ij, jn => by
    suffices xn a1 j % xn a1 n < xn a1 (j + 1) % xn a1 n from
      (lt_or_eq_of_le (Nat.le_of_succ_le_succ ij)).elim
        (fun h => lt_trans (eq_of_xn_modEq_lem1 h (le_of_lt jn)) this) fun h => by
        rw [h]; exact this
    rw [Nat.mod_eq_of_lt (strictMono_x _ (Nat.lt_of_succ_lt jn)),
        Nat.mod_eq_of_lt (strictMono_x _ jn)]
    exact strictMono_x _ (Nat.lt_succ_self _)
/-
**Pell.eq_of_xn_modEq_lem2** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_of_xn_modEq_lem2 {n} (h : 2 * xn a1 n = xn a1 (n + 1)) : a = 2 ∧ n = 0
参数：h : 2 * xn a1 n = xn a1 (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.lt_add_of_pos_right`：∀ {k n : ℕ}, 0 < k → n < n + k
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Pell.d_pos`：d_pos : 0 < d a1
· 使用定理 `Pell.strictMono_y`：strictMono_y : StrictMono (yn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : yn a1 m <= yn a1 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Pell.xn_succ`：xn_succ (n : Nat) : xn a1 (n + 1) = xn a1 n * a + d a1 * y
n a1 n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem eq_of_xn_modEq_lem2 {n} (h : 2 * xn a1 n = xn a1 (n + 1)) : a = 2 ∧ n = 0 := by
  rw [xn_succ, mul_comm] at h
  have : n = 0 :=
    n.eq_zero_or_pos.resolve_right fun np =>
      _root_.ne_of_lt
        (lt_of_le_of_lt (Nat.mul_le_mul_left _ a1)
          (Nat.lt_add_of_pos_right <| mul_pos (d_pos a1) (strictMono_y a1 np)))
        h
  cases this; simp at h; exact ⟨h.symm, rfl⟩
/-
**Pell.eq_of_xn_modEq_lem3** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_of_xn_modEq_lem3 {i n} (npos : 0 < n) : forall {j}, i < j -> j <= 2 * n
 -> j != n -> ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) -> xn a1 i % xn a1 n < xn a1 j % 
xn a1 n | 0, ij, _, _, _ => absurd ij (Nat.not_lt_zero _) | j + 1, ij, j2n, jnn,
 ntriv => have lem2 : forall k > n, k <= 2 * n -> (↑(xn a1 k % xn a1 n) : Int) =
 xn a1 n - xn a1 (2 * n - k)
参数：npos : 0 < n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_xn_modEq_lem3 {i n} (npos : 0 < n) :
    ∀ {j}, i < j → j ≤ 2 * n → j ≠ n → ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) →
        xn a1 i % xn a1 n < xn a1 j % xn a1 n
  | 0, ij, _, _, _ => absurd ij (Nat.not_lt_zero _)
  | j + 1, ij, j2n, jnn, ntriv =>
    have lem2 : ∀ k > n, k ≤ 2 * n → (↑(xn a1 k % xn a1 n) : ℤ) =
        xn a1 n - xn a1 (2 * n - k) := fun k kn k2n => by
      let k2nl : 2 * n - k < n := by lia
      have xle : xn a1 (2 * n - k) ≤ xn a1 n := le_of_lt <| strictMono_x a1 k2nl
      suffices xn a1 k % xn a1 n = xn a1 n - xn a1 (2 * n - k) by rw [this, Int.ofNat_sub xle]
      rw [← Nat.mod_eq_of_lt (Nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n - k)))]
      apply ModEq.add_right_cancel' (xn a1 (2 * n - k))
      rw [tsub_add_cancel_of_le xle]
      have t := xn_modEq_x2n_sub_lem a1 k2nl.le
      rw [tsub_tsub_cancel_of_le k2n] at t
      exact t.trans dvd_rfl.zero_modEq_nat
    (lt_trichotomy j n).elim (fun jn : j < n => eq_of_xn_modEq_lem1 _ ij (lt_of_le_of_ne jn jnn))
      fun o =>
      o.elim
        (fun jn : j = n => by
          cases jn
          apply Int.lt_of_ofNat_lt_ofNat
          rw [lem2 (n + 1) (Nat.lt_succ_self _) j2n,
            show 2 * n - (n + 1) = n - 1 by
              rw [two_mul, tsub_add_eq_tsub_tsub, add_tsub_cancel_right]]
          refine lt_sub_left_of_add_lt (Int.ofNat_lt_ofNat_of_lt ?_)
          rcases lt_or_eq_of_le <| Nat.le_of_succ_le_succ ij with lin | ein
          · rw [Nat.mod_eq_of_lt (strictMono_x _ lin)]
            have ll : xn a1 (n - 1) + xn a1 (n - 1) ≤ xn a1 n := by
              rw [← two_mul, mul_comm,
                show xn a1 n = xn a1 (n - 1 + 1) by rw [tsub_add_cancel_of_le (succ_le_of_lt npos)],
                xn_succ]
              exact le_trans (Nat.mul_le_mul_left _ a1) (Nat.le_add_right _ _)
            have npm : (n - 1).succ = n := Nat.succ_pred_eq_of_pos npos
            have il : i ≤ n - 1 := by
              apply Nat.le_of_succ_le_succ
              rw [npm]
              exact lin
            rcases lt_or_eq_of_le il with ill | ile
            · exact lt_of_lt_of_le (Nat.add_lt_add_left (strictMono_x a1 ill) _) ll
            · rw [ile]
              apply lt_of_le_of_ne ll
              rw [← two_mul]
              exact fun e =>
                ntriv <| by
                  let ⟨a2, s1⟩ :=
                    @eq_of_xn_modEq_lem2 _ a1 (n - 1)
                      (by rwa [tsub_add_cancel_of_le (succ_le_of_lt npos)])
                  have n1 : n = 1 := le_antisymm (tsub_eq_zero_iff_le.mp s1) npos
                  rw [ile, a2, n1]; exact ⟨rfl, rfl, rfl, rfl⟩
          · rw [ein, Nat.mod_self, add_zero]
            exact strictMono_x _ (Nat.pred_lt npos.ne'))
        fun jn : j > n =>
        have lem1 : j ≠ n → xn a1 j % xn a1 n < xn a1 (j + 1) % xn a1 n →
            xn a1 i % xn a1 n < xn a1 (j + 1) % xn a1 n :=
          fun jn s =>
          (lt_or_eq_of_le (Nat.le_of_succ_le_succ ij)).elim
            (fun h =>
              lt_trans
                (eq_of_xn_modEq_lem3 npos h (le_of_lt (Nat.lt_of_succ_le j2n)) jn
                    fun ⟨_, n1, _, j2⟩ => by
                      rw [n1, j2] at j2n; exact absurd j2n (by decide))
                s)
            fun h => by rw [h]; exact s
        lem1 (_root_.ne_of_gt jn) <|
          Int.lt_of_ofNat_lt_ofNat <| by
            rw [lem2 j jn (le_of_lt j2n), lem2 (j + 1) (Nat.le_succ_of_le jn) j2n]
            refine sub_lt_sub_left (Int.ofNat_lt_ofNat_of_lt <| strictMono_x _ ?_) _
            rw [Nat.sub_succ]
            exact Nat.pred_lt (_root_.ne_of_gt <| tsub_pos_of_lt j2n)
/-
**Pell.eq_of_xn_modEq_le** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_of_xn_modEq_le {i j n} (ij : i <= j) (j2n : j <= 2 * n) (h : xn a1 i ≡ 
xn a1 j [MOD xn a1 n]) (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j
参数：ij : i <= j；j2n : j <= 2 * n；h : xn a1 i ≡ xn a1 j [MOD xn a1 n]；ntriv : ¬(a 
= 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Pell.strictMono_x`：strictMono_x : StrictMono (xn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : xn a1 m <= xn a1 n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Pell.eq_of_xn_modEq_lem3`：eq_of_xn_modEq_lem3 {i n} (npos : 0 < n) : for
all {j}, i < j -> j <= 2 * n -> j != n -> ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) -> xn
 a1 i % xn a1 …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem eq_of_xn_modEq_le {i j n} (ij : i ≤ j) (j2n : j ≤ 2 * n)
    (h : xn a1 i ≡ xn a1 j [MOD xn a1 n])
    (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j :=
  if npos : n = 0 then by simp_all
  else
    (lt_or_eq_of_le ij).resolve_left fun ij' =>
      if jn : j = n then by
        refine _root_.ne_of_gt ?_ h
        rw [jn, Nat.mod_self]
        have x0 : 0 < xn a1 0 % xn a1 n := by
          rw [Nat.mod_eq_of_lt (strictMono_x a1 (Nat.pos_of_ne_zero npos))]
          exact Nat.succ_pos _
        rcases i with - | i
        · exact x0
        rw [jn] at ij'
        exact
          x0.trans
            (eq_of_xn_modEq_lem3 _ (Nat.pos_of_ne_zero npos) (Nat.succ_pos _) (le_trans ij j2n)
              (_root_.ne_of_lt ij') fun ⟨_, n1, _, i2⟩ => by
              rw [n1, i2] at ij'; exact absurd ij' (by decide))
      else _root_.ne_of_lt (eq_of_xn_modEq_lem3 a1 (Nat.pos_of_ne_zero npos) ij' j2n jn ntriv) h
/-
**Pell.eq_of_xn_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_of_xn_modEq {i j n} (i2n : i <= 2 * n) (j2n : j <= 2 * n) (h : xn a1 i 
≡ xn a1 j [MOD xn a1 n]) (ntriv : a = 2 -> n = 1 -> (i = 0 -> j != 2) ∧ (i = 2 -
> j != 0)) : i = j
参数：i2n : i <= 2 * n；j2n : j <= 2 * n；h : xn a1 i ≡ xn a1 j [MOD xn a1 n]；ntriv :
 a = 2 -> n = 1 -> (i = 0 -> j != 2) ∧ (i = 2 -> j != 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Pell.eq_of_xn_modEq_le`：eq_of_xn_modEq_le {i j n} (ij : i <= j) (j2n : j
 <= 2 * n) (h : xn a1 i ≡ xn a1 j [MOD xn a1 n]) (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 
0 ∧ j = 2)) …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_of_xn_modEq {i j n} (i2n : i ≤ 2 * n) (j2n : j ≤ 2 * n)
    (h : xn a1 i ≡ xn a1 j [MOD xn a1 n])
    (ntriv : a = 2 → n = 1 → (i = 0 → j ≠ 2) ∧ (i = 2 → j ≠ 0)) : i = j :=
  (le_total i j).elim
    (fun ij => eq_of_xn_modEq_le a1 ij j2n h fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij =>
    (eq_of_xn_modEq_le a1 ij i2n h.symm fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm
/-
**Pell.eq_of_xn_modEq'** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_of_xn_modEq' {i j n} (ipos : 0 < i) (hin : i <= n) (j4n : j <= 4 * n) (
h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) : j = i ∨ j + i = 4 * n
参数：ipos : 0 < i；hin : i <= n；j4n : j <= 4 * n；h : xn a1 j ≡ xn a1 i [MOD xn a1 n
]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Pell.eq_of_xn_modEq`：eq_of_xn_modEq {i j n} (i2n : i <= 2 * n) (j2n : j 
<= 2 * n) (h : xn a1 i ≡ xn a1 j [MOD xn a1 n]) (ntriv : a = 2 -> n = 1 -> (i = 
0 -> j !=…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Pell.xn_modEq_x4n_sub`：xn_modEq_x4n_sub {n j} (h : j <= 2 * n) : xn a1 (
4 * n - j) ≡ xn a1 j [MOD xn a1 n]
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
theorem eq_of_xn_modEq' {i j n} (ipos : 0 < i) (hin : i ≤ n) (j4n : j ≤ 4 * n)
    (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) : j = i ∨ j + i = 4 * n :=
  have i2n : i ≤ 2 * n := by apply le_trans hin; rw [two_mul]; apply Nat.le_add_left
  (le_or_gt j (2 * n)).imp
    (fun j2n : j ≤ 2 * n =>
      eq_of_xn_modEq a1 j2n i2n h fun _ n1 =>
        ⟨fun _ i2 => by rw [n1, i2] at hin; exact absurd hin (by decide), fun _ i0 =>
          _root_.ne_of_gt ipos i0⟩)
    fun j2n : 2 * n < j =>
    suffices i = 4 * n - j by rw [this, add_tsub_cancel_of_le j4n]
    have j42n : 4 * n - j ≤ 2 * n := by lia
    eq_of_xn_modEq a1 i2n j42n
      (h.symm.trans <| by
        let t := xn_modEq_x4n_sub a1 j42n
        rwa [tsub_tsub_cancel_of_le j4n] at t)
      (by lia)
/-
**Pell.modEq_of_xn_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：modEq_of_xn_modEq {i j n} (ipos : 0 < i) (hin : i <= n) (h : xn a1 j ≡ xn 
a1 i [MOD xn a1 n]) : j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n]
参数：ipos : 0 < i；hin : i <= n；h : xn a1 j ≡ xn a1 i [MOD xn a1 n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pell.xn.congr_simp`：∀ {a a_1 : ℕ} (e_a : a = a_1) (a1 : 1 < a) (n n_1 : 
ℕ), n = n_1 → Pell.xn a1 n = Pell.xn ⋯ n_1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.mul_succ`：∀ (n m : ℕ), n * m.succ = n * m + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Pell.xn_modEq_x4n_add`：xn_modEq_x4n_add (n j) : xn a1 (4 * n + j) ≡ xn a
1 j [MOD xn a1 n]
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nat.ModEq.add_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a + c ≡ b + 
c [MOD n]
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Pell.eq_of_xn_modEq'`：eq_of_xn_modEq' {i j n} (ipos : 0 < i) (hin : i <=
 n) (j4n : j <= 4 * n) (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) : j = i ∨ j + i = 4
 * n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
theorem modEq_of_xn_modEq {i j n} (ipos : 0 < i) (hin : i ≤ n)
    (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) :
    j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n] :=
  let j' := j % (4 * n)
  have n4 : 0 < 4 * n := mul_pos (by decide) (ipos.trans_le hin)
  have jl : j' < 4 * n := Nat.mod_lt _ n4
  have jj : j ≡ j' [MOD 4 * n] := by delta ModEq; rw [Nat.mod_eq_of_lt jl]
  have : ∀ j q, xn a1 (j + 4 * n * q) ≡ xn a1 j [MOD xn a1 n] := by
    intro j q; induction q with
    | zero => simp [ModEq.refl]
    | succ q IH =>
      rw [Nat.mul_succ, ← add_assoc, add_comm]
      exact (xn_modEq_x4n_add _ _ _).trans IH
  Or.imp (fun ji : j' = i => by rwa [← ji])
    (fun ji : j' + i = 4 * n =>
      (jj.add_right _).trans <| by
        rw [ji]
        exact dvd_rfl.modEq_zero_nat)
    (eq_of_xn_modEq' a1 ipos hin jl.le <|
      (h.symm.trans <| by
          rw [← Nat.mod_add_div j (4 * n)]
          exact this j' _).symm)

end

/-
**Pell.xy_modEq_of_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：∀ {a b c : ℕ} (a1 : 1 < a) (b1 : 1 < b),   a ≡ b [MOD c] → ∀ (n : ℕ), Pell
.xn a1 n ≡ Pell.xn b1 n [MOD c] ∧ Pell.yn a1 n ≡ Pell.yn b1 n [MOD c]
参数：a1 : 1 < a；b1 : 1 < b；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xy_modEq_of_modEq {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c]) :
    ∀ n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c]
  | 0 => by simp [Nat.ModEq.refl]
  | 1 => by simpa [Nat.ModEq.refl]
  | n + 2 =>
    ⟨(xy_modEq_of_modEq a1 b1 h n).left.add_right_cancel <| by
        rw [xn_succ_succ a1, xn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modEq_of_modEq _ _ h (n + 1)).left,
      (xy_modEq_of_modEq a1 b1 h n).right.add_right_cancel <| by
        rw [yn_succ_succ a1, yn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modEq_of_modEq _ _ h (n + 1)).right⟩
/-
**Pell.matiyasevic** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：matiyasevic {a k x y} : (exists a1 : 1 < a, xn a1 k = x ∧ yn a1 k = y) ↔ 1
 < a ∧ k <= y ∧ (x = 1 ∧ y = 0 ∨ exists u v s t b : Nat, x * x - (a * a - 1) * y
 * y = 1 ∧ u * u - (a * a - 1) * v * v = 1 ∧ s * s - (b * b - 1) * t * t = 1 ∧ 1
 < b ∧ b ≡ 1 [MOD 4 * y] ∧ b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧ t
 ≡ k [MOD 4 * y])
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Pell.yn_ge_n`：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), n ≤ Pell.yn a1 n
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Pell.ysq_dvd_yy`：ysq_dvd_yy (n) : yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pell.y_dvd_iff`：y_dvd_iff (m n) : yn a1 m ∣ yn a1 n ↔ m ∣ n
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Pell.yn_modEq_two`：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), Pell.yn a1 n ≡ n [MOD
 2]
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Nat.Coprime.coprime_dvd_right`：∀ {n m k : ℕ}, n ∣ m → k.Coprime m → k.Co
prime n
· 使用定理 `Pell.xy_coprime`：xy_coprime (n) : (xn a1 n).Coprime (yn a1 n)
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Pell.strictMono_y`：strictMono_y : StrictMono (yn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : yn a1 m <= yn a1 n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Pell.strictMono_x`：strictMono_x : StrictMono (xn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : xn a1 m <= xn a1 n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 71 条，此处仅展示前 30 条）
-/
theorem matiyasevic {a k x y} :
    (∃ a1 : 1 < a, xn a1 k = x ∧ yn a1 k = y) ↔
      1 < a ∧ k ≤ y ∧ (x = 1 ∧ y = 0 ∨
        ∃ u v s t b : ℕ,
          x * x - (a * a - 1) * y * y = 1 ∧ u * u - (a * a - 1) * v * v = 1 ∧
          s * s - (b * b - 1) * t * t = 1 ∧ 1 < b ∧ b ≡ 1 [MOD 4 * y] ∧
          b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧ t ≡ k [MOD 4 * y]) :=
  ⟨fun ⟨a1, hx, hy⟩ => by
    rw [← hx, ← hy]
    refine ⟨a1,
        (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0]; exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩)
          fun kpos => ?_⟩
    exact
      let x := xn a1 k
      let y := yn a1 k
      let m := 2 * (k * y)
      let u := xn a1 m
      let v := yn a1 m
      have ky : k ≤ y := yn_ge_n a1 k
      have yv : y * y ∣ v := (ysq_dvd_yy a1 k).trans <| (y_dvd_iff _ _ _).2 <| dvd_mul_left _ _
      have uco : Nat.Coprime u (4 * y) :=
        have : 2 ∣ v :=
          modEq_zero_iff_dvd.1 <| (yn_modEq_two _ _).trans (dvd_mul_right _ _).modEq_zero_nat
        have : Nat.Coprime u 2 := (xy_coprime a1 m).coprime_dvd_right this
        (this.mul_right this).mul_right <|
          (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv)
      let ⟨b, ba, bm1⟩ := chineseRemainder uco a 1
      have m1 : 1 < m :=
        have : 0 < k * y := mul_pos kpos (strictMono_y a1 kpos)
        Nat.mul_le_mul_left 2 this
      have vp : 0 < v := strictMono_y a1 (lt_trans zero_lt_one m1)
      have b1 : 1 < b :=
        have : xn a1 1 < u := strictMono_x a1 m1
        have : a < u := by simpa using this
        lt_of_lt_of_le a1 <| by
          delta ModEq at ba; rw [Nat.mod_eq_of_lt this] at ba; rw [← ba]
          apply Nat.mod_le
      let s := xn b1 k
      let t := yn b1 k
      have sx : s ≡ x [MOD u] := (xy_modEq_of_modEq b1 a1 ba k).left
      have tk : t ≡ k [MOD 4 * y] :=
        have : 4 * y ∣ b - 1 :=
          Int.natCast_dvd_natCast.1 <| by rw [Int.ofNat_sub (le_of_lt b1)]; exact bm1.symm.dvd
        (yn_modEq_a_sub_one _ _).of_dvd this
      ⟨ky,
        Or.inr
          ⟨u, v, s, t, b, pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩,
    fun ⟨a1, ky, o⟩ =>
    ⟨a1,
      match o with
      | Or.inl ⟨x1, y0⟩ => by
        rw [y0] at ky; rw [Nat.eq_zero_of_le_zero ky, x1, y0]; exact ⟨rfl, rfl⟩
      | Or.inr ⟨u, v, s, t, b, xy, uv, st, b1, rem⟩ =>
        match x, y, eq_pell a1 xy, u, v, eq_pell a1 uv, s, t, eq_pell b1 st, rem, ky with
        | _, _, ⟨i, rfl, rfl⟩, _, _, ⟨n, rfl, rfl⟩, _, _, ⟨j, rfl, rfl⟩,
          ⟨(bm1 : b ≡ 1 [MOD 4 * yn a1 i]), (ba : b ≡ a [MOD xn a1 n]), (vp : 0 < yn a1 n),
            (yv : yn a1 i * yn a1 i ∣ yn a1 n), (sx : xn b1 j ≡ xn a1 i [MOD xn a1 n]),
            (tk : yn b1 j ≡ k [MOD 4 * yn a1 i])⟩,
          (ky : k ≤ yn a1 i) =>
          (Nat.eq_zero_or_pos i).elim
            (fun i0 => by
              simp only [i0, yn_zero, nonpos_iff_eq_zero] at ky; rw [i0, ky]; exact ⟨rfl, rfl⟩)
            fun ipos => by
            suffices i = k by rw [this]; exact ⟨rfl, rfl⟩
            clear o rem xy uv st
            have iln : i ≤ n :=
              le_of_not_gt fun hin =>
                not_lt_of_ge (Nat.le_of_dvd vp (dvd_of_mul_left_dvd yv)) (strictMono_y a1 hin)
            have yd : 4 * yn a1 i ∣ 4 * n := by gcongr; exact dvd_of_ysq_dvd a1 yv
            have jk : j ≡ k [MOD 4 * yn a1 i] :=
              have : 4 * yn a1 i ∣ b - 1 :=
                Int.natCast_dvd_natCast.1 <| by rw [Int.ofNat_sub (le_of_lt b1)]; exact bm1.symm.dvd
              ((yn_modEq_a_sub_one b1 _).of_dvd this).symm.trans tk
            have ki : k + i < 4 * yn a1 i :=
              lt_of_le_of_lt (_root_.add_le_add ky (yn_ge_n a1 i)) <| by
                rw [← two_mul]
                exact Nat.mul_lt_mul_of_pos_right (by decide) (strictMono_y a1 ipos)
            have ji : j ≡ i [MOD 4 * n] :=
              have : xn a1 j ≡ xn a1 i [MOD xn a1 n] :=
                (xy_modEq_of_modEq b1 a1 ba j).left.symm.trans sx
              (modEq_of_xn_modEq a1 ipos iln this).resolve_right
                fun ji : j + i ≡ 0 [MOD 4 * n] =>
                not_le_of_gt ki <|
                  Nat.le_of_dvd (lt_of_lt_of_le ipos <| Nat.le_add_left _ _) <|
                    modEq_zero_iff_dvd.1 <| (jk.symm.add_right i).trans <| ji.of_dvd yd
            have : i % (4 * yn a1 i) = k % (4 * yn a1 i) := (ji.of_dvd yd).symm.trans jk
            rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_left _ _) ki),
              Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) ki)] at this⟩⟩
/-
**Pell.eq_pow_of_pell_lem** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_pow_of_pell_lem {a y k : Nat} (hy0 : y != 0) (hk0 : k != 0) (hyk : y ^ 
k < a) : (↑(y ^ k) : Int) < 2 * a * y - y * y - 1
参数：hy0 : y != 0；hk0 : k != 0；hyk : y ^ k < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.le_self_pow`：∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 65 条，此处仅展示前 30 条）
-/
theorem eq_pow_of_pell_lem {a y k : ℕ} (hy0 : y ≠ 0) (hk0 : k ≠ 0) (hyk : y ^ k < a) :
    (↑(y ^ k) : ℤ) < 2 * a * y - y * y - 1 :=
  have hya : y < a := (Nat.le_self_pow hk0 _).trans_lt hyk
  calc
    (↑(y ^ k) : ℤ) < a := Nat.cast_lt.2 hyk
    _ ≤ (a : ℤ) ^ 2 - (a - 1 : ℤ) ^ 2 - 1 := by lia
    _ ≤ (a : ℤ) ^ 2 - (a - y : ℤ) ^ 2 - 1 := by
      have := hya.le
      gcongr <;> norm_cast <;> lia
    _ = 2 * a * y - y * y - 1 := by ring
/-
**Pell.eq_pow_of_pell** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：eq_pow_of_pell {m n k} : n ^ k = m ↔ k = 0 ∧ m = 1 ∨ 0 < k ∧ (n = 0 ∧ m = 
0 ∨ 0 < n ∧ exists (w a t z : Nat) (a1 : 1 < a), xn a1 k ≡ yn a1 k * (a - n) + m
 [MOD t] ∧ 2 * a * n = t + (n * n + 1) ∧ m < t ∧ n <= w ∧ k <= w ∧ a * a - ((w +
 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Pell.strictMono_x`：strictMono_x : StrictMono (xn a1) | _, 0, h => absurd
 h Nat.not_lt_zero _ | m, n + 1, h => by have : xn a1 m <= xn a1 n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Pell.n_lt_xn`：n_lt_xn (n) : n < xn a1 n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Pell.yn_modEq_a_sub_one`：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), Pell.yn a1 n ≡ 
n [MOD a - 1]
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Pell.eq_pow_of_pell_lem`：eq_pow_of_pell_lem {a y k : Nat} (hy0 : y != 0)
 (hk0 : k != 0) (hyk : y ^ k < a) : (↑(y ^ k) : Int) < 2 * a * y - y * y - 1
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Pell.xn_ge_a_pow`：∀ {a : ℕ} (a1 : 1 < a) (n : ℕ), a ^ n ≤ Pell.xn a1 n
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.modEq_of_dvd`：∀ {n a b : ℕ}, ↑n ∣ ↑b - ↑a → a ≡ b [MOD n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
（共 57 条，此处仅展示前 30 条）
-/
theorem eq_pow_of_pell {m n k} :
    n ^ k = m ↔ k = 0 ∧ m = 1 ∨ 0 < k ∧ (n = 0 ∧ m = 0 ∨
      0 < n ∧ ∃ (w a t z : ℕ) (a1 : 1 < a), xn a1 k ≡ yn a1 k * (a - n) + m [MOD t] ∧
      2 * a * n = t + (n * n + 1) ∧ m < t ∧
      n ≤ w ∧ k ≤ w ∧ a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1) := by
  constructor
  · rintro rfl
    refine k.eq_zero_or_pos.imp (fun k0 : k = 0 => k0.symm ▸ ⟨rfl, rfl⟩) fun hk => ⟨hk, ?_⟩
    refine n.eq_zero_or_pos.imp (fun n0 : n = 0 ↦ n0.symm ▸ ⟨rfl, zero_pow hk.ne'⟩)
      fun hn ↦ ⟨hn, ?_⟩
    set w := max n k
    have nw : n ≤ w := le_max_left _ _
    have kw : k ≤ w := le_max_right _ _
    have wpos : 0 < w := hn.trans_le nw
    have w1 : 1 < w + 1 := Nat.succ_lt_succ wpos
    set a := xn w1 w
    have a1 : 1 < a := strictMono_x w1 wpos
    have na : n ≤ a := nw.trans (n_lt_xn w1 w).le
    set x := xn a1 k
    set y := yn a1 k
    obtain ⟨z, ze⟩ : w ∣ yn w1 w :=
      modEq_zero_iff_dvd.1 ((yn_modEq_a_sub_one w1 w).trans dvd_rfl.modEq_zero_nat)
    have nt : (↑(n ^ k) : ℤ) < 2 * a * n - n * n - 1 := by
      refine eq_pow_of_pell_lem hn.ne' hk.ne' ?_
      calc
        n ^ k ≤ n ^ w := Nat.pow_le_pow_right hn kw
        _ < (w + 1) ^ w := Nat.pow_lt_pow_left (Nat.lt_succ_of_le nw) wpos.ne'
        _ ≤ a := xn_ge_a_pow w1 w
    lift (2 * a * n - n * n - 1 : ℤ) to ℕ using (Nat.cast_nonneg _).trans nt.le with t te
    have tm : x ≡ y * (a - n) + n ^ k [MOD t] := by
      apply modEq_of_dvd
      rw [Int.natCast_add, Int.natCast_mul, Int.ofNat_sub na, te]
      exact x_sub_y_dvd_pow a1 n k
    have ta : 2 * a * n = t + (n * n + 1) := by
      zify
      lia
    have zp : a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1 := ze ▸ pell_eq w1 w
    exact ⟨w, a, t, z, a1, tm, ta, Nat.cast_lt.1 nt, nw, kw, zp⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hk0, ⟨rfl, rfl⟩ | ⟨hn0, w, a, t, z, a1, tm, ta, mt, nw, kw, zp⟩⟩)
    · exact _root_.pow_zero n
    · exact zero_pow hk0.ne'
    have hw0 : 0 < w := hn0.trans_le nw
    have hw1 : 1 < w + 1 := Nat.succ_lt_succ hw0
    rcases eq_pell hw1 zp with ⟨j, rfl, yj⟩
    have hj0 : 0 < j := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      exact lt_irrefl 1 a1
    have wj : w ≤ j :=
      Nat.le_of_dvd hj0
        (modEq_zero_iff_dvd.1 <|
          (yn_modEq_a_sub_one hw1 j).symm.trans <| modEq_zero_iff_dvd.2 ⟨z, yj.symm⟩)
    have hnka : n ^ k < xn hw1 j := calc
      n ^ k ≤ n ^ j := Nat.pow_le_pow_right hn0 (le_trans kw wj)
      _ < (w + 1) ^ j := Nat.pow_lt_pow_left (Nat.lt_succ_of_le nw) hj0.ne'
      _ ≤ xn hw1 j := xn_ge_a_pow hw1 j
    have nt : (↑(n ^ k) : ℤ) < 2 * xn hw1 j * n - n * n - 1 :=
      eq_pow_of_pell_lem hn0.ne' hk0.ne' hnka
    have na : n ≤ xn hw1 j := (Nat.le_self_pow hk0.ne' _).trans hnka.le
    have te : (t : ℤ) = 2 * xn hw1 j * n - n * n - 1 := by
      rw [sub_sub, eq_sub_iff_add_eq]
      exact mod_cast ta.symm
    have : xn a1 k ≡ yn a1 k * (xn hw1 j - n) + n ^ k [MOD t] := by
      apply modEq_of_dvd
      rw [te, Nat.cast_add, Nat.cast_mul, Int.ofNat_sub na]
      exact x_sub_y_dvd_pow a1 n k
    have : n ^ k % t = m % t := (this.symm.trans tm).add_left_cancel' _
    rw [← te] at nt
    rwa [Nat.mod_eq_of_lt (Nat.cast_lt.1 nt), Nat.mod_eq_of_lt mt] at this

end Pell

