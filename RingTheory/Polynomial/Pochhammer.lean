/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Algebra

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`ascPochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial and about
`descPochhammer R n : R[X] := X * (X - 1) * ... * (X - n + 1)`
which is also known as the falling factorial. Versions of this definition
that are focused on `Nat` can be found in `Data.Nat.Factorial` as `Nat.ascFactorial` and
`Nat.descFactorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ` or `ℤ`,
we define the polynomial with coefficients in any `[Semiring S]` or `[Ring R]`.
In an integral domain `S`, we show that `ascPochhammer S n` is zero iff
`n` is a sufficiently large non-positive integer.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/

@[expose] public section


universe u v

open Polynomial

section Semiring

variable (S : Type u) [Semiring S]

/-- `ascPochhammer S n` is the polynomial `X * (X + 1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
/-
**ascPochhammer** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(S : Type u) → [inst : Semiring S] → ℕ → Polynomial S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ascPochhammer S n` is the polynomial `X * (X + 1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def ascPochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (ascPochhammer n).comp (X + 1)

@[simp]
/-
**ascPochhammer_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_zero : ascPochhammer S 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascPochhammer_zero : ascPochhammer S 0 = 1 :=
  rfl

@[simp]
/-
**ascPochhammer_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_one : ascPochhammer S 1 = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ascPochhammer_one : ascPochhammer S 1 = X := by simp [ascPochhammer]
/-
**ascPochhammer_succ_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_succ_left (n : Nat) : ascPochhammer S (n + 1) = X * (ascPoch
hammer S n).comp (X + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer.eq_2`：∀ (S : Type u) [inst : Semiring S] (n : ℕ),   ascPoc
hhammer S n.succ = Polynomial.X * (ascPochhammer S n).comp (Polynomial.X + 1)
-/
theorem ascPochhammer_succ_left (n : ℕ) :
    ascPochhammer S (n + 1) = X * (ascPochhammer S n).comp (X + 1) := by
  rw [ascPochhammer]
/-
**monic_ascPochhammer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monic_ascPochhammer (n : Nat) [Nontrivial S] [NoZeroDivisors S] : Monic as
cPochhammer S n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.leadingCoeff_X_add_C`：leadingCoeff_X_add_C [Semiring S] (r : 
S) : (X + C r).leadingCoeff = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_comp`：leadingCoeff_comp (hq : natDegree q != 0) 
: leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.natDegree_X_add_C`：natDegree_X_add_C (x : R) : (X + C x).natD
egree = 1
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem monic_ascPochhammer (n : ℕ) [Nontrivial S] [NoZeroDivisors S] :
    Monic <| ascPochhammer S n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [ascPochhammer_succ_left, Monic.def, leadingCoeff_mul,
      leadingCoeff_comp (ne_zero_of_eq_one <| natDegree_X_add_C 1 : natDegree (X + 1) ≠ 0), hn,
      monic_X, one_mul, one_mul, this, one_pow]

section

variable {S} {T : Type v} [Semiring T]

@[simp]
/-
**ascPochhammer_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_map (f : S ->+* T) (n : Nat) : (ascPochhammer S n).map f = a
scPochhammer T n
参数：f : S ->+* T；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
-/
theorem ascPochhammer_map (f : S →+* T) (n : ℕ) :
    (ascPochhammer S n).map f = ascPochhammer T n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, ascPochhammer_succ_left, map_comp]
/-
**ascPochhammer_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascPochhammer_eval₂ (f : S →+* T) (n : ℕ) (t : T) :
    (ascPochhammer T n).eval t = (ascPochhammer S n).eval₂ f t := by
  rw [← ascPochhammer_map f]
  exact eval_map f t
/-
**ascPochhammer_eval_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_comp {R : Type*} [CommSemiring R] (n : Nat) (p : R[X]) 
[Algebra R S] (x : S) : ((ascPochhammer S n).comp (p.map (algebraMap R S))).eval
 x = (ascPochhammer S n).eval (p.eval₂ (algebraMap R S) x)
参数：n : Nat；p : R[X]；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_eval₂`：ascPochhammer_eval₂ (f : S ->+* T) (n : Nat) (t : T
) : (ascPochhammer T n).eval t = (ascPochhammer S n).eval₂ f t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_comp'`：eval₂_comp' : eval₂ (algebraMap R S) x (p.comp q
) = eval₂ (algebraMap R S) (eval₂ (algebraMap R S) x q) p
· 使用定理 `ascPochhammer_map`：ascPochhammer_map (f : S ->+* T) (n : Nat) : (ascPoch
hammer S n).map f = ascPochhammer T n
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
-/
theorem ascPochhammer_eval_comp {R : Type*} [CommSemiring R] (n : ℕ) (p : R[X]) [Algebra R S]
    (x : S) : ((ascPochhammer S n).comp (p.map (algebraMap R S))).eval x =
    (ascPochhammer S n).eval (p.eval₂ (algebraMap R S) x) := by
  rw [ascPochhammer_eval₂ (algebraMap R S), ← eval₂_comp', ← ascPochhammer_map (algebraMap R S),
    ← map_comp, eval_map]

end

@[simp, norm_cast]
/-
**ascPochhammer_eval_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_cast (n k : Nat) : (((ascPochhammer Nat n).eval k : Nat
) : S) = ((ascPochhammer S n).eval k : S)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ascPochhammer_map`：ascPochhammer_map (f : S ->+* T) (n : Nat) : (ascPoch
hammer S n).map f = ascPochhammer T n
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Polynomial.eval₂_at_natCast`：eval₂_at_natCast {S : Type*} [Semiring S] (
f : R ->+* S) (n : Nat) : p.eval₂ f n = f (p.eval n)
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
-/
theorem ascPochhammer_eval_cast (n k : ℕ) :
    (((ascPochhammer ℕ n).eval k : ℕ) : S) = ((ascPochhammer S n).eval k : S) := by
  rw [← ascPochhammer_map (algebraMap ℕ S), eval_map, ← eq_natCast (algebraMap ℕ S),
      eval₂_at_natCast, Nat.cast_id]
/-
**ascPochhammer_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_zero {n : Nat} : (ascPochhammer S n).eval 0 = if n = 0 
then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem ascPochhammer_eval_zero {n : ℕ} : (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, ascPochhammer_succ_left]
/-
**ascPochhammer_zero_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_zero_eval_zero : (ascPochhammer S 0).eval 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ascPochhammer_zero_eval_zero : (ascPochhammer S 0).eval 0 = 1 := by simp

@[simp]
/-
**ascPochhammer_ne_zero_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_ne_zero_eval_zero {n : Nat} (h : n != 0) : (ascPochhammer S 
n).eval 0 = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_eval_zero`：ascPochhammer_eval_zero {n : Nat} : (ascPochham
mer S n).eval 0 = if n = 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ascPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (ascPochhammer S n).eval 0 = 0 := by
  simp [ascPochhammer_eval_zero, h]
/-
**ascPochhammer_succ_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_succ_right (n : Nat) : ascPochhammer S (n + 1) = ascPochhamm
er S n * (X + (n : S[X]))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ascPochhammer_one`：ascPochhammer_one : ascPochhammer S 1 = X
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.natCast_comp`：natCast_comp {n : Nat} : (n : R[X]).comp p = n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `ascPochhammer_map`：ascPochhammer_map (f : S ->+* T) (n : Nat) : (ascPoch
hammer S n).map f = ascPochhammer T n
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_natCast`：∀ {R : Type u} {S : Type v} [inst : Semiring R] 
[inst_1 : Semiring S] (f : R →+* S) (n : ℕ), Polynomial.map f ↑n = ↑n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem ascPochhammer_succ_right (n : ℕ) :
    ascPochhammer S (n + 1) = ascPochhammer S n * (X + (n : S[X])) := by
  suffices h : ascPochhammer ℕ (n + 1) = ascPochhammer ℕ n * (X + (n : ℕ[X])) by
    apply_fun Polynomial.map (algebraMap ℕ S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_natCast] using h
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs =>
      rw [ascPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← ascPochhammer_succ_left, add_comp,
          X_comp, natCast_comp, add_assoc, add_comm (1 : ℕ[X]), ← Nat.cast_succ]
/-
**ascPochhammer_succ_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_succ_eval {S : Type*} [Semiring S] (n : Nat) (k : S) : (ascP
ochhammer S (n + 1)).eval k = (ascPochhammer S n).eval k * (k + n)
参数：n : Nat；k : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.eval_C_mul`：eval_C_mul : (C a * p).eval x = a * p.eval x
-/
theorem ascPochhammer_succ_eval {S : Type*} [Semiring S] (n : ℕ) (k : S) :
    (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eval k * (k + n) := by
  rw [ascPochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, ← C_eq_natCast,
    eval_C_mul, Nat.cast_comm, ← mul_add]
/-
**ascPochhammer_succ_comp_X_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_succ_comp_X_add_one (n : Nat) : (ascPochhammer S (n + 1)).co
mp (X + 1) = ascPochhammer S (n + 1) + (n + 1) • (ascPochhammer S n).comp (X + 1
)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.natCast_comp`：natCast_comp {n : Nat} : (n : R[X]).comp p = n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
（共 46 条，此处仅展示前 30 条）
-/
theorem ascPochhammer_succ_comp_X_add_one (n : ℕ) :
    (ascPochhammer S (n + 1)).comp (X + 1) =
      ascPochhammer S (n + 1) + (n + 1) • (ascPochhammer S n).comp (X + 1) := by
  suffices (ascPochhammer ℕ (n + 1)).comp (X + 1) =
      ascPochhammer ℕ (n + 1) + (n + 1) * (ascPochhammer ℕ n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul, ascPochhammer_succ_right ℕ n, mul_comp, mul_comm, add_comp, X_comp, natCast_comp,
    add_comm, ← add_assoc]
  ring
/-
**ascPochhammer_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_mul (n m : Nat) : ascPochhammer S n * (ascPochhammer S m).co
mp (X + (n : S[X])) = ascPochhammer S (n + m)
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `Polynomial.mul_X_add_natCast_comp`：mul_X_add_natCast_comp {n : Nat} : (p
 * (X + (n : R[X]))).comp q = p.comp q * (q + n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
theorem ascPochhammer_mul (n m : ℕ) :
    ascPochhammer S n * (ascPochhammer S m).comp (X + (n : S[X])) = ascPochhammer S (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_right, Polynomial.mul_X_add_natCast_comp, ← mul_assoc, ih,
      ← add_assoc, ascPochhammer_succ_right, Nat.cast_add, add_assoc]
/-
**ascPochhammer_nat_eq_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (n k : ℕ), Polynomial.eval n (ascPochhammer ℕ k) = n.ascFactorial k
参数：n k : ℕ；ascPochhammer ℕ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascPochhammer_nat_eq_ascFactorial (n : ℕ) :
    ∀ k, (ascPochhammer ℕ k).eval n = n.ascFactorial k
  | 0 => by rw [ascPochhammer_zero, eval_one, Nat.ascFactorial_zero]
  | t + 1 => by
    rw [ascPochhammer_succ_right, eval_mul, ascPochhammer_nat_eq_ascFactorial n t, eval_add, eval_X,
      eval_natCast, Nat.cast_id, Nat.ascFactorial_succ, mul_comm]
/-
**ascPochhammer_nat_eq_natCast_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_nat_eq_natCast_ascFactorial (S : Type*) [Semiring S] (n k : 
Nat) : (ascPochhammer S k).eval (n : S) = n.ascFactorial k
参数：S : Type*；n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_nat_eq_ascFactorial`：∀ (n k : ℕ), Polynomial.eval n (ascPo
chhammer ℕ k) = n.ascFactorial k
-/
theorem ascPochhammer_nat_eq_natCast_ascFactorial (S : Type*) [Semiring S] (n k : ℕ) :
    (ascPochhammer S k).eval (n : S) = n.ascFactorial k := by
  norm_cast
  rw [ascPochhammer_nat_eq_ascFactorial]
/-
**ascPochhammer_nat_eq_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_nat_eq_descFactorial (a b : Nat) : (ascPochhammer Nat b).eva
l a = (a + b - 1).descFactorial b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_nat_eq_ascFactorial`：∀ (n k : ℕ), Polynomial.eval n (ascPo
chhammer ℕ k) = n.ascFactorial k
· 使用定理 `Nat.add_descFactorial_eq_ascFactorial'`：∀ (n k : ℕ), (n + k - 1).descFac
torial k = n.ascFactorial k
-/
theorem ascPochhammer_nat_eq_descFactorial (a b : ℕ) :
    (ascPochhammer ℕ b).eval a = (a + b - 1).descFactorial b := by
  rw [ascPochhammer_nat_eq_ascFactorial, Nat.add_descFactorial_eq_ascFactorial']
/-
**ascPochhammer_nat_eq_natCast_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_nat_eq_natCast_descFactorial (S : Type*) [Semiring S] (a b :
 Nat) : (ascPochhammer S b).eval (a : S) = (a + b - 1).descFactorial b
参数：S : Type*；a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_nat_eq_descFactorial`：ascPochhammer_nat_eq_descFactorial (
a b : Nat) : (ascPochhammer Nat b).eval a = (a + b - 1).descFactorial b
-/
theorem ascPochhammer_nat_eq_natCast_descFactorial (S : Type*) [Semiring S] (a b : ℕ) :
    (ascPochhammer S b).eval (a : S) = (a + b - 1).descFactorial b := by
  norm_cast
  rw [ascPochhammer_nat_eq_descFactorial]

@[simp]
/-
**ascPochhammer_natDegree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_natDegree (n : Nat) [NoZeroDivisors S] [Nontrivial S] : (asc
Pochhammer S n).natDegree = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_X_add_C`：natDegree_X_add_C (x : R) : (X + C x).natD
egree = 1
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ne_zero_of_natDegree_gt`：ne_zero_of_natDegree_gt {n : Nat} (h
 : n < natDegree p) : p != 0
· 使用定理 `Nat.add_one_pos`：∀ (n : ℕ), 0 < n + 1
· 使用定理 `Nat.zero_lt_one`：0 < 1
-/
theorem ascPochhammer_natDegree (n : ℕ) [NoZeroDivisors S] [Nontrivial S] :
    (ascPochhammer S n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [ascPochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.add_one_pos _

end Semiring

section StrictOrderedSemiring

variable {S : Type*} [Semiring S] [PartialOrder S] [IsStrictOrderedRing S]

/-
**ascPochhammer_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_pos (n : Nat) (s : S) (h : 0 < s) : 0 < (ascPochhammer S n).
eval s
参数：n : Nat；s : S；h : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `Polynomial.eval_natCast_mul`：eval_natCast_mul {n : Nat} : ((n : R[X]) * 
p).eval x = n * p.eval x
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
theorem ascPochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (ascPochhammer S n).eval s := by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, eval_one]
    exact zero_lt_one
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_add, eval_add, ← Nat.cast_comm, eval_natCast_mul, eval_mul_X,
      Nat.cast_comm, ← mul_add]
    exact mul_pos ih (lt_of_lt_of_le h (le_add_of_nonneg_right (Nat.cast_nonneg n)))

end StrictOrderedSemiring

section Factorial

open Nat

variable (S : Type*) [Semiring S] (r n : ℕ)

@[simp]
/-
**ascPochhammer_eval_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_one (S : Type*) [Semiring S] (n : Nat) : (ascPochhammer
 S n).eval (1 : S) = (n ! : S)
参数：S : Type*；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ascPochhammer_nat_eq_ascFactorial`：∀ (n k : ℕ), Polynomial.eval n (ascPo
chhammer ℕ k) = n.ascFactorial k
· 使用定理 `Nat.one_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial
-/
theorem ascPochhammer_eval_one (S : Type*) [Semiring S] (n : ℕ) :
    (ascPochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]
/-
**factorial_mul_ascPochhammer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：factorial_mul_ascPochhammer (S : Type*) [Semiring S] (r n : Nat) : (r ! : 
S) * (ascPochhammer S n).eval (r + 1 : S) = (r + n)!
参数：S : Type*；r n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ascPochhammer_nat_eq_ascFactorial`：∀ (n k : ℕ), Polynomial.eval n (ascPo
chhammer ℕ k) = n.ascFactorial k
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial
-/
theorem factorial_mul_ascPochhammer (S : Type*) [Semiring S] (r n : ℕ) :
    (r ! : S) * (ascPochhammer S n).eval (r + 1 : S) = (r + n)! := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]
/-
**ascPochhammer_nat_eval_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (r n : ℕ), n * Polynomial.eval (n + 1) (ascPochhammer ℕ r) = (n + r) * P
olynomial.eval n (ascPochhammer ℕ r)
参数：r n : ℕ；n + 1；ascPochhammer ℕ r；n + r；ascPochhammer ℕ r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_eval_zero`：ascPochhammer_eval_zero {n : Nat} : (ascPochham
mer S n).eval 0 = if n = 0 then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ascPochhammer_nat_eq_ascFactorial`：∀ (n k : ℕ), Polynomial.eval n (ascPo
chhammer ℕ k) = n.ascFactorial k
· 使用定理 `Nat.succ_ascFactorial`：∀ (n k : ℕ), n * n.succ.ascFactorial k = (n + k) 
* n.ascFactorial k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem ascPochhammer_nat_eval_succ (r : ℕ) :
    ∀ n : ℕ, n * (ascPochhammer ℕ r).eval (n + 1) = (n + r) * (ascPochhammer ℕ r).eval n
  | 0 => by
    by_cases h : r = 0
    · simp only [h, zero_mul, zero_add]
    · simp only [ascPochhammer_eval_zero, zero_mul, if_neg h, mul_zero]
  | k + 1 => by simp only [ascPochhammer_nat_eq_ascFactorial, Nat.succ_ascFactorial, add_right_comm]
/-
**ascPochhammer_eval_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_succ (r n : Nat) : (n : S) * (ascPochhammer S r).eval (
n + 1 : S) = (n + r) * (ascPochhammer S r).eval (n : S)
参数：r n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ascPochhammer_nat_eval_succ`：∀ (r n : ℕ), n * Polynomial.eval (n + 1) (a
scPochhammer ℕ r) = (n + r) * Polynomial.eval n (ascPochhammer ℕ r)
-/
theorem ascPochhammer_eval_succ (r n : ℕ) :
    (n : S) * (ascPochhammer S r).eval (n + 1 : S) =
    (n + r) * (ascPochhammer S r).eval (n : S) :=
  mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)

namespace Nat
variable (a b : ℕ)

/-
**Nat.cast_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_ascFactorial : a.ascFactorial b = (ascPochhammer S b).eval (a : S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ascPochhammer_nat_eq_ascFactorial`：∀ (n k : ℕ), Polynomial.eval n (ascPo
chhammer ℕ k) = n.ascFactorial k
· 使用定理 `ascPochhammer_eval_cast`：ascPochhammer_eval_cast (n k : Nat) : (((ascPoc
hhammer Nat n).eval k : Nat) : S) = ((ascPochhammer S n).eval k : S)
-/
theorem cast_ascFactorial : a.ascFactorial b = (ascPochhammer S b).eval (a : S) := by
  rw [← ascPochhammer_nat_eq_ascFactorial, ascPochhammer_eval_cast]
/-
**Nat.cast_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_descFactorial : a.descFactorial b = (ascPochhammer S b).eval (a - (b 
- 1) : S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ascPochhammer_eval_cast`：ascPochhammer_eval_cast (n k : Nat) : (((ascPoc
hhammer Nat n).eval k : Nat) : S) = ((ascPochhammer S n).eval k : S)
· 使用定理 `ascPochhammer_nat_eq_descFactorial`：ascPochhammer_nat_eq_descFactorial (
a b : Nat) : (ascPochhammer Nat b).eval a = (a + b - 1).descFactorial b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Nat.descFactorial_of_lt`：∀ {n k : ℕ}, n < k → n.descFactorial k = 0
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem cast_descFactorial :
    a.descFactorial b = (ascPochhammer S b).eval (a - (b - 1) : S) := by
  rw [← ascPochhammer_eval_cast, ascPochhammer_nat_eq_descFactorial]
  induction b with
  | zero => simp
  | succ b =>
    simp_rw [add_succ, Nat.add_one_sub_one]
    obtain h | h := le_total a b
    · rw [descFactorial_of_lt (lt_succ_of_le h), descFactorial_of_lt (lt_succ_of_le _)]
      rw [tsub_eq_zero_iff_le.mpr h, zero_add]
    · rw [tsub_add_cancel_of_le h]
/-
**Nat.cast_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_factorial : (a ! : S) = (ascPochhammer S a).eval 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.one_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial
· 使用定理 `Nat.cast_ascFactorial`：cast_ascFactorial : a.ascFactorial b = (ascPochha
mmer S b).eval (a : S)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem cast_factorial : (a ! : S) = (ascPochhammer S a).eval 1 := by
  rw [← one_ascFactorial, cast_ascFactorial, cast_one]

end Nat

end Factorial

section Ring

variable (R : Type u) [Ring R]

/-- `descPochhammer R n` is the polynomial `X * (X - 1) * ... * (X - n + 1)`,
with coefficients in the ring `R`.
-/
/-
**descPochhammer** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(R : Type u) → [inst : Ring R] → ℕ → Polynomial R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`descPochhammer R n` is the polynomial `X * (X - 1) * ... * (X - n + 1)`,
with coefficients in the ring `R`.
-/
noncomputable def descPochhammer : ℕ → R[X]
  | 0 => 1
  | n + 1 => X * (descPochhammer n).comp (X - 1)

@[simp]
/-
**descPochhammer_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_zero : descPochhammer R 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descPochhammer_zero : descPochhammer R 0 = 1 :=
  rfl

@[simp]
/-
**descPochhammer_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_one : descPochhammer R 1 = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem descPochhammer_one : descPochhammer R 1 = X := by simp [descPochhammer]
/-
**descPochhammer_succ_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_succ_left (n : Nat) : descPochhammer R (n + 1) = X * (descP
ochhammer R n).comp (X - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer.eq_2`：∀ (R : Type u) [inst : Ring R] (n : ℕ),   descPochh
ammer R n.succ = Polynomial.X * (descPochhammer R n).comp (Polynomial.X - 1)
-/
theorem descPochhammer_succ_left (n : ℕ) :
    descPochhammer R (n + 1) = X * (descPochhammer R n).comp (X - 1) := by
  rw [descPochhammer]
/-
**monic_descPochhammer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monic_descPochhammer (n : Nat) [Nontrivial R] [NoZeroDivisors R] : Monic d
escPochhammer R n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_succ_left`：descPochhammer_succ_left (n : Nat) : descPochh
ammer R (n + 1) = X * (descPochhammer R n).comp (X - 1)
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_comp`：leadingCoeff_comp (hq : natDegree q != 0) 
: leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem monic_descPochhammer (n : ℕ) [Nontrivial R] [NoZeroDivisors R] :
    Monic <| descPochhammer R n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have h : leadingCoeff (X - 1 : R[X]) = 1 := leadingCoeff_X_sub_C 1
    have : natDegree (X - (1 : R[X])) ≠ 0 := ne_zero_of_eq_one <| natDegree_X_sub_C (1 : R)
    rw [descPochhammer_succ_left, Monic.def, leadingCoeff_mul, leadingCoeff_comp this, hn, monic_X,
        one_mul, one_mul, h, one_pow]

section

variable {R} {T : Type v} [Ring T]

@[simp]
/-
**descPochhammer_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_map (f : R ->+* T) (n : Nat) : (descPochhammer R n).map f =
 descPochhammer T n
参数：f : R ->+* T；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `descPochhammer_succ_left`：descPochhammer_succ_left (n : Nat) : descPochh
ammer R (n + 1) = X * (descPochhammer R n).comp (X - 1)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
-/
theorem descPochhammer_map (f : R →+* T) (n : ℕ) :
    (descPochhammer R n).map f = descPochhammer T n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, descPochhammer_succ_left, map_comp]
end

@[simp, norm_cast]
/-
**descPochhammer_eval_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_eval_cast (n : Nat) (k : Int) : (((descPochhammer Int n).ev
al k : Int) : R) = ((descPochhammer R n).eval k : R)
参数：n : Nat；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `descPochhammer_map`：descPochhammer_map (f : R ->+* T) (n : Nat) : (descP
ochhammer R n).map f = descPochhammer T n
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_at_intCast`：eval₂_at_intCast {S : Type*} [Ring S] (f : 
R ->+* S) (n : Int) : p.eval₂ f n = f (p.eval n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem descPochhammer_eval_cast (n : ℕ) (k : ℤ) :
    (((descPochhammer ℤ n).eval k : ℤ) : R) = ((descPochhammer R n).eval k : R) := by
  rw [← descPochhammer_map (algebraMap ℤ R), eval_map, ← eq_intCast (algebraMap ℤ R)]
  simp only [algebraMap_int_eq, eq_intCast, eval₂_at_intCast, Int.cast_id]
/-
**descPochhammer_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_eval_zero {n : Nat} : (descPochhammer R n).eval 0 = if n = 
0 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `descPochhammer_succ_left`：descPochhammer_succ_left (n : Nat) : descPochh
ammer R (n + 1) = X * (descPochhammer R n).comp (X - 1)
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem descPochhammer_eval_zero {n : ℕ} :
    (descPochhammer R n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, descPochhammer_succ_left]
/-
**descPochhammer_zero_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_zero_eval_zero : (descPochhammer R 0).eval 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem descPochhammer_zero_eval_zero : (descPochhammer R 0).eval 0 = 1 := by simp

@[simp]
/-
**descPochhammer_ne_zero_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_ne_zero_eval_zero {n : Nat} (h : n != 0) : (descPochhammer 
R n).eval 0 = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_eval_zero`：descPochhammer_eval_zero {n : Nat} : (descPoch
hammer R n).eval 0 = if n = 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem descPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (descPochhammer R n).eval 0 = 0 := by
  simp [descPochhammer_eval_zero, h]
/-
**descPochhammer_succ_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_succ_right (n : Nat) : descPochhammer R (n + 1) = descPochh
ammer R n * (X - (n : R[X]))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `descPochhammer_succ_left`：descPochhammer_succ_left (n : Nat) : descPochh
ammer R (n + 1) = X * (descPochhammer R n).comp (X - 1)
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.natCast_comp`：natCast_comp {n : Nat} : (n : R[X]).comp p = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_add_eq_sub_sub_swap`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (
a b c : α), a - (b + c) = a - c - b
· 使用定理 `descPochhammer_map`：descPochhammer_map (f : R ->+* T) (n : Nat) : (descP
ochhammer R n).map f = descPochhammer T n
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_natCast`：∀ {R : Type u} {S : Type v} [inst : Semiring R] 
[inst_1 : Semiring S] (f : R →+* S) (n : ℕ), Polynomial.map f ↑n = ↑n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem descPochhammer_succ_right (n : ℕ) :
    descPochhammer R (n + 1) = descPochhammer R n * (X - (n : R[X])) := by
  suffices h : descPochhammer ℤ (n + 1) = descPochhammer ℤ n * (X - (n : ℤ[X])) by
    apply_fun Polynomial.map (algebraMap ℤ R) at h
    simpa [descPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_intCast] using h
  induction n with
  | zero => simp [descPochhammer]
  | succ n ih =>
    conv_lhs =>
      rw [descPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← descPochhammer_succ_left, sub_comp,
          X_comp, natCast_comp]
    rw [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub_swap]

@[simp]
/-
**descPochhammer_natDegree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_natDegree (n : Nat) [NoZeroDivisors R] [Nontrivial R] : (de
scPochhammer R n).natDegree = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ne_zero_of_natDegree_gt`：ne_zero_of_natDegree_gt {n : Nat} (h
 : n < natDegree p) : p != 0
· 使用定理 `Nat.add_one_pos`：∀ (n : ℕ), 0 < n + 1
· 使用定理 `Nat.zero_lt_one`：0 < 1
-/
theorem descPochhammer_natDegree (n : ℕ) [NoZeroDivisors R] [Nontrivial R] :
    (descPochhammer R n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X - (n : R[X])) = 1 := natDegree_X_sub_C (n : R)
    rw [descPochhammer_succ_right,
        natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one), hn, this]
    cases n
    · simp
    · refine ne_zero_of_natDegree_gt <| hn.symm ▸ Nat.add_one_pos _
/-
**descPochhammer_succ_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_succ_eval {S : Type*} [Ring S] (n : Nat) (k : S) : (descPoc
hhammer S (n + 1)).eval k = (descPochhammer S n).eval k * (k - n)
参数：n : Nat；k : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.eval_C_mul`：eval_C_mul : (C a * p).eval x = a * p.eval x
-/
theorem descPochhammer_succ_eval {S : Type*} [Ring S] (n : ℕ) (k : S) :
    (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eval k * (k - n) := by
  rw [descPochhammer_succ_right, mul_sub, eval_sub, eval_mul_X, ← Nat.cast_comm, ← C_eq_natCast,
    eval_C_mul, Nat.cast_comm, ← mul_sub]
/-
**descPochhammer_succ_comp_X_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_succ_comp_X_sub_one (n : Nat) : (descPochhammer R (n + 1)).
comp (X - 1) = descPochhammer R (n + 1) - (n + (1 : R[X])) • (descPochhammer R n
).comp (X - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_succ_left`：descPochhammer_succ_left (n : Nat) : descPochh
ammer R (n + 1) = X * (descPochhammer R n).comp (X - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.natCast_comp`：natCast_comp {n : Nat} : (n : R[X]).comp p = n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 51 条，此处仅展示前 30 条）
-/
theorem descPochhammer_succ_comp_X_sub_one (n : ℕ) :
    (descPochhammer R (n + 1)).comp (X - 1) =
      descPochhammer R (n + 1) - (n + (1 : R[X])) • (descPochhammer R n).comp (X - 1) := by
  suffices (descPochhammer ℤ (n + 1)).comp (X - 1) =
      descPochhammer ℤ (n + 1) - (n + 1) * (descPochhammer ℤ n).comp (X - 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Int.castRingHom R)) this
  nth_rw 2 [descPochhammer_succ_left]
  rw [← sub_mul, descPochhammer_succ_right ℤ n, mul_comp, mul_comm, sub_comp, X_comp, natCast_comp]
  ring
/-
**descPochhammer_eq_ascPochhammer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_eq_ascPochhammer (n : Nat) : descPochhammer Int n = (ascPoc
hhammer Int n).comp ((X : Int[X]) - n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_zero`：descPochhammer_zero : descPochhammer R 0 = 1
· 使用定理 `ascPochhammer_zero`：ascPochhammer_zero : ascPochhammer S 0 = 1
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.mul_X_comp`：mul_X_comp : (p * X).comp r = p.comp r * r
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
-/
theorem descPochhammer_eq_ascPochhammer (n : ℕ) :
    descPochhammer ℤ n = (ascPochhammer ℤ n).comp ((X : ℤ[X]) - n + 1) := by
  induction n with
  | zero => rw [descPochhammer_zero, ascPochhammer_zero, one_comp]
  | succ n ih =>
    rw [Nat.cast_succ, sub_add, add_sub_cancel_right, descPochhammer_succ_right,
      ascPochhammer_succ_left, ih, X_mul, mul_X_comp, comp_assoc, add_comp, X_comp, one_comp]
/-
**descPochhammer_eval_eq_ascPochhammer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_eval_eq_ascPochhammer (r : R) (n : Nat) : (descPochhammer R
 n).eval r = (ascPochhammer R n).eval (r - n + 1)
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_zero`：descPochhammer_zero : descPochhammer R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `ascPochhammer_zero`：ascPochhammer_zero : ascPochhammer S 0 = 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `descPochhammer_succ_eval`：descPochhammer_succ_eval {S : Type*} [Ring S] 
(n : Nat) (k : S) : (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eva
l k * (k - n)
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_eval_comp`：ascPochhammer_eval_comp {R : Type*} [CommSemiri
ng R] (n : Nat) (p : R[X]) [Algebra R S] (x : S) : ((ascPochhammer S n).comp (p.
map (algebraM…
· 使用定理 `Polynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Polynomial.eval₂_one`：eval₂_one : (1 : R[X]).eval₂ f x = 1
-/
theorem descPochhammer_eval_eq_ascPochhammer (r : R) (n : ℕ) :
    (descPochhammer R n).eval r = (ascPochhammer R n).eval (r - n + 1) := by
  induction n with
  | zero => rw [descPochhammer_zero, eval_one, ascPochhammer_zero, eval_one]
  | succ n ih =>
    rw [Nat.cast_succ, sub_add, add_sub_cancel_right, descPochhammer_succ_eval, ih,
      ascPochhammer_succ_left, X_mul, eval_mul_X, show (X + 1 : R[X]) =
      (X + 1 : ℕ[X]).map (algebraMap ℕ R) by simp only [Polynomial.map_add, map_X,
      Polynomial.map_one], ascPochhammer_eval_comp, eval₂_add, eval₂_X, eval₂_one]
/-
**descPochhammer_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_mul (n m : Nat) : descPochhammer R n * (descPochhammer R m)
.comp (X - (n : R[X])) = descPochhammer R (n + m)
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Polynomial.mul_X_sub_intCast_comp`：mul_X_sub_intCast_comp {n : Nat} : (p
 * (X - (n : R[X]))).comp q = p.comp q * (q - n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - (b + c) = a - b - c
-/
theorem descPochhammer_mul (n m : ℕ) :
    descPochhammer R n * (descPochhammer R m).comp (X - (n : R[X])) = descPochhammer R (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_right, Polynomial.mul_X_sub_intCast_comp, ← mul_assoc, ih,
      ← add_assoc, descPochhammer_succ_right, Nat.cast_add, sub_add_eq_sub_sub]
/-
**ascPochhammer_eval_neg_eq_descPochhammer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u) [inst : Ring R] (r : R) (k : ℕ),   Polynomial.eval (-r) (as
cPochhammer R k) = (-1) ^ k * Polynomial.eval r (descPochhammer R k)
参数：R : Type u；r : R；k : ℕ；-r；ascPochhammer R k；-1；descPochhammer R k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascPochhammer_eval_neg_eq_descPochhammer (r : R) : ∀ (k : ℕ),
    (ascPochhammer R k).eval (-r) = (-1) ^ k * (descPochhammer R k).eval r
  | 0 => by
    rw [ascPochhammer_zero, descPochhammer_zero]
    simp only [eval_one, pow_zero, mul_one]
  | (k + 1) => by
    rw [ascPochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, eval_natCast_mul,
      Nat.cast_comm, ← mul_add, ascPochhammer_eval_neg_eq_descPochhammer r k, mul_assoc,
      descPochhammer_succ_right, mul_sub, eval_sub, eval_mul_X, ← Nat.cast_comm, eval_natCast_mul,
      pow_add, pow_one, mul_assoc ((-1) ^ k) (-1), mul_sub, neg_one_mul, neg_mul_eq_mul_neg,
      Nat.cast_comm, sub_eq_add_neg, neg_one_mul, neg_neg, ← mul_add]
/-
**descPochhammer_eval_eq_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_eval_eq_descFactorial (n k : Nat) : (descPochhammer R k).ev
al (n : R) = n.descFactorial k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_zero`：descPochhammer_zero : descPochhammer R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Nat.descFactorial_zero`：descFactorial_zero (n : Nat) : n.descFactorial 0
 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Nat.descFactorial_succ`：descFactorial_succ (n k : Nat) : n.descFactorial
 (k + 1) = (n - k) * n.descFactorial k
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `Polynomial.eval_natCast_mul`：eval_natCast_mul {n : Nat} : ((n : R[X]) * 
p).eval x = n * p.eval x
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.descFactorial_eq_zero_iff_lt`：∀ {n k : ℕ}, n.descFactorial k = 0 ↔ n
 < k
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
-/
theorem descPochhammer_eval_eq_descFactorial (n k : ℕ) :
    (descPochhammer R k).eval (n : R) = n.descFactorial k := by
  induction k with
  | zero => rw [descPochhammer_zero, eval_one, Nat.descFactorial_zero, Nat.cast_one]
  | succ k ih =>
    rw [descPochhammer_succ_right, Nat.descFactorial_succ, mul_sub, eval_sub, eval_mul_X,
      ← Nat.cast_comm k, eval_natCast_mul, ← Nat.cast_comm n, ← sub_mul, ih]
    by_cases! h : n < k
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, mul_zero, mul_zero, Nat.cast_zero]
    · rw [Nat.cast_mul, Nat.cast_sub h]
/-
**descPochhammer_int_eq_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_int_eq_ascFactorial (a b : Nat) : (descPochhammer Int b).ev
al (a + b : Int) = (a + 1).ascFactorial b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `descPochhammer_eval_eq_descFactorial`：descPochhammer_eval_eq_descFactori
al (n k : Nat) : (descPochhammer R k).eval (n : R) = n.descFactorial k
· 使用定理 `Nat.add_descFactorial_eq_ascFactorial`：∀ (n k : ℕ), (n + k).descFactoria
l k = (n + 1).ascFactorial k
-/
theorem descPochhammer_int_eq_ascFactorial (a b : ℕ) :
    (descPochhammer ℤ b).eval (a + b : ℤ) = (a + 1).ascFactorial b := by
  rw [← Nat.cast_add, descPochhammer_eval_eq_descFactorial ℤ (a + b) b,
    Nat.add_descFactorial_eq_ascFactorial]

variable {R}

/-- The Pochhammer polynomial of degree `n` has roots at `0`, `-1`, ..., `-(n - 1)`. -/
/-
**ascPochhammer_eval_neg_coe_nat_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_neg_coe_nat_of_lt {n k : Nat} (h : k < n) : (ascPochham
mer R n).eval (-(k : R)) = 0
参数：h : k < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_succ_eval`：ascPochhammer_succ_eval {S : Type*} [Semiring S
] (n : Nat) (k : S) : (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eva
l k * (k + n)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
The Pochhammer polynomial of degree `n` has roots at `0`, `-1`, ..., `-(n - 1)`.
-/
theorem ascPochhammer_eval_neg_coe_nat_of_lt {n k : ℕ} (h : k < n) :
    (ascPochhammer R n).eval (-(k : R)) = 0 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    rcases lt_trichotomy k n with hkn | rfl | hkn
    · simp [ih hkn]
    · simp
    · lia

/-- Over an integral domain, the Pochhammer polynomial of degree `n` has roots *only* at
`0`, `-1`, ..., `-(n - 1)`. -/
@[simp]
/-
**ascPochhammer_eval_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ascPochhammer_eval_eq_zero_iff [IsDomain R] (n : Nat) (r : R) : (ascPochha
mmer R n).eval r = 0 ↔ exists k < n, k = -r
参数：n : Nat；r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ascPochhammer_succ_eval`：ascPochhammer_succ_eval {S : Type*} [Semiring S
] (n : Nat) (k : S) : (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eva
l k * (k + n)
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_neg_of_add_eq_zero_right`：∀ {α : Type u_1} [inst : SubtractionMonoid 
α] {a b : α}, a + b = 0 → b = -a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_eval_neg_coe_nat_of_lt`：ascPochhammer_eval_neg_coe_nat_of_
lt {n k : Nat} (h : k < n) : (ascPochhammer R n).eval (-(k : R)) = 0

--- 原说明 ---
Over an integral domain, the Pochhammer polynomial of degree `n` has roots *only
* at
`0`, `-1`, ..., `-(n - 1)`.
-/
theorem ascPochhammer_eval_eq_zero_iff [IsDomain R]
    (n : ℕ) (r : R) : (ascPochhammer R n).eval r = 0 ↔ ∃ k < n, k = -r := by
  refine ⟨fun zero' ↦ ?_, fun hrn ↦ ?_⟩
  · induction n with
    | zero => simp only [ascPochhammer_zero, Polynomial.eval_one, one_ne_zero] at zero'
    | succ n ih =>
      rw [ascPochhammer_succ_eval, mul_eq_zero] at zero'
      cases zero' with
      | inl h =>
        obtain ⟨rn, hrn, rrn⟩ := ih h
        exact ⟨rn, by lia, rrn⟩
      | inr h =>
        exact ⟨n, lt_add_one n, eq_neg_of_add_eq_zero_right h⟩
  · obtain ⟨rn, hrn, rnn⟩ := hrn
    convert! ascPochhammer_eval_neg_coe_nat_of_lt hrn
    simp [rnn]

/-- `descPochhammer R n` is `0` for `0, 1, …, n-1`. -/
/-
**descPochhammer_eval_coe_nat_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_eval_coe_nat_of_lt {k n : Nat} (h : k < n) : (descPochhamme
r R n).eval (k : R) = 0
参数：h : k < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_eval_eq_ascPochhammer`：descPochhammer_eval_eq_ascPochhamm
er (r : R) (n : Nat) : (descPochhammer R n).eval r = (ascPochhammer R n).eval (r
 - n + 1)
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `ascPochhammer_eval_neg_coe_nat_of_lt`：ascPochhammer_eval_neg_coe_nat_of_
lt {n k : Nat} (h : k < n) : (ascPochhammer R n).eval (-(k : R)) = 0
· 使用定理 `Nat.sub_lt_of_pos_le`：∀ {a b : ℕ}, 0 < a → a ≤ b → b - a < b
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
`descPochhammer R n` is `0` for `0, 1, …, n-1`.
-/
theorem descPochhammer_eval_coe_nat_of_lt {k n : ℕ} (h : k < n) :
    (descPochhammer R n).eval (k : R) = 0 := by
  rw [descPochhammer_eval_eq_ascPochhammer, sub_add_eq_add_sub,
    ← Nat.cast_add_one, ← neg_sub, ← Nat.cast_sub h]
  exact ascPochhammer_eval_neg_coe_nat_of_lt (Nat.sub_lt_of_pos_le k.succ_pos h)
/-
**descPochhammer_eval_eq_prod_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：descPochhammer_eval_eq_prod_range {R : Type*} [CommRing R] (n : Nat) (r : 
R) : (descPochhammer R n).eval r = ∏ j in Finset.range n, (r - j)
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
-/
lemma descPochhammer_eval_eq_prod_range {R : Type*} [CommRing R] (n : ℕ) (r : R) :
    (descPochhammer R n).eval r = ∏ j ∈ Finset.range n, (r - j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [descPochhammer_succ_right, ih, ← Finset.prod_range_succ]

end Ring

section StrictOrderedRing

variable {S : Type*} [Ring S] [PartialOrder S] [IsStrictOrderedRing S]

/-- `descPochhammer S n` is positive on `(n-1, ∞)`. -/
/-
**descPochhammer_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_pos {n : Nat} {s : S} (h : n - 1 < s) : 0 < (descPochhammer
 S n).eval s
参数：h : n - 1 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_eval_eq_ascPochhammer`：descPochhammer_eval_eq_ascPochhamm
er (r : R) (n : Nat) : (descPochhammer R n).eval r = (ascPochhammer R n).eval (r
 - n + 1)
· 使用定理 `ascPochhammer_pos`：ascPochhammer_pos (n : Nat) (s : S) (h : 0 < s) : 0 <
 (ascPochhammer S n).eval s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
`descPochhammer S n` is positive on `(n-1, ∞)`.
-/
theorem descPochhammer_pos {n : ℕ} {s : S} (h : n - 1 < s) :
    0 < (descPochhammer S n).eval s := by
  rw [← sub_pos, ← sub_add] at h
  rw [descPochhammer_eval_eq_ascPochhammer]
  exact ascPochhammer_pos n (s - n + 1) h

/-- `descPochhammer S n` is nonnegative on `[n-1, ∞)`. -/
/-
**descPochhammer_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：descPochhammer_nonneg {n : Nat} {s : S} (h : n - 1 <= s) : 0 <= (descPochh
ammer S n).eval s
参数：h : n - 1 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `descPochhammer_eval_eq_ascPochhammer`：descPochhammer_eval_eq_ascPochhamm
er (r : R) (n : Nat) : (descPochhammer R n).eval r = (ascPochhammer R n).eval (r
 - n + 1)
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `ascPochhammer_eval_zero`：ascPochhammer_eval_zero {n : Nat} : (ascPochham
mer S n).eval 0 = if n = 0 then 1 else 0
· 使用引理 `Mathlib.Meta.Positivity.ite_nonneg_of_pos_of_nonneg`：ite_nonneg_of_pos_o
f_nonneg [Preorder α] (ha : 0 < a) (hb : 0 <= b) : 0 <= ite p a b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `descPochhammer_pos`：descPochhammer_pos {n : Nat} {s : S} (h : n - 1 < s)
 : 0 < (descPochhammer S n).eval s

--- 原说明 ---
`descPochhammer S n` is nonnegative on `[n-1, ∞)`.
-/
theorem descPochhammer_nonneg {n : ℕ} {s : S} (h : n - 1 ≤ s) :
    0 ≤ (descPochhammer S n).eval s := by
  rcases eq_or_lt_of_le h with heq | h
  · rw [← heq, descPochhammer_eval_eq_ascPochhammer,
      sub_sub_cancel_left, neg_add_cancel, ascPochhammer_eval_zero]
    positivity
  · exact (descPochhammer_pos h).le

/-- `descPochhammer S n` is at least `(s-n+1)^n` on `[n-1, ∞)`. -/
/-
**pow_le_descPochhammer_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_descPochhammer_eval {n : Nat} {s : S} (h : n - 1 <= s) : (s - n + 1
) ^ n <= (descPochhammer S n).eval s
参数：h : n - 1 <= s。
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
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `le_of_sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, 0 ≤ a - b → b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `descPochhammer_succ_eval`：descPochhammer_succ_eval {S : Type*} [Ring S] 
(n : Nat) (k : S) : (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eva
l k * (k - n)
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
`descPochhammer S n` is at least `(s-n+1)^n` on `[n-1, ∞)`.
-/
theorem pow_le_descPochhammer_eval {n : ℕ} {s : S} (h : n - 1 ≤ s) :
    (s - n + 1) ^ n ≤ (descPochhammer S n).eval s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_sub_cancel_right, ← sub_nonneg] at h
    have hsub1 : n - 1 ≤ s := (sub_le_self (n : S) zero_le_one).trans (le_of_sub_nonneg h)
    rw [pow_succ, descPochhammer_succ_eval, Nat.cast_add_one, sub_add, add_sub_cancel_right]
    apply mul_le_mul _ le_rfl h (descPochhammer_nonneg hsub1)
    exact (ih hsub1).trans' <| pow_le_pow_left₀ h (le_add_of_nonneg_right zero_le_one) n

/-- `descPochhammer S n` is monotone on `[n-1, ∞)`. -/
/-
**monotoneOn_descPochhammer_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_descPochhammer_eval (n : Nat) : MonotoneOn (descPochhammer S n)
.eval (Set.Ici (n - 1 : S))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `descPochhammer_succ_eval`：descPochhammer_succ_eval {S : Type*} [Ring S] 
(n : Nat) (k : S) : (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eva
l k * (k - n)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `descPochhammer_nonneg`：descPochhammer_nonneg {n : Nat} {s : S} (h : n - 
1 <= s) : 0 <= (descPochhammer S n).eval s

--- 原说明 ---
`descPochhammer S n` is monotone on `[n-1, ∞)`.
-/
theorem monotoneOn_descPochhammer_eval (n : ℕ) :
    MonotoneOn (descPochhammer S n).eval (Set.Ici (n - 1 : S)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ici, Nat.cast_add_one, add_sub_cancel_right] at ha hb
    have ha_sub1 : n - 1 ≤ a := (sub_le_self (n : S) zero_le_one).trans ha
    have hb_sub1 : n - 1 ≤ b := (sub_le_self (n : S) zero_le_one).trans hb
    simp_rw [descPochhammer_succ_eval]
    exact mul_le_mul (ih ha_sub1 hb_sub1 hab) (sub_le_sub_right hab (n : S))
      (sub_nonneg_of_le ha) (descPochhammer_nonneg hb_sub1)

end StrictOrderedRing

variable (K : Type*)

namespace Nat
section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

/-
**Nat.cast_choose_eq_ascPochhammer_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_choose_eq_ascPochhammer_div (a b : Nat) : (a.choose b : K) = (ascPoch
hammer K b).eval ↑(a - (b - 1)) / b !
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `Nat.cast_descFactorial`：cast_descFactorial : a.descFactorial b = (ascPoc
hhammer S b).eval (a - (b - 1) : S)
-/
theorem cast_choose_eq_ascPochhammer_div (a b : ℕ) :
    (a.choose b : K) = (ascPochhammer K b).eval ↑(a - (b - 1)) / b ! := by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) ≠ 0), ← cast_mul,
    mul_comm, ← descFactorial_eq_factorial_mul_choose, ← cast_descFactorial]

end DivisionSemiring

section DivisionRing
variable [DivisionRing K] [CharZero K]

/-
**Nat.cast_choose_eq_descPochhammer_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_choose_eq_descPochhammer_div (a b : Nat) : (a.choose b : K) = (descPo
chhammer K b).eval ↑a / b !
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `descPochhammer_eval_eq_descFactorial`：descPochhammer_eval_eq_descFactori
al (n k : Nat) : (descPochhammer R k).eval (n : R) = n.descFactorial k
-/
theorem cast_choose_eq_descPochhammer_div (a b : ℕ) :
    (a.choose b : K) = (descPochhammer K b).eval ↑a / b ! := by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) ≠ 0), ← cast_mul,
    mul_comm, ← descFactorial_eq_factorial_mul_choose, descPochhammer_eval_eq_descFactorial]

end DivisionRing
end Nat

