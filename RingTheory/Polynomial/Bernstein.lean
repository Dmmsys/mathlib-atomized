/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernsteinPolynomial (R : Type*) [CommRing R] (n ν : ℕ) : R[X] :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : Fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(Finset.range (n + 1)).sum (fun ν ↦ bernsteinPolynomial R n ν) = 1`
* `(Finset.range (n + 1)).sum (fun ν ↦ ν • bernsteinPolynomial R n ν) = n • X`
* `(Finset.range (n + 1)).sum (fun ν ↦ (ν * (ν-1)) • bernsteinPolynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `Mathlib/Analysis/SpecialFunctions/Bernstein.lean`, which defines the Bernstein
approximations of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly
to `f`.
-/

@[expose] public section


noncomputable section

open Nat (choose)

open Polynomial (X)

open scoped Polynomial

variable (R : Type*) [CommRing R]

/-- `bernsteinPolynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
/-
**bernsteinPolynomial** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bernsteinPolynomial (n ν : Nat) : R[X]
参数：n ν : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bernsteinPolynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitra
ry commutative ring.
-/
def bernsteinPolynomial (n ν : ℕ) : R[X] :=
  (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : bernsteinPolynomial ℤ 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [bernsteinPolynomial, choose]
  ring

namespace bernsteinPolynomial

/-
**bernsteinPolynomial.eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomi
al`。
形式化陈述：eq_zero_of_lt {n ν : Nat} (h : n < ν) : bernsteinPolynomial R n ν = 0
参数：h : n < ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

section

variable {R} {S : Type*} [CommRing S]

@[simp]
/-
**bernsteinPolynomial.map** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：map (f : R ->+* S) (n ν : Nat) : (bernsteinPolynomial R n ν).map f = berns
teinPolynomial S n ν
参数：f : R ->+* S；n ν : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_natCast`：∀ {R : Type u} {S : Type v} [inst : Semiring R] 
[inst_1 : Semiring S] (f : R →+* S) (n : ℕ), Polynomial.map f ↑n = ↑n
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map (f : R →+* S) (n ν : ℕ) :
    (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν := by simp [bernsteinPolynomial]

end

/-
**bernsteinPolynomial.flip** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：flip (n ν : Nat) (h : ν <= n) : (bernsteinPolynomial R n ν).comp (1 - X) =
 bernsteinPolynomial R n (n - ν)
参数：n ν : Nat；h : ν <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Polynomial.natCast_comp`：natCast_comp {n : Nat} : (n : R[X]).comp p = n
· 使用定理 `Polynomial.pow_comp`：pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) 
(n : Nat) : (p ^ n).comp q = p.comp q ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用定理 `tsub_tsub_assoc`：tsub_tsub_assoc (h₁ : b <= a) (h₂ : c <= b) : a - (b - 
c) = a - b + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flip (n ν : ℕ) (h : ν ≤ n) :
    (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) := by
  simp [bernsteinPolynomial, h, tsub_tsub_assoc, mul_right_comm]
/-
**bernsteinPolynomial.flip'** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：flip' (n ν : Nat) (h : ν <= n) : bernsteinPolynomial R n ν = (bernsteinPol
ynomial R n (n - ν)).comp (1 - X)
参数：n ν : Nat；h : ν <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bernsteinPolynomial.flip`：flip (n ν : Nat) (h : ν <= n) : (bernsteinPoly
nomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν)
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Polynomial.comp_X`：comp_X : p.comp X = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flip' (n ν : ℕ) (h : ν ≤ n) :
    bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) := by
  simp [← flip _ _ _ h, Polynomial.comp_assoc]
/-
**bernsteinPolynomial.eval_at_0** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：eval_at_0 (n ν : Nat) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then
 1 else 0
参数：n ν : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.eq_1`：∀ (R : Type u_1) [inst : CommRing R] (n ν : ℕ)
,   bernsteinPolynomial R n ν = ↑(n.choose ν) * Polynomial.X ^ ν * (1 - Polynomi
al.X) ^ (n - ν…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem eval_at_0 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 := by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · simp [zero_pow h]
/-
**bernsteinPolynomial.eval_at_1** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：eval_at_1 (n ν : Nat) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then
 1 else 0
参数：n ν : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.eq_1`：∀ (R : Type u_1) [inst : CommRing R] (n ν : ℕ)
,   bernsteinPolynomial R n ν = ↑(n.choose ν) * Polynomial.X ^ ν * (1 - Polynomi
al.X) ^ (n - ν…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.sub_ne_zero_of_lt`：∀ {a b : ℕ}, a < b → b - a ≠ 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 31 条，此处仅展示前 30 条）
-/
theorem eval_at_1 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 := by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · obtain hνn | hnν := Ne.lt_or_gt h
    · simp [zero_pow <| Nat.sub_ne_zero_of_lt hνn]
    · simp [Nat.choose_eq_zero_of_lt hnν]
/-
**bernsteinPolynomial.derivative_succ_aux** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPo
lynomial`。
形式化陈述：derivative_succ_aux (n ν : Nat) : Polynomial.derivative (bernsteinPolynomi
al R (n + 1) (ν + 1)) = (n + 1) * (bernsteinPolynomial R n ν - bernsteinPolynomi
al R n (ν + 1))
参数：n ν : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.eq_1`：∀ (R : Type u_1) [inst : CommRing R] (n ν : ℕ)
,   bernsteinPolynomial R n ν = ↑(n.choose ν) * Polynomial.X ^ ν * (1 - Polynomi
al.X) ^ (n - ν…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.add_one_mul_choose_eq`：∀ (n k : ℕ), (n + 1) * n.choose k = (n + 1).c
hoose (k + 1) * (k + 1)
· 使用定理 `tsub_add_eq_tsub_tsub`：tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) =
 a - b - c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.choose_mul_succ_eq`：choose_mul_succ_eq (n k : Nat) : n.choose k * (n
 + 1) = (n + 1).choose k * (n + 1 - k)
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `Polynomial.derivative_natCast`：derivative_natCast {n : Nat} : derivative
 (n : R[X]) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.derivative_pow`：derivative_pow (p : R[X]) (n : Nat) : derivat
ive (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
（共 45 条，此处仅展示前 30 条）
-/
theorem derivative_succ_aux (n ν : ℕ) :
    Polynomial.derivative (bernsteinPolynomial R (n + 1) (ν + 1)) =
      (n + 1) * (bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν + 1)) := by
  rw [bernsteinPolynomial]
  suffices ((n + 1).choose (ν + 1) : R[X]) * ((↑(ν + 1 : ℕ) : R[X]) * X ^ ν) * (1 - X) ^ (n - ν) -
      ((n + 1).choose (ν + 1) : R[X]) * X ^ (ν + 1) * ((↑(n - ν) : R[X]) * (1 - X) ^ (n - ν - 1)) =
      (↑(n + 1) : R[X]) * ((n.choose ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν) -
        (n.choose (ν + 1) : R[X]) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))) by
    simpa [Polynomial.derivative_pow, ← sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
      Polynomial.derivative_mul, Polynomial.derivative_natCast, zero_mul,
      Nat.cast_add, algebraMap.coe_one, Polynomial.derivative_X, mul_one, zero_add,
      Polynomial.derivative_sub, Polynomial.derivative_one, zero_sub, mul_neg, Nat.sub_zero,
      bernsteinPolynomial, map_add, map_natCast, Nat.cast_one]
  conv_rhs => rw [mul_sub]
  -- We'll prove the two terms match up separately.
  refine congr (congr_arg Sub.sub ?_) ?_
  · simp only [← mul_assoc]
    apply congr (congr_arg (· * ·) (congr (congr_arg (· * ·) _) rfl)) rfl
    -- Now it's just about binomial coefficients
    exact mod_cast congr_arg (fun m : ℕ => (m : R[X])) (Nat.add_one_mul_choose_eq n ν).symm
  · rw [← tsub_add_eq_tsub_tsub, ← mul_assoc, ← mul_assoc]; congr 1
    rw [mul_comm, ← mul_assoc, ← mul_assoc]; congr 1
    norm_cast
    congr 1
    convert! (Nat.choose_mul_succ_eq n (ν + 1)).symm using 1
    · convert! mul_comm _ _ using 2
      simp
    · apply mul_comm
/-
**bernsteinPolynomial.derivative_succ** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolyno
mial`。
形式化陈述：derivative_succ (n ν : Nat) : Polynomial.derivative (bernsteinPolynomial R
 n (ν + 1)) = n * (bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 
1) (ν + 1))
参数：n ν : Nat。
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
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.derivative_zero`：derivative_zero : derivative (0 : R[X]) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `bernsteinPolynomial.derivative_succ_aux`：derivative_succ_aux (n ν : Nat)
 : Polynomial.derivative (bernsteinPolynomial R (n + 1) (ν + 1)) = (n + 1) * (be
rnsteinPolynomial R n ν - ber…
-/
theorem derivative_succ (n ν : ℕ) : Polynomial.derivative (bernsteinPolynomial R n (ν + 1)) =
    n * (bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν + 1)) := by
  cases n
  · simp [bernsteinPolynomial]
  · rw [Nat.cast_succ]; apply derivative_succ_aux
/-
**bernsteinPolynomial.derivative_zero** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolyno
mial`。
形式化陈述：derivative_zero (n : Nat) : Polynomial.derivative (bernsteinPolynomial R n
 0) = -n * bernsteinPolynomial R (n - 1) 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.derivative_pow`：derivative_pow (p : R[X]) (n : Nat) : derivat
ive (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_one`：derivative_one : derivative (1 : R[X]) = 0
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivative_zero (n : ℕ) :
    Polynomial.derivative (bernsteinPolynomial R n 0) = -n * bernsteinPolynomial R (n - 1) 0 := by
  simp [bernsteinPolynomial, Polynomial.derivative_pow]
/-
**bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt** 是 Mathlib 中的一个定理，位
于命名空间 `bernsteinPolynomial`。
形式化陈述：iterate_derivative_at_0_eq_zero_of_lt (n : Nat) {ν k : Nat} : k < ν -> (Po
lynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 0 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bernsteinPolynomial.eval_at_0`：eval_at_0 (n ν : Nat) : (bernsteinPolynom
ial R n ν).eval 0 = if ν = 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `bernsteinPolynomial.derivative_succ`：derivative_succ (n ν : Nat) : Polyn
omial.derivative (bernsteinPolynomial R n (ν + 1)) = n * (bernsteinPolynomial R 
(n - 1) ν - bernsteinPoly…
· 使用定理 `Polynomial.iterate_derivative_natCast_mul`：iterate_derivative_natCast_mu
l {n k : Nat} {f : R[X]} : derivative^[k] ((n : R[X]) * f) = n * derivative^[k] 
f
· 使用定理 `Polynomial.iterate_derivative_sub`：iterate_derivative_sub {k : Nat} {f g
 : R[X]} : derivative^[k] (f - g) = derivative^[k] f - derivative^[k] g
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.pred_le_pred`：∀ {n m : ℕ}, n ≤ m → n.pred ≤ m.pred
-/
theorem iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < ν → (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 0 = 0 := by
  rcases ν with - | ν
  · rintro ⟨⟩
  · rw [Nat.lt_succ_iff]
    induction k generalizing n ν with
    | zero => simp [eval_at_0]
    | succ k ih =>
      simp only [derivative_succ, Function.comp_apply,
        Function.iterate_succ, Polynomial.iterate_derivative_sub,
        Polynomial.iterate_derivative_natCast_mul, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_sub]
      intro h
      apply mul_eq_zero_of_right
      rw [ih _ _ (Nat.le_of_succ_le h), sub_zero]
      convert! ih _ _ (Nat.pred_le_pred h)
      exact (Nat.succ_pred_eq_of_pos (k.succ_pos.trans_le h)).symm

@[simp]
/-
**bernsteinPolynomial.iterate_derivative_succ_at_0_eq_zero** 是 Mathlib 中的一个定理，位于
命名空间 `bernsteinPolynomial`。
形式化陈述：iterate_derivative_succ_at_0_eq_zero (n ν : Nat) : (Polynomial.derivative^
[ν] (bernsteinPolynomial R n (ν + 1))).eval 0 = 0
参数：n ν : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt`：iterate_deriv
ative_at_0_eq_zero_of_lt (n : Nat) {ν k : Nat} : k < ν -> (Polynomial.derivative
^[k] (bernsteinPolynomial R n ν)).eval 0 = 0
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
-/
theorem iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n (ν + 1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open Polynomial

@[simp]
/-
**bernsteinPolynomial.iterate_derivative_at_0** 是 Mathlib 中的一个定理，位于命名空间 `bernste
inPolynomial`。
形式化陈述：iterate_derivative_at_0 (n ν : Nat) : (Polynomial.derivative^[ν] (bernstei
nPolynomial R n ν)).eval 0 = (ascPochhammer R ν).eval ((n - (ν - 1) : Nat) : R)
参数：n ν : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.eval_at_0`：eval_at_0 (n ν : Nat) : (bernsteinPolynom
ial R n ν).eval 0 = if ν = 0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `le_tsub_of_add_le_right`：le_tsub_of_add_le_right (h : a + b <= c) : a <=
 c - b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `bernsteinPolynomial.derivative_succ`：derivative_succ (n ν : Nat) : Polyn
omial.derivative (bernsteinPolynomial R n (ν + 1)) = n * (bernsteinPolynomial R 
(n - 1) ν - bernsteinPoly…
· 使用定理 `Polynomial.iterate_derivative_natCast_mul`：iterate_derivative_natCast_mu
l {n k : Nat} {f : R[X]} : derivative^[k] ((n : R[X]) * f) = n * derivative^[k] 
f
· 使用定理 `Polynomial.iterate_derivative_sub`：iterate_derivative_sub {k : Nat} {f g
 : R[X]} : derivative^[k] (f - g) = derivative^[k] f - derivative^[k] g
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `bernsteinPolynomial.iterate_derivative_succ_at_0_eq_zero`：iterate_deriva
tive_succ_at_0_eq_zero (n ν : Nat) : (Polynomial.derivative^[ν] (bernsteinPolyno
mial R n (ν + 1))).eval 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
（共 58 条，此处仅展示前 30 条）
-/
theorem iterate_derivative_at_0 (n ν : ℕ) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 =
      (ascPochhammer R ν).eval ((n - (ν - 1) : ℕ) : R) := by
  by_cases! h : ν ≤ n
  · induction ν generalizing n with
    | zero => simp [eval_at_0]
    | succ ν ih =>
      have h' : ν ≤ n - 1 := le_tsub_of_add_le_right h
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero,
        Nat.succ_sub_succ_eq_sub, sub_zero, iterate_derivative_sub,
        iterate_derivative_natCast_mul, eval_one, eval_mul, eval_add, eval_sub, eval_X, eval_comp,
        eval_natCast, Function.comp_apply, Function.iterate_succ, ascPochhammer_succ_left]
      obtain rfl | h'' := ν.eq_zero_or_pos
      · simp
      · have : n - 1 - (ν - 1) = n - ν := by lia
        rw [this, ascPochhammer_eval_succ, Nat.sub_zero]
        rw_mod_cast [tsub_add_cancel_of_le (h'.trans n.pred_le)]
  · rw [tsub_eq_zero_iff_le.mpr (Nat.le_sub_one_of_lt h), eq_zero_of_lt R h]
    simp [pos_iff_ne_zero.mp (pos_of_gt h)]
/-
**bernsteinPolynomial.iterate_derivative_at_0_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`bernsteinPolynomial`。
形式化陈述：iterate_derivative_at_0_ne_zero [CharZero R] (n ν : Nat) (h : ν <= n) : (P
olynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 != 0
参数：n ν : Nat；h : ν <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bernsteinPolynomial.iterate_derivative_at_0`：iterate_derivative_at_0 (n 
ν : Nat) : (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 = (asc
Pochhammer R ν).eval ((n - (ν - 1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_pos`：ascPochhammer_pos (n : Nat) (s : S) (h : 0 < s) : 0 <
 (ascPochhammer S n).eval s
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 ≠ 0 := by
  simp only [bernsteinPolynomial.iterate_derivative_at_0, Ne]
  simp only [← ascPochhammer_eval_cast]
  norm_cast
  apply ne_of_gt
  obtain rfl | h' := Nat.eq_zero_or_pos ν
  · simp
  · rw [← Nat.succ_pred_eq_of_pos h'] at h
    exact ascPochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_le h))

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/


/-
**bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt** 是 Mathlib 中的一个定理，位
于命名空间 `bernsteinPolynomial`。
形式化陈述：iterate_derivative_at_1_eq_zero_of_lt (n : Nat) {ν k : Nat} : k < n - ν ->
 (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 1 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.flip'`：flip' (n ν : Nat) (h : ν <= n) : bernsteinPol
ynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.iterate_derivative_comp_one_sub_X`：iterate_derivative_comp_on
e_sub_X (p : R[X]) (k : Nat) : derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (der
ivative^[k] p).comp (1 - X)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt`：iterate_deriv
ative_at_0_eq_zero_of_lt (n : Nat) {ν k : Nat} : k < ν -> (Polynomial.derivative
^[k] (bernsteinPolynomial R n ν)).eval 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/
theorem iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < n - ν → (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 1 = 0 := by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]
/-
**bernsteinPolynomial.iterate_derivative_at_1** 是 Mathlib 中的一个定理，位于命名空间 `bernste
inPolynomial`。
形式化陈述：iterate_derivative_at_1 (n ν : Nat) (h : ν <= n) : (Polynomial.derivative^
[n - ν] (bernsteinPolynomial R n ν)).eval 1 = (-1) ^ (n - ν) * (ascPochhammer R 
(n - ν)).eval (ν + 1 : R)
参数：n ν : Nat；h : ν <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.flip'`：flip' (n ν : Nat) (h : ν <= n) : bernsteinPol
ynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.iterate_derivative_comp_one_sub_X`：iterate_derivative_comp_on
e_sub_X (p : R[X]) (k : Nat) : derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (der
ivative^[k] p).comp (1 - X)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `bernsteinPolynomial.iterate_derivative_at_0`：iterate_derivative_at_0 (n 
ν : Nat) : (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 = (asc
Pochhammer R ν).eval ((n - (ν - 1…
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 =
      (-1) ^ (n - ν) * (ascPochhammer R (n - ν)).eval (ν + 1 : R) := by
  rw [flip' _ _ _ h]
  simp only [iterate_derivative_comp_one_sub_X, eval_mul, eval_pow, eval_neg, eval_one, eval_comp,
    eval_sub, eval_X, sub_self, iterate_derivative_at_0]
  obtain rfl | h' := h.eq_or_lt
  · simp
  · norm_cast
    congr
    lia
/-
**bernsteinPolynomial.iterate_derivative_at_1_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`bernsteinPolynomial`。
形式化陈述：iterate_derivative_at_1_ne_zero [CharZero R] (n ν : Nat) (h : ν <= n) : (P
olynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 != 0
参数：n ν : Nat；h : ν <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinPolynomial.iterate_derivative_at_1`：iterate_derivative_at_1 (n 
ν : Nat) (h : ν <= n) : (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n 
ν)).eval 1 = (-1) ^ (n - ν) * (as…
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `neg_one_pow_mul_eq_zero_iff`：∀ {R : Type u} [inst : Ring R] {a : R} {n :
 ℕ}, (-1) ^ n * a = 0 ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `ascPochhammer_eval_cast`：ascPochhammer_eval_cast (n k : Nat) : (((ascPoc
hhammer Nat n).eval k : Nat) : S) = ((ascPochhammer S n).eval k : S)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ascPochhammer_pos`：ascPochhammer_pos (n : Nat) (s : S) (h : 0 < s) : 0 <
 (ascPochhammer S n).eval s
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 ≠ 0 := by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h, Ne, neg_one_pow_mul_eq_zero_iff, ←
    Nat.cast_succ, ← ascPochhammer_eval_cast, ← Nat.cast_zero, Nat.cast_inj]
  exact (ascPochhammer_pos _ _ (Nat.succ_pos ν)).ne'

open Submodule
/-
**bernsteinPolynomial.linearIndependent_aux** 是 Mathlib 中的一个定理，位于命名空间 `bernstein
Polynomial`。
形式化陈述：linearIndependent_aux (n k : Nat) (h : k <= n + 1) : LinearIndependent Rat
 fun ν : Fin k => bernsteinPolynomial Rat n ν
参数：n k : Nat；h : k <= n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_finSucc'`：linearIndependent_finSucc' {n} {v : Fin (n +
 1) -> V} : LinearIndependent K v ↔ LinearIndependent K (Fin.init v) ∧ v (Fin.la
st _) ∉ Submodul…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Submodule.notMem_span_of_apply_notMem_span_image`：notMem_span_of_apply_n
otMem_span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M} {s : Set M
} (h : f x ∉ Submodule.span R₂ (f '' s…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt`：iterate_deriv
ative_at_1_eq_zero_of_lt (n : Nat) {ν k : Nat} : k < n - ν -> (Polynomial.deriva
tive^[k] (bernsteinPolynomial R n ν)).eval 1 = …
· 使用定理 `tsub_lt_tsub_iff_left_of_le`：tsub_lt_tsub_iff_left_of_le (h : b <= a) : 
a - b < a - c ↔ c < b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iterate_map_zero`：∀ {M : Type u_10} {F : Type u_11} [inst : Zero M] [ins
t_1 : FunLike F M M] [ZeroHomClass F M M] (f : F) (n : ℕ),   (⇑f)^[n] 0 = 0
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
（共 44 条，此处仅展示前 30 条）
-/
theorem linearIndependent_aux (n k : ℕ) (h : k ≤ n + 1) :
    LinearIndependent ℚ fun ν : Fin k => bernsteinPolynomial ℚ n ν := by
  induction k with
  | zero => apply linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_finSucc'.mpr
    fconstructor
    · exact ih (le_of_lt h)
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih
      simp only [add_le_add_iff_right] at h
      simp only [Fin.val_last, Fin.init_def]
      dsimp
      apply notMem_span_of_apply_notMem_span_image (@Polynomial.derivative ℚ _ ^ (n - k))
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `span_image` into `span_image _`
      simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image _]
      intro p m
      apply_fun Polynomial.eval (1 : ℚ)
      simp only [Module.End.pow_apply]
      -- The right-hand side is nonzero,
      -- so it will suffice to show the left-hand side is always zero.
      suffices (Polynomial.derivative^[n - k] p).eval 1 = 0 by
        rw [this]
        exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm
      refine span_induction ?_ ?_ ?_ ?_ m
      · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        rintro ⟨a, w⟩; simp only
        rw [iterate_derivative_at_1_eq_zero_of_lt ℚ n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro a x _ h; simp [h]

/-- The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernsteinPolynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernsteinPolynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/
/-
**bernsteinPolynomial.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPoly
nomial`。
形式化陈述：linearIndependent (n : Nat) : LinearIndependent Rat fun ν : Fin (n + 1) =>
 bernsteinPolynomial Rat n ν
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bernsteinPolynomial.linearIndependent_aux`：linearIndependent_aux (n k : 
Nat) (h : k <= n + 1) : LinearIndependent Rat fun ν : Fin k => bernsteinPolynomi
al Rat n ν
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernsteinPolynomial n ν` for `ν = 
0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, eva
luated at 1,
annihilates `bernsteinPolynomial n ν` for `ν < k`, but has a nonzero value at `ν
 = k`.
-/
theorem linearIndependent (n : ℕ) :
    LinearIndependent ℚ fun ν : Fin (n + 1) => bernsteinPolynomial ℚ n ν :=
  linearIndependent_aux n (n + 1) le_rfl
/-
**bernsteinPolynomial.sum** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：sum (n : Nat) : (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) =
 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem sum (n : ℕ) : (∑ ν ∈ Finset.range (n + 1), bernsteinPolynomial R n ν) = 1 :=
  calc
    (∑ ν ∈ Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      simp only [bernsteinPolynomial, mul_comm, mul_assoc]
    _ = 1 := by simp

open Polynomial

open MvPolynomial hiding X
/-
**bernsteinPolynomial.sum_smul** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：sum_smul (n : Nat) : (∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial
 R n ν) = n • X
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.pderiv_X`：pderiv_X [DecidableEq σ] (i j : σ) : pderiv i (X 
j : MvPolynomial σ R) = Pi.single (M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `bernsteinPolynomial.eq_1`：∀ (R : Type u_1) [inst : CommRing R] (n ν : ℕ)
,   bernsteinPolynomial R n ν = ↑(n.choose ν) * Polynomial.X ^ ν * (1 - Polynomi
al.X) ^ (n - ν…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 84 条，此处仅展示前 30 条）
-/
theorem sum_smul (n : ℕ) :
    (∑ ν ∈ Finset.range (n + 1), ν • bernsteinPolynomial R n ν) = n • X := by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true ((x + y) ^ n)) * X
  -- On the left-hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : ∀ k : ℕ, k • bernsteinPolynomial R n k =
        (k : R[X]) * Polynomial.X ^ (k - 1) * (1 - Polynomial.X) ^ (n - k) * (n.choose k : R[X]) *
          Polynomial.X := by
      rintro (_ | k)
      · simp
      · rw [bernsteinPolynomial]
        simp only [← natCast_mul, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow, map_sum (pderiv true), map_sum (MvPolynomial.aeval e), Finset.sum_mul]
    -- Step inside the sum:
    refine Finset.sum_congr rfl fun k _ => (w k).trans ?_
    simp only [x, y, e, pderiv_true_x, pderiv_true_y, smul_eq_mul, nsmul_eq_mul,
      Bool.cond_true, Bool.cond_false, add_zero, mul_one, mul_zero, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_mul, Derivation.leibniz_pow, Derivation.map_natCast, map_natCast, map_pow,
      map_mul]
  · rw [(pderiv true).leibniz_pow, (pderiv true).map_add, pderiv_true_x, pderiv_true_y]
    simp only [x, y, e, smul_eq_mul, nsmul_eq_mul, map_natCast, map_pow, map_add,
      map_mul, Bool.cond_true, Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel,
      one_pow, add_zero, mul_one]
/-
**bernsteinPolynomial.sum_mul_smul** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomia
l`。
形式化陈述：sum_mul_smul (n : Nat) : (∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • ber
nsteinPolynomial R n ν) = (n * (n - 1)) • X ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.pderiv_X`：pderiv_X [DecidableEq σ] (i j : σ) : pderiv i (X 
j : MvPolynomial σ R) = Pi.single (M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `bernsteinPolynomial.eq_1`：∀ (R : Type u_1) [inst : CommRing R] (n ν : ℕ)
,   bernsteinPolynomial R n ν = ↑(n.choose ν) * Polynomial.X ^ ν * (1 - Polynomi
al.X) ^ (n - ν…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 97 条，此处仅展示前 30 条）
-/
theorem sum_mul_smul (n : ℕ) :
    (∑ ν ∈ Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν) =
      (n * (n - 1)) • X ^ 2 := by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the second `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true (pderiv true ((x + y) ^ n))) * X ^ 2
  -- On the left-hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : ∀ k : ℕ, (k * (k - 1)) • bernsteinPolynomial R n k =
        (n.choose k : R[X]) * ((1 - Polynomial.X) ^ (n - k) *
          ((k : R[X]) * ((↑(k - 1) : R[X]) * Polynomial.X ^ (k - 1 - 1)))) * Polynomial.X ^ 2 := by
      rintro (_ | _ | k)
      · simp
      · simp
      · rw [bernsteinPolynomial]
        simp only [← natCast_mul, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow, map_sum (pderiv true), map_sum (pderiv true), map_sum (MvPolynomial.aeval e),
      Finset.sum_mul]
    -- Step inside the sum:
    refine Finset.sum_congr rfl fun k _ => (w k).trans ?_
    simp only [x, y, e, pderiv_true_x, pderiv_true_y, smul_eq_mul, nsmul_eq_mul,
      Bool.cond_true, Bool.cond_false, add_zero, zero_add, mul_zero, mul_one,
      MvPolynomial.aeval_X,
      Derivation.leibniz_pow, Derivation.leibniz, Derivation.map_natCast, map_natCast, map_pow,
      map_mul]
  -- On the right-hand side, we'll just simplify.
  · simp only [x, y, e, (pderiv _).leibniz_pow,
      (pderiv true).map_add, pderiv_true_x, pderiv_true_y, smul_eq_mul, add_zero,
      mul_one, map_nsmul, map_pow, map_add, Bool.cond_true,
      Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel, one_pow, smul_smul,
      smul_one_mul]

/-- A certain linear combination of the previous three identities,
which we'll want later.
-/
/-
**bernsteinPolynomial.variance** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinPolynomial`。
形式化陈述：variance (n : Nat) : (∑ ν in Finset.range (n + 1), (n • Polynomial.X - (ν 
: R[X])) ^ 2 * bernsteinPolynomial R n ν) = n • Polynomial.X * ((1 : R[X]) - Pol
ynomial.X)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
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
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
A certain linear combination of the previous three identities,
which we'll want later.
-/
theorem variance (n : ℕ) :
    (∑ ν ∈ Finset.range (n + 1), (n • Polynomial.X - (ν : R[X])) ^ 2 * bernsteinPolynomial R n ν) =
      n • Polynomial.X * ((1 : R[X]) - Polynomial.X) := by
  have p : ((((Finset.range (n + 1)).sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
      (1 - (2 * n) • Polynomial.X) * (Finset.range (n + 1)).sum fun ν =>
        ν • bernsteinPolynomial R n ν) + n ^ 2 • X ^ 2 *
          (Finset.range (n + 1)).sum fun ν => bernsteinPolynomial R n ν) = _ :=
    rfl
  conv at p =>
    lhs
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [← natCast_mul]
    simp only [← mul_assoc]
    simp only [← add_mul]
  conv at p =>
    rhs
    rw [sum, sum_smul, sum_mul_smul, ← natCast_mul]
  calc
    _ = _ := Finset.sum_congr rfl fun k m => ?_
    _ = _ := p
    _ = _ := ?_
  · congr 1; simp only [← natCast_mul, push_cast]
    cases k <;> · simp; ring
  · simp only [← natCast_mul, push_cast]
    cases n
    · simp
    · simp; ring

end bernsteinPolynomial

