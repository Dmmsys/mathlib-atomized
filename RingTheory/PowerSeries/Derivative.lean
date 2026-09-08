/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill, Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Formal derivatives of univariate power series

This file defines `PowerSeries.derivative`, the formal derivative of a univariate
power series, as a `Derivation R R⟦X⟧ R⟦X⟧`.

See also `MvPowerSeries.pderiv` for the multivariate setting.

## Main definitions

- `PowerSeries.derivative`: the formal derivative, as a derivation.

## Main results

- `PowerSeries.coeff_derivative`: coefficient formula
  `coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)`.
- `PowerSeries.derivative_coe`: compatibility with `Polynomial.derivative`.
- `PowerSeries.trunc_derivative`: truncation commutes with differentiation.
- `PowerSeries.derivative.ext`: a power series is determined by its constant term and derivative.
- `PowerSeries.derivative_pow`: power rule.
- `PowerSeries.derivative_inv`, `PowerSeries.derivative_inv'`: derivative of an inverse.
- `PowerSeries.derivative_subst`: chain rule for power series substitution.
-/

@[expose] public section

namespace PowerSeries

open Polynomial Derivation Nat

variable {R : Type*}

section CommutativeSemiring

variable [CommSemiring R]

variable (R) in
/-- The formal derivative of a formal power series -/
/-
**PowerSeries.derivative** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：derivative : Derivation R R⟦X⟧ R⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formal derivative of a formal power series
-/
noncomputable def derivative : Derivation R R⟦X⟧ R⟦X⟧ :=
  MvPowerSeries.pderiv R ()

/-- Abbreviation of `PowerSeries.derivative`, the formal derivative on `R⟦X⟧` -/
scoped notation "d⁄dX" => derivative

/-
**PowerSeries.derivative_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {r : R}, (PowerSeries.derivative 
R) (PowerSeries.C r) = 0
参数：PowerSeries.derivative R；PowerSeries.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_C`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemi
ring R] {i : σ} {r : R},   (MvPowerSeries.pderiv R i) (MvPowerSeries.C r) = 0
-/
@[simp] theorem derivative_C {r : R} : d⁄dX R (C r) = 0 := MvPowerSeries.pderiv_C
/-
**PowerSeries.derivative_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivative_one : d⁄dX R 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_one`：pderiv_one {i : σ} : pderiv R i 1 = 0
-/
theorem derivative_one : d⁄dX R 1 = 0 := MvPowerSeries.pderiv_one
/-
**PowerSeries.coeff_derivative** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_derivative (f : R⟦X⟧) (n : Nat) : coeff n (d⁄dX R f) = coeff (n + 1)
 f * (n + 1)
参数：f : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_pderiv`：coeff_pderiv {i : σ} (f : MvPowerSeries σ R)
 (n : σ ->₀ Nat) : coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1) := by
  simp [coeff, derivative, MvPowerSeries.coeff_pderiv]

/-- The `k`-th coefficient of the `n`-th formal derivative: differentiating `n` times multiplies the
`(k + n)`-th coefficient by the ascending factorial `(k + 1)(k + 2) ⋯ (k + n)`. -/
/-
**PowerSeries.coeff_iterate_derivative** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_iterate_derivative (f : R⟦X⟧) (n k : Nat) : coeff k ((d⁄dX R)^[n] f)
 = (k + 1).ascFactorial n * coeff (k + n) f
参数：f : R⟦X⟧；n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `PowerSeries.coeff_derivative`：coeff_derivative (f : R⟦X⟧) (n : Nat) : co
eff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)
· 使用定理 `Nat.ascFactorial_succ`：ascFactorial_succ {n k : Nat} : n.ascFactorial k.
succ = (n + k) * n.ascFactorial k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_ascFactorial`：∀ (n k : ℕ), n * n.succ.ascFactorial k = (n + k) 
* n.ascFactorial k

--- 原说明 ---
The `k`-th coefficient of the `n`-th formal derivative: differentiating `n` time
s multiplies the
`(k + n)`-th coefficient by the ascending factorial `(k + 1)(k + 2) ⋯ (k + n)`.
-/
theorem coeff_iterate_derivative (f : R⟦X⟧) (n k : ℕ) :
    coeff k ((d⁄dX R)^[n] f) = (k + 1).ascFactorial n * coeff (k + n) f := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.ascFactorial_succ,
      ← Nat.succ_ascFactorial]
    grind

/-- Specialisation of `coeff_iterate_derivative` at `k = 0`: the constant term of the `n`-th formal
derivative recovers `n !` times the `n`-th coefficient, `constantCoeff (Dⁿ f) = n ! * coeff n f`. -/
/-
**PowerSeries.constantCoeff_iterate_derivative** 是 Mathlib 中的一个定理，位于命名空间 `PowerS
eries`。
形式化陈述：constantCoeff_iterate_derivative (f : R⟦X⟧) (n : Nat) : constantCoeff ((d⁄
dX R)^[n] f) = n ! * coeff n f
参数：f : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.one_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial
· 使用定理 `PowerSeries.coeff_iterate_derivative`：coeff_iterate_derivative (f : R⟦X⟧
) (n k : Nat) : coeff k ((d⁄dX R)^[n] f) = (k + 1).ascFactorial n * coeff (k + n
) f

--- 原说明 ---
Specialisation of `coeff_iterate_derivative` at `k = 0`: the constant term of th
e `n`-th formal
derivative recovers `n !` times the `n`-th coefficient, `constantCoeff (Dⁿ f) = 
n ! * coeff n f`.
-/
theorem constantCoeff_iterate_derivative (f : R⟦X⟧) (n : ℕ) :
    constantCoeff ((d⁄dX R)^[n] f) = n ! * coeff n f := by
  simpa using coeff_iterate_derivative f n 0
/-
**PowerSeries.derivative_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivative_coe (f : R[X]) : d⁄dX R f = Polynomial.derivative f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_derivative`：coeff_derivative (f : R⟦X⟧) (n : Nat) : co
eff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Polynomial.coeff_derivative`：coeff_derivative (p : R[X]) (n : Nat) : coe
ff (derivative p) n = coeff p (n + 1) * (n + 1)
-/
theorem derivative_coe (f : R[X]) : d⁄dX R f = Polynomial.derivative f := by
  ext
  rw [coeff_derivative, coeff_coe, coeff_coe, Polynomial.coeff_derivative]
/-
**PowerSeries.derivative_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], (PowerSeries.derivative R) Power
Series.X = 1
参数：PowerSeries.derivative R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_X_self`：pderiv_X_self {i : σ} : pderiv R i (X i) = 
1
-/
@[simp] theorem derivative_X : d⁄dX R (X : R⟦X⟧) = 1 :=
  MvPowerSeries.pderiv_X_self

-- We can't use `MvPowerSeries.trunc_pderiv` in the following proof,
-- since `PowerSeries.trunc` is not defined in terms of `MvPowerSeries.trunc`.
/-
**PowerSeries.trunc_derivative** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_derivative (f : R⟦X⟧) (n : Nat) : trunc n (d⁄dX R f) = Polynomial.de
rivative (trunc (n + 1) f)
参数：f : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `PowerSeries.coeff_derivative`：coeff_derivative (f : R⟦X⟧) (n : Nat) : co
eff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)
· 使用定理 `Polynomial.coeff_derivative`：coeff_derivative (p : R[X]) (n : Nat) : coe
ff (derivative p) n = coeff p (n + 1) * (n + 1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem trunc_derivative (f : R⟦X⟧) (n : ℕ) :
    trunc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f) := by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative, Polynomial.coeff_derivative, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [Polynomial.coeff_derivative, coeff_trunc, if_neg this, zero_mul]
/-
**PowerSeries.trunc_derivative'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_derivative' (f : R⟦X⟧) (n : Nat) : trunc (n - 1) (d⁄dX R f) = Polyno
mial.derivative (trunc n f)
参数：f : R⟦X⟧；n : Nat。
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
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `PowerSeries.trunc_derivative`：trunc_derivative (f : R⟦X⟧) (n : Nat) : tr
unc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `PowerSeries.trunc_one_left`：trunc_one_left (p : R⟦X⟧) : trunc (R
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `Polynomial.derivative_zero`：derivative_zero : derivative (0 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem trunc_derivative' (f : R⟦X⟧) (n : ℕ) :
    trunc (n - 1) (d⁄dX R f) = Polynomial.derivative (trunc n f) := by
  cases n <;> simp [trunc_derivative]

/-- The derivative of `g^n` equals `n * g^(n-1) * g'`. -/
/-
**PowerSeries.derivative_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivative_pow (g : R⟦X⟧) (n : Nat) : d⁄dX R (g ^ n) = n * g ^ (n - 1) * d
⁄dX R g
参数：g : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_pow`：pderiv_pow {i : σ} (g : MvPowerSeries σ R) (n 
: Nat) : pderiv R i (g ^ n) = n * g ^ (n - 1) * pderiv R i g

--- 原说明 ---
The derivative of `g^n` equals `n * g^(n-1) * g'`.
-/
theorem derivative_pow (g : R⟦X⟧) (n : ℕ) :
    d⁄dX R (g ^ n) = n * g ^ (n - 1) * d⁄dX R g :=
  MvPowerSeries.pderiv_pow g n

end CommutativeSemiring

/-- If `f` and `g` have the same constant term and derivative, then they are equal. -/
/-
**PowerSeries.derivative.ext** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.derivative`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [IsAddTorsionFree R] {f g : PowerSeri
es R},   (PowerSeries.derivative R) f = (PowerSeries.derivative R) g →     Power
Series.constantCoeff f = PowerSeries.constantCoeff g → f = g
参数：PowerSeries.derivative R；PowerSeries.derivative R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv.ext`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRi
ng R] [IsAddTorsionFree R] {f g : MvPowerSeries σ R},   (∀ (i : σ), (MvPowerSeri
es.pderiv R i)…

--- 原说明 ---
If `f` and `g` have the same constant term and derivative, then they are equal.
-/
theorem derivative.ext [CommRing R] [IsAddTorsionFree R] {f g} (hD : d⁄dX R f = d⁄dX R g)
    (hc : constantCoeff f = constantCoeff g) : f = g :=
  MvPowerSeries.pderiv.ext (fun _ => hD) hc

@[simp]
/-
**PowerSeries.derivative_inv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivative_inv [CommRing R] (f : R⟦X⟧ˣ) : d⁄dX R ↑f⁻¹ = -(↑f⁻¹ : R⟦X⟧) ^ 2
 * d⁄dX R f
参数：f : R⟦X⟧ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_inv`：pderiv_inv {i : σ} [CommRing R] (f : (MvPowerS
eries σ R)ˣ) : pderiv R i ↑f⁻¹ = -(↑f⁻¹ : MvPowerSeries σ R) ^ 2 * pderiv R i f
-/
theorem derivative_inv [CommRing R] (f : R⟦X⟧ˣ) :
    d⁄dX R ↑f⁻¹ = -(↑f⁻¹ : R⟦X⟧) ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_inv f

@[simp]
/-
**PowerSeries.derivative_invOf** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivative_invOf [CommRing R] (f : R⟦X⟧) [Invertible f] : d⁄dX R ⅟f = -⅟f 
^ 2 * d⁄dX R f
参数：f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_invOf`：pderiv_invOf {i : σ} [CommRing R] (f : MvPow
erSeries σ R) [Invertible f] : pderiv R i ⅟f = -⅟f ^ 2 * pderiv R i f
-/
theorem derivative_invOf [CommRing R] (f : R⟦X⟧) [Invertible f] :
    d⁄dX R ⅟f = -⅟f ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_invOf f

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv R⟦X⟧` for more general base rings `R`.
-/

/-
**PowerSeries.derivative_inv'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (f : PowerSeries R),   (PowerSeries.deri
vative R) f⁻¹ = -f⁻¹ ^ 2 * (PowerSeries.derivative R) f
参数：f : PowerSeries R；PowerSeries.derivative R；PowerSeries.derivative R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.pderiv_inv'`：pderiv_inv' {i : σ} [Field R] (f : MvPowerSer
ies σ R) : pderiv R i f⁻¹ = -f⁻¹ ^ 2 * pderiv R i f

--- 原说明 ---
The following theorem is stated only in the case that `R` is a field. This is be
cause
there is currently no instance of `Inv R⟦X⟧` for more general base rings `R`.
-/
@[simp] theorem derivative_inv' [Field R] (f : R⟦X⟧) : d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_inv' f

/-- Chain rule for polynomials viewed as power series.  Use `derivative_subst` instead. -/
/-
**PowerSeries.derivative_subst_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Chain rule for polynomials viewed as power series.  Use `derivative_subst` inste
ad.
-/
private theorem derivative_subst_coe [CommRing R] (p : Polynomial R) {g : R⟦X⟧} (hg : HasSubst g) :
    d⁄dX R ((p : R⟦X⟧).subst g) = (d⁄dX R (p : R⟦X⟧)).subst g * d⁄dX R g := by
  simp [subst_coe hg, derivative_coe, Derivation.comp_aeval_eq (a := g) (derivative R) p,
    smul_eq_mul]
/-
**PowerSeries.derivative_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivative_subst [CommRing R] {f g : R⟦X⟧} (hg : HasSubst g) : d⁄dX R (f.s
ubst g) = (d⁄dX R f).subst g * d⁄dX R g
参数：hg : HasSubst g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `Filter.Eventually.exists_forall_of_atTop`：∀ {α : Type u_3} [inst : Preor
der α] [IsDirectedOrder α] {p : α → Prop} [Nonempty α],   (∀ᶠ (x : α) in Filter.
atTop, p x) → ∃ a, ∀ (b : α), …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `PowerSeries.HasSubst.eventually_coeff_pow_eq_zero`：∀ {A : Type u_1} [ins
t : CommRing A] {f : PowerSeries A},   PowerSeries.HasSubst f → ∀ (n : ℕ), ∀ᶠ (m
 : ℕ) in Filter.atTop, ∀ n' ≤ n, (Power…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_subst'`：coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f :
 R⟦X⟧) (e : Nat) : coeff e (f.subst b) = finsum (fun (d : Nat) => coeff d f • Po
werSeries.coef…
· 使用定理 `finsum_congr`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M] {
f g : α → M}, (∀ (x : α), f x = g x) → finsum f = finsum g
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `PowerSeries.coeff_coe_trunc_of_lt`：coeff_coe_trunc_of_lt {n m} {f : R⟦X⟧
} (h : n < m) : coeff n (trunc m f) = coeff n f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_derivative`：coeff_derivative (f : R⟦X⟧) (n : Nat) : co
eff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.RingTheory.PowerSeries.Derivative.0.PowerSeries.derivat
ive_subst_coe`：∀ {R : Type u_1} [inst : CommRing R] (p : Polynomial R) {g : Powe
rSeries R},   PowerSeries.HasSubst g →     (PowerSeries.derivative R) (Powe…
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem derivative_subst [CommRing R] {f g : R⟦X⟧} (hg : HasSubst g) :
    d⁄dX R (f.subst g) = (d⁄dX R f).subst g * d⁄dX R g := by
  ext n
  obtain ⟨m, hm⟩ := (hg.eventually_coeff_pow_eq_zero (n + 1)).exists_forall_of_atTop
  have : coeff (n + 1) (f.subst g) = coeff (n + 1) ((↑(trunc (m + 1) f) : R⟦X⟧).subst g) := by
    rw [coeff_subst' hg, coeff_subst' hg]
    refine finsum_congr fun d ↦ ?_
    obtain hd | hd := lt_or_ge d m
    · rw [coeff_coe_trunc_of_lt (by lia)]
    · simp [coeff_trunc, hd, hm]
  rw [coeff_derivative, this, ← coeff_derivative, derivative_subst_coe _ hg, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
  congr 1
  simp only [coeff_subst' hg, coeff_derivative, coeff_coe, coeff_trunc]
  exact finsum_congr fun d ↦ by split_ifs <;> simp (disch := grind [Finset.mem_antidiagonal]) [hm]

section deprecated

variable [CommSemiring R]

/--
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `derivative` on `R⟦X⟧`.
-/
@[deprecated derivative (since := "2026-06-26")]
/-
**PowerSeries.derivativeFun** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：derivativeFun (f : R⟦X⟧)
参数：f : R⟦X⟧。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `derivative` on `R⟦X⟧`.
-/
noncomputable def derivativeFun (f : R⟦X⟧) := (derivative R).toFun f

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_add" (since := "2026-06-26")]
/-
**PowerSeries.derivativeFun_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivativeFun_add (f g : R⟦X⟧) : derivativeFun (f + g) = derivativeFun f +
 derivativeFun g
参数：f g : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_add`：∀ {R : Type u_1} {A : Type u_2} {M : Type u_4} [inst
 : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMonoid M] [inst_
3 : Alge…
-/
theorem derivativeFun_add (f g : R⟦X⟧) :
    derivativeFun (f + g) = derivativeFun f + derivativeFun g :=
  (derivative R).map_add f g

set_option linter.deprecated false in
@[deprecated "Use Derivation.leibniz" (since := "2026-06-26")]
/-
**PowerSeries.derivativeFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivativeFun_mul (f g : R⟦X⟧) : derivativeFun (f * g) = f • g.derivativeF
un + g • f.derivativeFun
参数：f g : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
-/
theorem derivativeFun_mul (f g : R⟦X⟧) :
    derivativeFun (f * g) = f • g.derivativeFun + g • f.derivativeFun :=
  (derivative R).leibniz f g

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_one_eq_zero" (since := "2026-06-26")]
/-
**PowerSeries.derivativeFun_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
-/
theorem derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0 :=
  (derivative R).map_one_eq_zero

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_smul" (since := "2026-06-26")]
/-
**PowerSeries.derivativeFun_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • deriva
tiveFun f
参数：r : R；f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
-/
theorem derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • derivativeFun f :=
  (derivative R).map_smul r f

@[deprecated (since := "2026-06-26")] alias derivativeFun_C := derivative_C

@[deprecated (since := "2026-06-26")] alias coeff_derivativeFun := coeff_derivative

@[deprecated (since := "2026-06-26")] alias derivativeFun_coe := derivative_coe

@[deprecated (since := "2026-06-26")] alias trunc_derivativeFun := trunc_derivative

end deprecated

end PowerSeries

