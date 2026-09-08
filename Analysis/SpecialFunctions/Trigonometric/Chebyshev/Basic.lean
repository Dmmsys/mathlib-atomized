/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for the real
(`Real.cos`) and complex (`Complex.cos`) cosine and the real (`Real.cosh`) and complex
(`Complex.cosh`) hyperbolic cosine.
-/

public section


namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

@[simp, norm_cast]
/-
**Polynomial.Chebyshev.complex_ofReal_eval_T** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：complex_ofReal_eval_T : forall (x : Real) n, (((T Real n).eval x : Real) :
 Complex) = (T Complex n).eval (x : Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.algebraMap_eval_T`：algebraMap_eval_T [Algebra R R']
 (x : R) (n : Int) : algebraMap R R' ((T R n).eval x) = (T R' n).eval (algebraMa
p R R' x)
-/
theorem complex_ofReal_eval_T : ∀ (x : ℝ) n, (((T ℝ n).eval x : ℝ) : ℂ) = (T ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_T ℝ ℂ _ _ _

@[simp, norm_cast]
/-
**Polynomial.Chebyshev.complex_ofReal_eval_U** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：complex_ofReal_eval_U : forall (x : Real) n, (((U Real n).eval x : Real) :
 Complex) = (U Complex n).eval (x : Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.algebraMap_eval_U`：algebraMap_eval_U [Algebra R R']
 (x : R) (n : Int) : algebraMap R R' ((U R n).eval x) = (U R' n).eval (algebraMa
p R R' x)
-/
theorem complex_ofReal_eval_U : ∀ (x : ℝ) n, (((U ℝ n).eval x : ℝ) : ℂ) = (U ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_U ℝ ℂ _ _ _

@[simp, norm_cast]
/-
**Polynomial.Chebyshev.complex_ofReal_eval_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：complex_ofReal_eval_C : forall (x : Real) n, (((C Real n).eval x : Real) :
 Complex) = (C Complex n).eval (x : Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.algebraMap_eval_C`：algebraMap_eval_C [Algebra R R']
 (x : R) (n : Int) : algebraMap R R' ((C R n).eval x) = (C R' n).eval (algebraMa
p R R' x)
-/
theorem complex_ofReal_eval_C : ∀ (x : ℝ) n, (((C ℝ n).eval x : ℝ) : ℂ) = (C ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_C ℝ ℂ _ _ _

@[simp, norm_cast]
/-
**Polynomial.Chebyshev.complex_ofReal_eval_S** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：complex_ofReal_eval_S : forall (x : Real) n, (((S Real n).eval x : Real) :
 Complex) = (S Complex n).eval (x : Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.algebraMap_eval_S`：algebraMap_eval_S [Algebra R R']
 (x : R) (n : Int) : algebraMap R R' ((S R n).eval x) = (S R' n).eval (algebraMa
p R R' x)
-/
theorem complex_ofReal_eval_S : ∀ (x : ℝ) n, (((S ℝ n).eval x : ℝ) : ℂ) = (S ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_S ℝ ℂ _ _ _

/-! ### Complex versions -/

section Complex

open Complex

variable (θ : ℂ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.T_complex_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheby
shev`。
形式化陈述：T_complex_cos (n : Int) : (T Complex n).eval (cos θ) = cos (n * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.induct`：∀ (motive : ℤ → Prop),   motive 0 →     mot
ive 1 →       (∀ (n : ℕ), motive (↑n + 1) → motive ↑n → motive (↑n + 2)) →      
   (∀ (n : ℕ), mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.T_zero`：T_zero : T R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Chebyshev.T_one`：T_one : T R 1 = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Chebyshev.T_add_two`：T_add_two : forall n, T R (n + 2) = 2 * 
X * T R (n + 1) - T R n | (k : Nat) => T.eq_3 R k | -(k + 1 : Nat) => by linear_
combination (norm
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用引理 `Polynomial.eval_ofNat`：eval_ofNat (n : Nat) [n.AtLeastTwo] (a : R) : (of
Nat(n) : R[X]).eval a = ofNat(n)
· 使用定理 `Complex.cos_add_cos`：cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2)
 * cos ((x - y) / 2)
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`.
-/
theorem T_complex_cos (n : ℤ) : (T ℂ n).eval (cos θ) = cos (n * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add,
      cos_add_cos]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add',
      cos_add_cos]
    push_cast
    ring_nf

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.U_complex_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheby
shev`。
形式化陈述：U_complex_cos (n : Int) : (U Complex n).eval (cos θ) * sin θ = sin ((n + 1
) * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.induct`：∀ (motive : ℤ → Prop),   motive 0 →     mot
ive 1 →       (∀ (n : ℕ), motive (↑n + 1) → motive ↑n → motive (↑n + 2)) →      
   (∀ (n : ℕ), mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Chebyshev.U_zero`：U_zero : U R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Chebyshev.U_one`：U_one : U R 1 = 2 * X
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用引理 `Polynomial.eval_ofNat`：eval_ofNat (n : Nat) [n.AtLeastTwo] (a : R) : (of
Nat(n) : R[X]).eval a = ofNat(n)
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Complex.sin_two_mul`：sin_two_mul : sin (2 * x) = 2 * sin x * cos x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`.
-/
theorem U_complex_cos (n : ℤ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [one_add_one_eq_two, sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add', sin_add_sin]
    push_cast
    ring_nf

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.C_two_mul_complex_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：C_two_mul_complex_cos (n : Int) : (C Complex n).eval (2 * cos θ) = 2 * cos
 (n * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X`：C_eq_two_mul_T_comp
_half_mul_X [Invertible (2 : R)] (n : Int) : C R n = 2 * (T R n).comp (Polynomia
l.C ⅟2 * X)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.eval_ofNat`：eval_ofNat (n : Nat) [n.AtLeastTwo] (a : R) : (of
Nat(n) : R[X]).eval a = ofNat(n)
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Chebyshev.T_complex_cos`：T_complex_cos (n : Int) : (T Complex
 n).eval (cos θ) = cos (n * θ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomi
al) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`.
-/
theorem C_two_mul_complex_cos (n : ℤ) : (C ℂ n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.S_two_mul_complex_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：S_two_mul_complex_cos (n : Int) : (S Complex n).eval (2 * cos θ) * sin θ =
 sin ((n + 1) * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.S_eq_U_comp_half_mul_X`：S_eq_U_comp_half_mul_X [Inv
ertible (2 : R)] (n : Int) : S R n = (U R n).comp (Polynomial.C ⅟2 * X)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Chebyshev.U_complex_cos`：U_complex_cos (n : Int) : (U Complex
 n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci pol
ynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`.
-/
theorem S_two_mul_complex_cos (n : ℤ) : (S ℂ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.T_complex_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheb
yshev`。
形式化陈述：T_complex_cosh (n : Int) : (T Complex n).eval (cosh θ) = cosh (n * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cos_mul_I`：cos_mul_I : cos (x * I) = cosh x
· 使用定理 `Polynomial.Chebyshev.T_complex_cos`：T_complex_cos (n : Int) : (T Complex
 n).eval (cos θ) = cos (n * θ)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`.
-/
theorem T_complex_cosh (n : ℤ) : (T ℂ n).eval (cosh θ) = cosh (n * θ) := calc
  (T ℂ n).eval (cosh θ)
  _ = (T ℂ n).eval (cos (θ * I))        := by rw [cos_mul_I]
  _ = cos (n * (θ * I))                 := T_complex_cos (θ * I) n
  _ = cos (n * θ * I)                   := by rw [mul_assoc]
  _ = cosh (n * θ)                      := cos_mul_I (n * θ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.U_complex_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheb
yshev`。
形式化陈述：U_complex_cosh (n : Int) : (U Complex n).eval (cosh θ) * sinh θ = sinh ((n
 + 1) * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.cos_mul_I`：cos_mul_I : cos (x * I) = cosh x
· 使用定理 `Complex.sin_mul_I`：sin_mul_I : sin (x * I) = sinh x * I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Chebyshev.U_complex_cos`：U_complex_cos (n : Int) : (U Complex
 n).eval (cos θ) * sin θ = sin ((n + 1) * θ)

--- 原说明 ---
The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`.
-/
theorem U_complex_cosh (n : ℤ) : (U ℂ n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ) := calc
  (U ℂ n).eval (cosh θ) * sinh θ
  _ = (U ℂ n).eval (cos (θ * I)) * sin (θ * I) * (-I)   := by simp [cos_mul_I, sin_mul_I, mul_assoc]
  _ = sin ((n + 1) * (θ * I)) * (-I)                    := by rw [U_complex_cos]
  _ = sin ((n + 1) * θ * I) * (-I)                      := by rw [mul_assoc]
  _ = sinh ((n + 1) * θ)                                := by
    rw [sin_mul_I ((n + 1) * θ), mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one]

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.C_two_mul_complex_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：C_two_mul_complex_cosh (n : Int) : (C Complex n).eval (2 * cosh θ) = 2 * c
osh (n * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X`：C_eq_two_mul_T_comp
_half_mul_X [Invertible (2 : R)] (n : Int) : C R n = 2 * (T R n).comp (Polynomia
l.C ⅟2 * X)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.eval_ofNat`：eval_ofNat (n : Nat) [n.AtLeastTwo] (a : R) : (of
Nat(n) : R[X]).eval a = ofNat(n)
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Chebyshev.T_complex_cosh`：T_complex_cosh (n : Int) : (T Compl
ex n).eval (cosh θ) = cosh (n * θ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomi
al) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`.
-/
theorem C_two_mul_complex_cosh (n : ℤ) : (C ℂ n).eval (2 * cosh θ) = 2 * cosh (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.S_two_mul_complex_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：S_two_mul_complex_cosh (n : Int) : (S Complex n).eval (2 * cosh θ) * sinh 
θ = sinh ((n + 1) * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.S_eq_U_comp_half_mul_X`：S_eq_U_comp_half_mul_X [Inv
ertible (2 : R)] (n : Int) : S R n = (U R n).comp (Polynomial.C ⅟2 * X)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Chebyshev.U_complex_cosh`：U_complex_cosh (n : Int) : (U Compl
ex n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci pol
ynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`.
-/
theorem S_two_mul_complex_cosh (n : ℤ) : (S ℂ n).eval (2 * cosh θ) * sinh θ =
    sinh ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

end Complex

/-! ### Real versions -/

section Real

open Real

variable (θ : ℝ) (n : ℤ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.T_real_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebyshe
v`。
形式化陈述：T_real_cos : (T Real n).eval (cos θ) = cos (n * θ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Chebyshev.T_complex_cos`：T_complex_cos (n : Int) : (T Complex
 n).eval (cos θ) = cos (n * θ)

--- 原说明 ---
The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`.
-/
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := mod_cast T_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.U_real_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebyshe
v`。
形式化陈述：U_real_cos : (U Real n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Polynomial.Chebyshev.U_complex_cos`：U_complex_cos (n : Int) : (U Complex
 n).eval (cos θ) * sin θ = sin ((n + 1) * θ)

--- 原说明 ---
The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`.
-/
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast U_complex_cos θ n

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.C_two_mul_real_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：C_two_mul_real_cos : (C Real n).eval (2 * cos θ) = 2 * cos (n * θ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Chebyshev.C_two_mul_complex_cos`：C_two_mul_complex_cos (n : I
nt) : (C Complex n).eval (2 * cos θ) = 2 * cos (n * θ)

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomi
al) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`.
-/
theorem C_two_mul_real_cos : (C ℝ n).eval (2 * cos θ) = 2 * cos (n * θ) :=
  mod_cast C_two_mul_complex_cos θ n

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.S_two_mul_real_cos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：S_two_mul_real_cos : (S Real n).eval (2 * cos θ) * sin θ = sin ((n + 1) * 
θ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Polynomial.Chebyshev.S_two_mul_complex_cos`：S_two_mul_complex_cos (n : I
nt) : (S Complex n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ)

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci pol
ynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`.
-/
theorem S_two_mul_real_cos : (S ℝ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast S_two_mul_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.T_real_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebysh
ev`。
形式化陈述：T_real_cosh (n : Int) : (T Real n).eval (cosh θ) = cosh (n * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Chebyshev.T_complex_cosh`：T_complex_cosh (n : Int) : (T Compl
ex n).eval (cosh θ) = cosh (n * θ)

--- 原说明 ---
The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`.
-/
theorem T_real_cosh (n : ℤ) : (T ℝ n).eval (cosh θ) = cosh (n * θ) := mod_cast T_complex_cosh θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.U_real_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebysh
ev`。
形式化陈述：U_real_cosh (n : Int) : (U Real n).eval (cosh θ) * sinh θ = sinh ((n + 1) 
* θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Polynomial.Chebyshev.U_complex_cosh`：U_complex_cosh (n : Int) : (U Compl
ex n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ)

--- 原说明 ---
The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`.
-/
theorem U_real_cosh (n : ℤ) : (U ℝ n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ) :=
  mod_cast U_complex_cosh θ n

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`. -/
@[simp]
/-
**Polynomial.Chebyshev.C_two_mul_real_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Chebyshev`。
形式化陈述：C_two_mul_real_cosh (n : Int) : (C Real n).eval (2 * cosh θ) = 2 * cosh (n
 * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Chebyshev.C_two_mul_complex_cosh`：C_two_mul_complex_cosh (n :
 Int) : (C Complex n).eval (2 * cosh θ) = 2 * cosh (n * θ)

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomi
al) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`.
-/
theorem C_two_mul_real_cosh (n : ℤ) : (C ℝ n).eval (2 * cosh θ) = 2 * cosh (n * θ) :=
  mod_cast C_two_mul_complex_cosh θ n

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/-
**Polynomial.Chebyshev.S_two_mul_real_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Chebyshev`。
形式化陈述：S_two_mul_real_cosh (n : Int) : (S Real n).eval (2 * cosh θ) * sinh θ = si
nh ((n + 1) * θ)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Polynomial.Chebyshev.S_two_mul_complex_cosh`：S_two_mul_complex_cosh (n :
 Int) : (S Complex n).eval (2 * cosh θ) * sinh θ = sinh ((n + 1) * θ)

--- 原说明 ---
The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci pol
ynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`.
-/
theorem S_two_mul_real_cosh (n : ℤ) : (S ℝ n).eval (2 * cosh θ) * sinh θ = sinh ((n + 1) * θ) :=
  mod_cast S_two_mul_complex_cosh θ n

end Real

end Polynomial.Chebyshev

