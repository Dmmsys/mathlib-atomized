/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylorCoeffWithin`: the Taylor coefficient using `iteratedDerivWithin`
* `taylorWithin`: the Taylor polynomial using `iteratedDerivWithin`

## Main statements

* `taylor_tendsto`: Taylor's theorem as a limit
* `taylor_isLittleO`: Taylor's theorem using little-o notation
* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector-valued functions with a
  polynomial bound on the remainder
* `taylor_integral_remainder_of_absolutelyContinuous`,
  `taylor_integral_remainder`: Taylor's theorem with the integral form of the
  remainder

## TODO

* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/

@[expose] public section


open scoped Interval Topology Nat

open Set

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`th coefficient of the Taylor polynomial. -/
/-
**taylorCoeffWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：taylorCoeffWithin (f : Real -> E) (k : Nat) (s : Set Real) (x₀ : Real) : E
参数：f : Real -> E；k : Nat；s : Set Real；x₀ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`th coefficient of the Taylor polynomial.
-/
noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀

/-- The Taylor polynomial with derivatives inside of a set `s`.

The Taylor polynomial is given by
$$∑_{k=0}^n \frac{(x - x₀)^k}{k!} f^{(k)}(x₀),$$
where $f^{(k)}(x₀)$ denotes the iterated derivative in the set `s`. -/
/-
**taylorWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：taylorWithin (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real) : Polyno
mialModule Real E
参数：f : Real -> E；n : Nat；s : Set Real；x₀ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Taylor polynomial with derivatives inside of a set `s`.

The Taylor polynomial is given by
$$∑_{k=0}^n \frac{(x - x₀)^k}{k!} f^{(k)}(x₀),$$
where $f^{(k)}(x₀)$ denotes the iterated derivative in the set `s`.
-/
noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))

/-- The Taylor polynomial with derivatives inside of a set `s` considered as a function `ℝ → E` -/
/-
**taylorWithinEval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：taylorWithinEval (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real) : 
E
参数：f : Real -> E；n : Nat；s : Set Real；x₀ x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Taylor polynomial with derivatives inside of a set `s` considered as a funct
ion `ℝ → E`
-/
noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)
/-
**taylorWithin_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylorWithin_succ (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real) : t
aylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ + PolynomialModule.comp (Poly
nomial.X - Polynomial.C x₀) (PolynomialModule.single Real (n + 1) (taylorCoeffWi
thin f (n + 1) s x₀))
参数：f : Real -> E；n : Nat；s : Set Real；x₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
-/
theorem taylorWithin_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ +
      PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) := by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]

@[simp]
/-
**taylorWithinEval_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylorWithinEval_succ (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Rea
l) : taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x + (((n + 1 
: Real) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀
参数：f : Real -> E；n : Nat；s : Set Real；x₀ x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `taylorWithin_succ`：taylorWithin_succ (f : Real -> E) (n : Nat) (s : Set 
Real) (x₀ : Real) : taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ + Polyno
mialMod…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `PolynomialModule.comp_eval`：comp_eval (p : R[X]) (q : PolynomialModule R
 M) (r : R) : eval r (comp p q) = eval (p.eval r) q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem taylorWithinEval_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x +
      (((n + 1 : ℝ) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀ := by
  simp_rw [taylorWithinEval, taylorWithin_succ, map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul, mul_comm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_inv_rev]

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp]
/-
**taylor_within_zero_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_within_zero_eval (f : Real -> E) (s : Set Real) (x₀ x : Real) : tay
lorWithinEval f 0 s x₀ x = f x₀
参数：f : Real -> E；s : Set Real；x₀ x : Real。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PolynomialModule.comp_apply`：∀ {R : Type u_2} {M : Type u_3} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Polynomia
l R) (x : Polynom…
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `PolynomialModule.eval_lsingle`：eval_lsingle (r : R) (i : Nat) (m : M) : 
eval r (lsingle R i m) = r ^ i • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Taylor polynomial of order zero evaluates to `f x`.
-/
theorem taylor_within_zero_eval (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 0 s x₀ x = f x₀ := by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp]
/-
**taylorWithinEval_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylorWithinEval_self (f : Real -> E) (n : Nat) (s : Set Real) (x₀ : Real)
 : taylorWithinEval f n s x₀ x₀ = f x₀
参数：f : Real -> E；n : Nat；s : Set Real；x₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `taylor_within_zero_eval`：taylor_within_zero_eval (f : Real -> E) (s : Se
t Real) (x₀ x : Real) : taylorWithinEval f 0 s x₀ x = f x₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `taylorWithinEval_succ`：taylorWithinEval_succ (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ x : Real) : taylorWithinEval f (n + 1) s x₀ x = taylorWithinEv
al f n s x₀…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Evaluating the Taylor polynomial at `x = x₀` yields `f x`.
-/
theorem taylorWithinEval_self (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithinEval f n s x₀ x₀ = f x₀ := by
  induction n with
  | zero => exact taylor_within_zero_eval _ _ _ _
  | succ k hk => simp [hk]
/-
**taylor_within_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_within_apply (f : Real -> E) (n : Nat) (s : Set Real) (x₀ x : Real)
 : taylorWithinEval f n s x₀ x = ∑ k in Finset.range (n + 1), ((k ! : Real)⁻¹ * 
(x - x₀) ^ k) • iteratedDerivWithin k f s x₀
参数：f : Real -> E；n : Nat；s : Set Real；x₀ x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `taylor_within_zero_eval`：taylor_within_zero_eval (f : Real -> E) (s : Se
t Real) (x₀ x : Real) : taylorWithinEval f 0 s x₀ x = f x₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `taylorWithinEval_succ`：taylorWithinEval_succ (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ x : Real) : taylorWithinEval f (n + 1) s x₀ x = taylorWithinEv
al f n s x₀…
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
theorem taylor_within_apply (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ := by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [taylorWithinEval_succ, Finset.sum_range_succ, hk]
    simp [Nat.factorial]

/-- If `f` is `n` times continuous differentiable on a set `s`, then the Taylor polynomial
  `taylorWithinEval f n s x₀ x` is continuous in `x₀`. -/
/-
**continuousOn_taylorWithinEval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_taylorWithinEval {f : Real -> E} {x : Real} {n : Nat} {s : Se
t Real} (hs : UniqueDiffOn Real s) (hf : ContDiffOn Real n f s) : ContinuousOn (
fun t => taylorWithinEval f n s t x) s
参数：hs : UniqueDiffOn Real s；hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `taylor_within_apply`：taylor_within_apply (f : Real -> E) (n : Nat) (s : 
Set Real) (x₀ x : Real) : taylorWithinEval f n s x₀ x = ∑ k in Finset.range (n +
 1), ((k …
· 使用定理 `continuousOn_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMono
id M] [Conti…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.pow`：ContinuousOn.pow {f : X -> M} {s : Set X} (hf : Contin
uousOn f s) (n : Nat) : ContinuousOn (f ^ n) s
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `contDiffOn_nat_iff_continuousOn_differentiableOn_deriv`：contDiffOn_nat_i
ff_continuousOn_differentiableOn_deriv {n : Nat} (hs : UniqueDiffOn 𝕜 s) : ContD
iffOn 𝕜 n f s ↔ (forall m : Nat, m <= n -> C…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n

--- 原说明 ---
If `f` is `n` times continuous differentiable on a set `s`, then the Taylor poly
nomial
  `taylorWithinEval f n s x₀ x` is continuous in `x₀`.
-/
theorem continuousOn_taylorWithinEval {f : ℝ → E} {x : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ n f s) :
    ContinuousOn (fun t => taylorWithinEval f n s t x) s := by
  simp_rw [taylor_within_apply]
  refine continuousOn_finsetSum (Finset.range (n + 1)) fun i hi => ?_
  refine (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).smul ?_
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs] at hf
  simp only [Finset.mem_range] at hi
  refine hf.1 i ?_
  simp only [Nat.lt_succ_iff.mp hi]

/-- Helper lemma for calculating the derivative of the monomial that appears in Taylor
expansions. -/
/-
**monomial_has_deriv_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monomial_has_deriv_aux (t x : Real) (n : Nat) : HasDerivAt (fun y => (x - 
y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t
参数：t x : Real；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.pow`：HasDerivAt.pow (h : HasDerivAt f f' x) (n : Nat) : HasDe
rivAt (f ^ n) (n * f x ^ (n - 1) * f') x
· 使用定理 `HasDerivAt.add_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x

--- 原说明 ---
Helper lemma for calculating the derivative of the monomial that appears in Tayl
or
expansions.
-/
theorem monomial_has_deriv_aux (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t := by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ← mul_assoc]
  convert! ((hasDerivAt_id t).neg.add_const x).pow (n + 1)
  simp only [Nat.cast_add, Nat.cast_one]
/-
**hasDerivWithinAt_taylor_coeff_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_taylor_coeff_within {f : Real -> E} {x y : Real} {k : Nat
} {s t : Set Real} (ht : UniqueDiffWithinAt Real t y) (hs : s in 𝓝[t] y) (hf : D
ifferentiableWithinAt Real (iteratedDerivWithin (k + 1) f s) s y) : HasDerivWith
inAt (fun z => (((k + 1 : Real) * k !)⁻¹ * (x - z) ^ (k + 1)) • iteratedDerivWit
hin (k + 1) f s z) ((((k + 1 : Real) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDer
ivWithin (k + 2) f s y - ((k ! : Real)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k
 + 1) f s y) t y
参数：ht : UniqueDiffWithinAt Real t y；hs : s in 𝓝[t] y；hf : DifferentiableWithinAt
 Real (iteratedDerivWithin (k + 1) f s) s y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `derivWithin_of_mem_nhdsWithin`：derivWithin_of_mem_nhdsWithin (st : t in 
𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f t x) : d
erivWithin f s x = …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`：DifferentiableWithinAt.mo
no_of_mem_nhdsWithin (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s i
n 𝓝[t] x) : DifferentiableWithinAt …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
（共 118 条，此处仅展示前 30 条）
-/
theorem hasDerivWithinAt_taylor_coeff_within {f : ℝ → E} {x y : ℝ} {k : ℕ} {s t : Set ℝ}
    (ht : UniqueDiffWithinAt ℝ t y) (hs : s ∈ 𝓝[t] y)
    (hf : DifferentiableWithinAt ℝ (iteratedDerivWithin (k + 1) f s) s y) :
    HasDerivWithinAt
      (fun z => (((k + 1 : ℝ) * k !)⁻¹ * (x - z) ^ (k + 1)) • iteratedDerivWithin (k + 1) f s z)
      ((((k + 1 : ℝ) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDerivWithin (k + 2) f s y -
        ((k ! : ℝ)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k + 1) f s y) t y := by
  replace hf :
    HasDerivWithinAt (iteratedDerivWithin (k + 1) f s) (iteratedDerivWithin (k + 2) f s y) t y := by
    convert (hf.mono_of_mem_nhdsWithin hs).hasDerivWithinAt
    rw [iteratedDerivWithin_succ]
    exact (derivWithin_of_mem_nhdsWithin hs ht hf).symm
  have : HasDerivWithinAt (fun t => ((k + 1 : ℝ) * k !)⁻¹ * (x - t) ^ (k + 1))
      (-((k ! : ℝ)⁻¹ * (x - y) ^ k)) t y := by
    -- Commuting the factors:
    have : -((k ! : ℝ)⁻¹ * (x - y) ^ k) = ((k + 1 : ℝ) * k !)⁻¹ * (-(k + 1) * (x - y) ^ k) := by
      field
    rw [this]
    exact (monomial_has_deriv_aux y x _).hasDerivWithinAt.const_mul _
  convert! this.smul hf using 1
  field_simp
  module

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for arbitrary sets -/
/-
**hasDerivWithinAt_taylorWithinEval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_taylorWithinEval {f : Real -> E} {x y : Real} {n : Nat} {
s s' : Set Real} (hs_unique : UniqueDiffOn Real s) (hs' : s' in 𝓝[s] y) (hy : y 
in s') (h : s' subseteq s) (hf : ContDiffOn Real n f s) (hf' : DifferentiableWit
hinAt Real (iteratedDerivWithin n f s) s y) : HasDerivWithinAt (fun t => taylorW
ithinEval f n s t x) (((n ! : Real)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 
1) f s y) s' y
参数：hs_unique : UniqueDiffOn Real s；hs' : s' in 𝓝[s] y；hy : y in s'；h : s' subset
eq s；hf : ContDiffOn Real n f s；hf' : DifferentiableWithinAt Real (iteratedDeriv
Within n f s) s y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono_nhds`：UniqueDiffWithinAt.mono_nhds (h : UniqueDi
ffWithinAt 𝕜 s x) (st : 𝓝[s] x <= 𝓝[t] x) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `taylor_within_zero_eval`：taylor_within_zero_eval (f : Real -> E) (s : Se
t Real) (x₀ x : Real) : taylorWithinEval f 0 s x₀ x = f x₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iteratedDerivWithin_one`：iteratedDerivWithin_one : iteratedDerivWithin 1
 f s = derivWithin f s
· 使用定理 `HasDerivWithinAt.mono`：HasDerivWithinAt.mono (h : HasDerivWithinAt f f' 
t x) (hst : s subseteq t) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `taylorWithinEval_succ`：taylorWithinEval_succ (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ x : Real) : taylorWithinEval f (n + 1) s x₀ x = taylorWithinEv
al f n s x₀…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for arbitrary sets
-/
theorem hasDerivWithinAt_taylorWithinEval {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : Set ℝ}
    (hs_unique : UniqueDiffOn ℝ s) (hs' : s' ∈ 𝓝[s] y)
    (hy : y ∈ s') (h : s' ⊆ s) (hf : ContDiffOn ℝ n f s)
    (hf' : DifferentiableWithinAt ℝ (iteratedDerivWithin n f s) s y) :
    HasDerivWithinAt (fun t => taylorWithinEval f n s t x)
      (((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f s y) s' y := by
  have hs'_unique : UniqueDiffWithinAt ℝ s' y :=
    UniqueDiffWithinAt.mono_nhds (hs_unique _ (h hy)) (nhdsWithin_le_iff.mpr hs')
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    simp only [iteratedDerivWithin_zero] at hf'
    rw [iteratedDerivWithin_one]
    exact hf'.hasDerivWithinAt.mono h
  | succ k hk =>
    simp_rw [Nat.add_succ, taylorWithinEval_succ]
    simp only [add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have coe_lt_succ : (k : WithTop ℕ) < k.succ := Nat.cast_lt.2 k.lt_succ_self
    have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k f s) s' :=
      (hf.differentiableOn_iteratedDerivWithin (mod_cast coe_lt_succ) hs_unique).mono h
    specialize hk hf.of_succ ((hdiff y hy).mono_of_mem_nhdsWithin hs')
    convert!
      hk.add
        (hasDerivWithinAt_taylor_coeff_within hs'_unique (nhdsWithin_mono _ h self_mem_nhdsWithin)
          hf') using 1
    exact (add_sub_cancel _ _).symm

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for open intervals -/
/-
**taylorWithinEval_hasDerivAt_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylorWithinEval_hasDerivAt_Ioo {f : Real -> E} {a b t : Real} (x : Real) 
{n : Nat} (hx : a < b) (ht : t in Ioo a b) (hf : ContDiffOn Real n f (Icc a b)) 
(hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) : Ha
sDerivAt (fun y => taylorWithinEval f n (Icc a b) y x) (((n ! : Real)⁻¹ * (x - t
) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t
参数：x : Real；hx : a < b；ht : t in Ioo a b；hf : ContDiffOn Real n f (Icc a b)；hf' 
: DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Ioo a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `hasDerivWithinAt_taylorWithinEval`：hasDerivWithinAt_taylorWithinEval {f 
: Real -> E} {x y : Real} {n : Nat} {s s' : Set Real} (hs_unique : UniqueDiffOn 
Real s) (hs' : s' in 𝓝[…
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`：DifferentiableWithinAt.mo
no_of_mem_nhdsWithin (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s i
n 𝓝[t] x) : DifferentiableWithinAt …

--- 原说明 ---
Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for open intervals
-/
theorem taylorWithinEval_hasDerivAt_Ioo {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ} (hx : a < b)
    (ht : t ∈ Ioo a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    HasDerivAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t :=
  have h_nhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b ∈ 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx) h_nhds' ht
    Ioo_subset_Icc_self hf <| (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for closed intervals -/
/-
**hasDerivWithinAt_taylorWithinEval_at_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_taylorWithinEval_at_Icc {f : Real -> E} {a b t : Real} (x
 : Real) {n : Nat} (hx : a < b) (ht : t in Icc a b) (hf : ContDiffOn Real n f (I
cc a b)) (hf' : DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Icc a
 b)) : HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x) (((n ! : R
eal)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t
参数：x : Real；hx : a < b；ht : t in Icc a b；hf : ContDiffOn Real n f (Icc a b)；hf' 
: DifferentiableOn Real (iteratedDerivWithin n f (Icc a b)) (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivWithinAt_taylorWithinEval`：hasDerivWithinAt_taylorWithinEval {f 
: Real -> E} {x y : Real} {n : Nat} {s s' : Set Real} (hs_unique : UniqueDiffOn 
Real s) (hs' : s' in 𝓝[…
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b

--- 原说明 ---
Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for closed intervals
-/
theorem hasDerivWithinAt_taylorWithinEval_at_Icc {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
    (hx : a < b) (ht : t ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
  hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)

/-- Calculate the derivative of the Taylor polynomial with respect to `x`. -/
/-
**hasDerivAt_taylorWithinEval_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_taylorWithinEval_succ {x₀ x : Real} {s : Set Real} (f : Real ->
 E) (n : Nat) : HasDerivAt (taylorWithinEval f (n + 1) s x₀) (taylorWithinEval (
derivWithin f s) n s x₀ x) x
参数：f : Real -> E；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `taylor_within_apply`：taylor_within_apply (f : Real -> E) (n : Nat) (s : 
Set Real) (x₀ x : Real) : taylorWithinEval f n s x₀ x = ∑ k in Finset.range (n +
 1), ((k …
· 使用定理 `HasDerivAt.smul_const`：HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f
 : F) : HasDerivAt (fun y => c y • f) (c' • f) x
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `HasDerivAt.pow`：HasDerivAt.pow (h : HasDerivAt f f' x) (n : Nat) : HasDe
rivAt (f ^ n) (n * f x ^ (n - 1) * f') x
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `HasDerivAt.congr_deriv`：HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (
h' : f' = g') : HasDerivAt f g' x
· 使用定理 `HasDerivAt.fun_sum`：HasDerivAt.fun_sum (h : forall i in u, HasDerivAt (A
 i) (A' i) x) : HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedDerivWithin_succ'`：iteratedDerivWithin_succ' : iteratedDerivWith
in (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
Calculate the derivative of the Taylor polynomial with respect to `x`.
-/
theorem hasDerivAt_taylorWithinEval_succ {x₀ x : ℝ} {s : Set ℝ} (f : ℝ → E) (n : ℕ) :
    HasDerivAt (taylorWithinEval f (n + 1) s x₀)
      (taylorWithinEval (derivWithin f s) n s x₀ x) x := by
  change HasDerivAt (fun x ↦ taylorWithinEval f _ s x₀ x) _ _
  simp_rw [taylor_within_apply]
  have : ∀ (i : ℕ) {c : ℝ} {c' : E},
      HasDerivAt (fun x ↦ (c * (x - x₀) ^ i) • c') ((c * (i * (x - x₀) ^ (i - 1) * 1)) • c') x :=
    fun _ _ ↦ hasDerivAt_id _ |>.sub_const _ |>.pow _ |>.const_mul _ |>.smul_const _
  apply HasDerivAt.fun_sum (fun i _ => this i) |>.congr_deriv
  rw [Finset.sum_range_succ', Nat.cast_zero, zero_mul, zero_mul, mul_zero, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [← iteratedDerivWithin_succ']
  congr 1
  simp [field, Nat.factorial_succ]

/-- **Taylor's theorem** using little-o notation. -/
/-
**taylor_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_isLittleO {f : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real} (hs 
: Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) : (fun x => f x -
 taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x => (x - x₀) ^ n
参数：hs : Convex Real s；hx₀s : x₀ in s；hf : ContDiffOn Real n f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `taylor_within_zero_eval`：taylor_within_zero_eval (f : Real -> E) (s : Se
t Real) (x₀ x : Real) : taylorWithinEval f 0 s x₀ x = f x₀
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用引理 `Set.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in s)
 : s = {a} ∨ s.Nontrivial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用定理 `taylorWithinEval_succ`：taylorWithinEval_succ (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ x : Real) : taylorWithinEval f (n + 1) s x₀ x = taylorWithinEv
al f n s x₀…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `uniqueDiffOn_convex`：uniqueDiffOn_convex (conv : Convex Real s) (hs : (i
nterior s).Nonempty) : UniqueDiffOn Real s
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
**Taylor's theorem** using little-o notation.
-/
theorem taylor_isLittleO {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    (fun x ↦ f x - taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ n := by
  induction n generalizing f with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s
  | succ n h =>
    rcases s.eq_singleton_or_nontrivial hx₀s with rfl | hs'
    · simp
    replace hs' := uniqueDiffOn_convex hs (hs.nontrivial_iff_nonempty_interior.1 hs')
    simp only [Nat.cast_add, Nat.cast_one] at hf
    convert!
      Convex.isLittleO_pow_succ_real hs hx₀s ?_ (h (hf.derivWithin hs' le_rfl)) (f := fun x ↦
        f x - taylorWithinEval f (n + 1) s x₀ x) using 1
    · simp
    · intro x hx
      refine HasDerivWithinAt.sub ?_ (hasDerivAt_taylorWithinEval_succ f n).hasDerivWithinAt
      exact (hf.differentiableOn (by simp) _ hx).hasDerivWithinAt
/-
**taylor_isLittleO_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_isLittleO_univ {f : Real -> E} {x₀ : Real} {n : Nat} (hf : ContDiff
 Real n f) : (fun x => f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x => (
x - x₀) ^ n
参数：hf : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `taylor_isLittleO`：taylor_isLittleO {f : Real -> E} {x₀ : Real} {n : Nat}
 {s : Set Real} (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f 
s) : (…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
-/
theorem taylor_isLittleO_univ {f : ℝ → E} {x₀ : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    (fun x ↦ f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x ↦ (x - x₀) ^ n := by
  simpa using taylor_isLittleO convex_univ (mem_univ x₀) hf.contDiffOn

/-- **Taylor's theorem** as a limit. -/
/-
**taylor_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_tendsto {f : Real -> E} {x₀ : Real} {n : Nat} {s : Set Real} (hs : 
Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) : Filter.Tendsto (f
un x => ((x - x₀) ^ n)⁻¹ • (f x - taylorWithinEval f n s x₀ x)) (𝓝[s] x₀) (𝓝 0)
参数：hs : Convex Real s；hx₀s : x₀ in s；hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.norm_norm`：∀ {α : Type u_1} {E' : Type u_6} {F' : 
Type u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'
]   {f' : α → E'} {g'…
· 使用定理 `taylor_isLittleO`：taylor_isLittleO {f : Real -> E} {x₀ : Real} {n : Nat}
 {s : Set Real} (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f 
s) : (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Asymptotics.isLittleO_iff_tendsto`：isLittleO_iff_tendsto {f g : α -> 𝕜} 
(hgf : forall x, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x / g x) 
l (𝓝 0)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
**Taylor's theorem** as a limit.
-/
theorem taylor_tendsto {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    Filter.Tendsto (fun x ↦ ((x - x₀) ^ n)⁻¹ • (f x - taylorWithinEval f n s x₀ x))
      (𝓝[s] x₀) (𝓝 0) := by
  have h_isLittleO := (taylor_isLittleO hs hx₀s hf).norm_norm
  rw [Asymptotics.isLittleO_iff_tendsto] at h_isLittleO
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_smul, div_eq_inv_mul] using h_isLittleO
  · simp only [norm_pow, Real.norm_eq_abs, pow_eq_zero_iff', abs_eq_zero, ne_eq, norm_eq_zero,
      and_imp]
    intro x hx
    rw [sub_eq_zero] at hx
    simp [hx]

/-- **Taylor's theorem** as a limit. -/
/-
**Real.taylor_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.taylor_tendsto {f : Real -> Real} {x₀ : Real} {n : Nat} {s : Set Real
} (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) : Filter.Te
ndsto (fun x => (f x - taylorWithinEval f n s x₀ x) / (x - x₀) ^ n) (𝓝[s] x₀) (𝓝
 0)
参数：hs : Convex Real s；hx₀s : x₀ in s；hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `taylor_tendsto`：taylor_tendsto {f : Real -> E} {x₀ : Real} {n : Nat} {s 
: Set Real} (hs : Convex Real s) (hx₀s : x₀ in s) (hf : ContDiffOn Real n f s) :
 Fil…

--- 原说明 ---
**Taylor's theorem** as a limit.
-/
theorem Real.taylor_tendsto {f : ℝ → ℝ} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    Filter.Tendsto (fun x ↦ (f x - taylorWithinEval f n s x₀ x) / (x - x₀) ^ n)
      (𝓝[s] x₀) (𝓝 0) := by
  convert _root_.taylor_tendsto hs hx₀s hf with x
  simp [div_eq_inv_mul]


/-! ### Taylor's theorem with mean value type remainder estimate -/


/-- **Taylor's theorem** with the general mean value form of the remainder.

We assume that `f` is `n`-times continuously differentiable in the closed set `uIcc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`, and `g` is a differentiable function on
`uIoo x₀ x` and continuous on `uIcc x₀ x`. Then there exists an `x' ∈ uIoo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{(x - x')^n}{n!} \frac{g(x) - g(x₀)}{g' x'},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$. -/
/-
**taylor_mean_remainder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_mean_remainder {f : Real -> Real} {g g' : Real -> Real} {x x₀ : Rea
l} {n : Nat} (hx : x₀ != x) (hf : ContDiffOn Real n f (uIcc x₀ x)) (hf' : Differ
entiableOn Real (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) (gcont : Cont
inuousOn g (uIcc x₀ x)) (gdiff : forall x_1 : Real, x_1 in uIoo x₀ x -> HasDeriv
At g (g' x_1) x_1) (g'_ne : forall x_1 : Real, x_1 in uIoo x₀ x -> g' x_1 != 0) 
: exists x' in uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = ((x - x'
) ^ n / n ! * (g x - g x₀)
参数：hx : x₀ != x；hf : ContDiffOn Real n f (uIcc x₀ x)；hf' : DifferentiableOn Real
 (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)；gcont : ContinuousOn g (uIcc 
x₀ x)；gdiff : forall x_1 : Real, x_1 in uIoo x₀ x -> HasDerivAt g (g' x_1) x_1；g
'_ne : forall x_1 : Real, x_1 in uIoo x₀ x -> g' x_1 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `exists_ratio_hasDerivAt_eq_ratio_slope`：exists_ratio_hasDerivAt_eq_ratio
_slope : exists c in Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c
· 使用定理 `continuousOn_taylorWithinEval`：continuousOn_taylorWithinEval {f : Real -
> E} {x : Real} {n : Nat} {s : Set Real} (hs : UniqueDiffOn Real s) (hf : ContDi
ffOn Real n f s) : …
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `taylorWithinEval_hasDerivAt_Ioo`：taylorWithinEval_hasDerivAt_Ioo {f : Re
al -> E} {a b t : Real} (x : Real) {n : Nat} (hx : a < b) (ht : t in Ioo a b) (h
f : ContDiffOn Real n…

--- 原说明 ---
**Taylor's theorem** with the general mean value form of the remainder.

We assume that `f` is `n`-times continuously differentiable in the closed set `u
Icc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`, and `g` is a differentia
ble function on
`uIoo x₀ x` and continuous on `uIcc x₀ x`. Then there exists an `x' ∈ uIoo x₀ x`
 such that
$$f(x) - (P_n f)(x₀, x) = \frac{(x - x')^n}{n!} \frac{g(x) - g(x₀)}{g' x'},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$.
-/
theorem taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x))
    (gcont : ContinuousOn g (uIcc x₀ x))
    (gdiff : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → HasDerivAt g (g' x_1) x_1)
    (g'_ne : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → g' x_1 ≠ 0) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = ((x - x') ^ n / n ! *
      (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' := by
  have hx₁ : min x₀ x < max x₀ x := by grind
  -- We apply the mean value theorem
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (uIcc x₀ x) t x)
      (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t) hx₁
      (continuousOn_taylorWithinEval (uniqueDiffOn_Icc hx₁) hf)
      (fun _ hy => taylorWithinEval_hasDerivAt_Ioo x hx₁ hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩
  use y, hy
  -- The rest is simplifications and trivial calculations
  grind [uIoo, smul_eq_mul, taylorWithinEval_self]

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- **Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n`-times continuously differentiable in the closed set `uIcc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`. Then there exists an `x' ∈ uIoo x₀ x` such
that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
/-
**taylor_mean_remainder_lagrange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_mean_remainder_lagrange {f : Real -> Real} {x x₀ : Real} {n : Nat} 
(hx : x₀ != x) (hf : ContDiffOn Real n f (uIcc x₀ x)) (hf' : DifferentiableOn Re
al (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) : exists x' in uIoo x₀ x, 
f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = iteratedDerivWithin (n + 1) f (uIc
c x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)!
参数：hx : x₀ != x；hf : ContDiffOn Real n f (uIcc x₀ x)；hf' : DifferentiableOn Real
 (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Nat.cast_add_one_ne_zero`：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) !
= 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `taylor_mean_remainder`：taylor_mean_remainder {f : Real -> Real} {g g' : 
Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x) (hf : ContDiffOn Real n f (
uIcc x₀ x))…
· 使用定理 `monomial_has_deriv_aux`：monomial_has_deriv_aux (t x : Real) (n : Nat) : 
HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
**Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n`-times continuously differentiable in the closed set `u
Icc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`. Then there exists an `x'
 ∈ uIoo x₀ x` such
that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the
 $n+1$-th iterated
derivative.
-/
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have gcont : ContinuousOn (fun t : ℝ => (x - t) ^ (n + 1)) (uIcc x₀ x) := by fun_prop
  have xy_ne : ∀ y : ℝ, y ∈ uIoo x₀ x → (x - y) ^ n ≠ 0 := by grind [uIoo, pow_ne_zero]
  have hg' : ∀ y : ℝ, y ∈ uIoo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 := fun y hy =>
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)) (xy_ne y hy)
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder hx hf hf' gcont (fun y _ => monomial_has_deriv_aux y x _) hg' with
    ⟨y, hy, h⟩
  use y, hy
  simp only [sub_self, zero_pow, Ne, Nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h
  rw [h, neg_div, ← div_neg, neg_mul, neg_neg]
  simp [field, xy_ne y hy, Nat.factorial]

/-- A corollary of Taylor's theorem with the Lagrange form of the remainder. -/
/-
**taylor_mean_remainder_lagrange_iteratedDeriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：taylor_mean_remainder_lagrange_iteratedDeriv {f : Real -> Real} {x x₀ : Re
al} {n : Nat} (hx : x₀ != x) (hf : ContDiffOn Real (n + 1) f (uIcc x₀ x)) : exis
ts x' in uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = iteratedDeriv 
(n + 1) f x' * (x - x₀) ^ (n + 1) / (n + 1)!
参数：hx : x₀ != x；hf : ContDiffOn Real (n + 1) f (uIcc x₀ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffOn_uIcc`：uniqueDiffOn_uIcc {a b : Real} (hab : a != b) : Uniqu
eDiffOn Real (uIcc a b)
· 使用定理 `ContDiffOn.differentiableOn_iteratedDerivWithin`：ContDiffOn.differentiab
leOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m
 < n) (hs : UniqueDiffOn 𝕜 s) : Diffe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `taylor_mean_remainder_lagrange`：taylor_mean_remainder_lagrange {f : Real
 -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x) (hf : ContDiffOn Real n f (uIcc
 x₀ x)) (hf' : Diffe…
· 使用定理 `ContDiffOn.of_succ`：ContDiffOn.of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : 
ContDiffOn 𝕜 n f s
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `iteratedDeriv_eq_iteratedFDeriv`：iteratedDeriv_eq_iteratedFDeriv : itera
tedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1
· 使用定理 `iteratedDerivWithin_eq_iteratedFDerivWithin`：iteratedDerivWithin_eq_iter
atedFDerivWithin : iteratedDerivWithin n f s x = (iteratedFDerivWithin 𝕜 n f s x
 : (Fin n -> 𝕜) -> F) fun _ : Fin…
· 使用定理 `iteratedFDerivWithin_eq_iteratedFDeriv`：iteratedFDerivWithin_eq_iterated
FDeriv {n : Nat} (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) 
: iteratedFDerivWithin 𝕜 n f…
· 使用定理 `ContDiffOn.contDiffAt`：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (h
x : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Icc_mem_nhds_iff`：Icc_mem_nhds_iff [NoMinOrder α] [NoMaxOrder α] {a b x 
: α} : Icc a b in 𝓝 x ↔ x in Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A corollary of Taylor's theorem with the Lagrange form of the remainder.
-/
lemma taylor_mean_remainder_lagrange_iteratedDeriv {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc hx
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIcc x₀ x) := by
    refine hf.differentiableOn_iteratedDerivWithin ?_ hu
    norm_cast
    simp
  obtain ⟨x', h1, h2⟩ := taylor_mean_remainder_lagrange hx hf.of_succ (hd.mono Ioo_subset_Icc_self)
  use x', h1
  rw [h2, iteratedDeriv_eq_iteratedFDeriv, iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv hu _ ⟨le_of_lt h1.1, le_of_lt h1.2⟩]
  exact hf.contDiffAt (Icc_mem_nhds_iff.2 h1)

/-- **Taylor's theorem** with the Cauchy form of the remainder.

We assume that `f` is `n`-times continuously differentiable on the closed set `uIcc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`. Then there exists an `x' ∈ uIoo x₀ x` such
that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x')^n (x-x₀)}{n!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
/-
**taylor_mean_remainder_cauchy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_mean_remainder_cauchy {f : Real -> Real} {x x₀ : Real} {n : Nat} (h
x : x₀ != x) (hf : ContDiffOn Real n f (uIcc x₀ x)) (hf' : DifferentiableOn Real
 (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) : exists x' in uIoo x₀ x, f 
x - taylorWithinEval f n (uIcc x₀ x) x₀ x = iteratedDerivWithin (n + 1) f (uIcc 
x₀ x) x' * (x - x') ^ n / n ! * (x - x₀)
参数：hx : x₀ != x；hf : ContDiffOn Real n f (uIcc x₀ x)；hf' : DifferentiableOn Real
 (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `taylor_mean_remainder`：taylor_mean_remainder {f : Real -> Real} {g g' : 
Real -> Real} {x x₀ : Real} {n : Nat} (hx : x₀ != x) (hf : ContDiffOn Real n f (
uIcc x₀ x))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
**Taylor's theorem** with the Cauchy form of the remainder.

We assume that `f` is `n`-times continuously differentiable on the closed set `u
Icc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`. Then there exists an `x'
 ∈ uIoo x₀ x` such
that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x')^n (x-x₀)}{n!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the
 $n+1$-th iterated
derivative.
-/
theorem taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := by
  have gcont : ContinuousOn id (uIcc x₀ x) := by fun_prop
  have gdiff : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → HasDerivAt id ((fun _ : ℝ => (1 : ℝ)) x_1) x_1 :=
    fun _ _ => hasDerivAt_id _
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff fun _ _ => by simp with ⟨y, hy, h⟩
  use y, hy
  rw [h]
  simp [field]

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
The difference of `f` and its `n`-th Taylor polynomial can be estimated by
`C * (x - a)^(n+1) / n!` where `C` is a bound for the `n+1`-th iterated derivative of `f`. -/
/-
**taylor_mean_remainder_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_mean_remainder_bound {f : Real -> E} {a b C x : Real} {n : Nat} (ha
b : a <= b) (hf : ContDiffOn Real (n + 1) f (Icc a b)) (hx : x in Icc a b) (hC :
 forall y in Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ <= C) : ‖f x -
 taylorWithinEval f n (Icc a b) a x‖ <= C * (x - a) ^ (n + 1) / n !
参数：hab : a <= b；hf : ContDiffOn Real (n + 1) f (Icc a b)；hx : x in Icc a b；hC : 
forall y in Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `ContDiffOn.differentiableOn_iteratedDerivWithin`：ContDiffOn.differentiab
leOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m
 < n) (hs : UniqueDiffOn 𝕜 s) : Diffe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
（共 118 条，此处仅展示前 30 条）

--- 原说明 ---
**Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set 
`Icc a b`.
The difference of `f` and its `n`-th Taylor polynomial can be estimated by
`C * (x - a)^(n+1) / n!` where `C` is a bound for the `n+1`-th iterated derivati
ve of `f`.
-/
theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n ! := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  -- The nth iterated derivative is differentiable
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self)
      (uniqueDiffOn_Icc h)
  -- We can uniformly bound the derivative of the Taylor polynomial
  have h' : ∀ y ∈ Ico a x,
      ‖((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤
        (n ! : ℝ)⁻¹ * |x - a| ^ n * C := by
    rintro y ⟨hay, hyx⟩
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    · rw [abs_mul, abs_pow, abs_inv, Nat.abs_cast]
      gcongr
    -- Estimate the iterated derivative by `C`
    · exact hC y ⟨hay, hyx.le.trans hx.2⟩
  -- Apply the mean value theorem for vector-valued functions:
  have A : ∀ t ∈ Icc a x, HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((↑n !)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a x) t := by
    intro t ht
    have I : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
    exact (hasDerivWithinAt_taylorWithinEval_at_Icc x h (I ht) hf.of_succ hf').mono I
  have := norm_image_sub_le_of_norm_deriv_le_segment' A h' x (right_mem_Icc.2 hx.1)
  simp only [taylorWithinEval_self] at this
  refine this.trans_eq ?_
  -- The rest is a trivial calculation
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  ring

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
There exists a constant `C` such that for all `x ∈ Icc a b` the difference of `f` and its `n`-th
Taylor polynomial can be estimated by `C * (x - a)^(n+1)`. -/
/-
**exists_taylor_mean_remainder_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_taylor_mean_remainder_bound {f : Real -> E} {a b : Real} {n : Nat} 
(hab : a <= b) (hf : ContDiffOn Real (n + 1) f (Icc a b)) : exists C, forall x i
n Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ <= C * (x - a) ^ (n + 1)
参数：hab : a <= b；hf : ContDiffOn Real (n + 1) f (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_mul_eq_mul_div₀`：div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * 
b / c
· 使用定理 `taylor_mean_remainder_bound`：taylor_mean_remainder_bound {f : Real -> E}
 {a b C x : Real} {n : Nat} (hab : a <= b) (hf : ContDiffOn Real (n + 1) f (Icc 
a b)) (hx : x in …
· 使用定理 `ContinuousOn.le_sSup_image_Icc`：le_sSup_image_Icc (h : ContinuousOn f <|
 Icc a b) (hc : c in Icc a b) : f c <= sSup (f '' Icc a b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `ContDiffOn.continuousOn_iteratedDerivWithin`：ContDiffOn.continuousOn_ite
ratedDerivWithin {n : Nat∞ω} {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m <= n) (
hs : UniqueDiffOn 𝕜 s) : Continuo…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)

--- 原说明 ---
**Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set 
`Icc a b`.
There exists a constant `C` such that for all `x ∈ Icc a b` the difference of `f
` and its `n`-th
Taylor polynomial can be estimated by `C * (x - a)^(n+1)`.
-/
theorem exists_taylor_mean_remainder_bound {f : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    have : x = a := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : ℝ → ℝ := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖
  use SupSet.sSup (g '' Icc a b) / (n !)
  intro x hx
  rw [div_mul_eq_mul_div₀]
  refine taylor_mean_remainder_bound hab hf hx fun y => ?_
  exact (hf.continuousOn_iteratedDerivWithin rfl.le <| uniqueDiffOn_Icc h).norm.le_sSup_image_Icc

/-- **Taylor's theorem** with the Integral form of the remainder. This is an auxiliary theorem
which is used to prove the two useful versions `taylor_integral_remainder_of_absolutelyContinuous`
and `taylor_integral_remainder`.

We assume that for any `k ≤ n`, the following equation on integration by parts hold:
$$\int_{x_0}^x \frac{f^{(k+1)}(t) (x - t)^k}{k!} =
\frac{f^{(k)}(t) (x - t)^k}{k!} |_{x_0}^x -\int_{x_0}^x \frac{f^{(k)}(t) (x - t)^{k-1}}{(k-1)!}.$$
Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
/-
**taylor_integral_remainder_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_integral_remainder_aux [NormedAddCommGroup F] [NormedSpace Real F] 
{f : Real -> F} {x x₀ : Real} {n : Nat} (hf : forall k <= n, let u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `taylor_within_zero_eval`：taylor_within_zero_eval (f : Real -> E) (s : Se
t Real) (x₀ x : Real) : taylorWithinEval f 0 s x₀ x = f x₀
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_one`：iteratedDerivWithin_one : iteratedDerivWithin 1
 f s = derivWithin f s
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `deriv_div_const`：deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x =
 deriv c x / d
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
**Taylor's theorem** with the Integral form of the remainder. This is an auxilia
ry theorem
which is used to prove the two useful versions `taylor_integral_remainder_of_abs
olutelyContinuous`
and `taylor_integral_remainder`.

We assume that for any `k ≤ n`, the following equation on integration by parts h
old:
$$\int_{x_0}^x \frac{f^{(k+1)}(t) (x - t)^k}{k!} =
\frac{f^{(k)}(t) (x - t)^k}{k!} |_{x_0}^x -\int_{x_0}^x \frac{f^{(k)}(t) (x - t)
^{k-1}}{(k-1)!}.$$
Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the
 $n+1$-th iterated
derivative.
-/
theorem taylor_integral_remainder_aux [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, let u := fun t ↦ (x - t) ^ k / k !;
      let v := fun t ↦ iteratedDerivWithin k f [[x₀, x]] t;
      ∫ (t : ℝ) in x₀..x, u t • deriv v t = u x • v x - u x₀ • v x₀ -
      ∫ (t : ℝ) in x₀..x, deriv u t • v t) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, zero_add, iteratedDerivWithin_one, one_smul]
    simp only [nonpos_iff_eq_zero, sub_self, deriv_div_const, forall_eq, pow_zero,
      Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
      iteratedDerivWithin_zero, one_smul, deriv_const', div_one, zero_smul,
      intervalIntegral.integral_zero, sub_zero] at hf
    rw [← hf]
    refine intervalIntegral.integral_congr_uIoo fun _ ⟨h1, h2⟩ => ?_
    rw [← derivWithin_of_mem_nhds <| Icc_mem_nhds h1 h2]
    rfl
  | succ n ih =>
    specialize ih (by grind)
    simp only [taylorWithinEval_succ, mul_inv_rev]
    rw [sub_add_eq_sub_sub, ih]
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have := hf (n + 1) (by rfl)
    convert! this.symm using 1
    · simp only [sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, zero_smul, zero_sub, deriv_div_const, Nat.factorial]
      apply fun (a b c d : F) (_ : b = c) (_ : a = -d) ↦ show a - b = -c - d by grind
      · grind
      · rw [← intervalIntegral.integral_neg]
        congr
        ext t
        rw [deriv_fun_pow (by fun_prop), deriv_const_sub, deriv_id'', ← neg_smul]
        congr
        field_simp
        grind
    · refine intervalIntegral.integral_congr_uIoo fun _ ⟨h1, h2⟩ => ?_
      rw [iteratedDerivWithin_succ]
      congr
      · rw [Nat.factorial, Nat.cast_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      · rw [← derivWithin_of_mem_nhds <| Icc_mem_nhds h1 h2]
        rfl

/-- **Taylor's theorem** with the Integral form of the remainder.

We assume that `f` is `n`-times continuously differentiable on the closed set `uIcc x₀ x` and
its `n`-th derivative is absolutely continuous on `uIcc x₀ x`. Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
/-
**taylor_integral_remainder_of_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：taylor_integral_remainder_of_absolutelyContinuous {f : Real -> Real} {x x₀
 : Real} {n : Nat} (hf₁ : ContDiffOn Real n f (uIcc x₀ x)) (hf₂ : AbsolutelyCont
inuousOnInterval (iteratedDerivWithin n f (uIcc x₀ x)) x₀ x) : f x - taylorWithi
nEval f n (uIcc x₀ x) x₀ x = ∫ t in x₀..x, ((x - t) ^ n / n !) * iteratedDerivWi
thin (n + 1) f (uIcc x₀ x) t
参数：hf₁ : ContDiffOn Real n f (uIcc x₀ x)；hf₂ : AbsolutelyContinuousOnInterval (i
teratedDerivWithin n f (uIcc x₀ x)) x₀ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `taylor_integral_remainder_aux`：taylor_integral_remainder_aux [NormedAddC
ommGroup F] [NormedSpace Real F] {f : Real -> F} {x x₀ : Real} {n : Nat} (hf : f
orall k <= n, let u
· 使用定理 `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`：Absolute
lyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul {f g : Real -> Real} {a b
 : Real} (hf : AbsolutelyContinuousOnInterval f a b)…
· 使用定理 `ContDiffOn.absolutelyContinuousOnInterval`：∀ {a b : ℝ} {E : Type u_3} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {f : ℝ → E},   ContDiffOn
 ℝ 1 f (Set.uIcc a b) → Absolut…
· 使用定理 `ContDiffOn.div_const`：ContDiffOn.div_const {f : E -> 𝕜'} {n} (hf : ContD
iffOn 𝕜 n f s) (c : 𝕜') : ContDiffOn 𝕜 n (fun x => f x / c) s
· 使用定理 `ContDiffOn.pow`：ContDiffOn.pow {f : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (m
 : Nat) : ContDiffOn 𝕜 n (fun y => f y ^ m) s
· 使用定理 `ContDiffOn.sub`：ContDiffOn.sub {s : Set E} {f g : E -> F} (hf : ContDiff
On 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s
· 使用定理 `contDiffOn_const`：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n 
(fun _ : E => c) s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
**Taylor's theorem** with the Integral form of the remainder.

We assume that `f` is `n`-times continuously differentiable on the closed set `u
Icc x₀ x` and
its `n`-th derivative is absolutely continuous on `uIcc x₀ x`. Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the
 $n+1$-th iterated
derivative.
-/
theorem taylor_integral_remainder_of_absolutelyContinuous {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hf₁ : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf₂ : AbsolutelyContinuousOnInterval (iteratedDerivWithin n f (uIcc x₀ x)) x₀ x) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) * iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  apply taylor_integral_remainder_aux
  intro k hk
  apply AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
  · apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  · rcases hk.eq_or_lt with rfl | hk
    · exact hf₂
    replace hf₁ := hf₁.of_le (m := k.succ) (by norm_cast)
    grind [ContDiffOn.absolutelyContinuousOnInterval, uniqueDiffOn_uIcc,
      contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin]

/-- **Taylor's theorem** with the Integral form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable on the closed set `uIcc x₀ x`. Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
/-
**taylor_integral_remainder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：taylor_integral_remainder [NormedAddCommGroup F] [NormedSpace Real F] [Com
pleteSpace F] {f : Real -> F} {x x₀ : Real} {n : Nat} (hf : ContDiffOn Real (n +
 1 : Nat) f (uIcc x₀ x)) : f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = ∫ t in 
x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t
参数：hf : ContDiffOn Real (n + 1 : Nat) f (uIcc x₀ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `taylorWithinEval_self`：taylorWithinEval_self (f : Real -> E) (n : Nat) (
s : Set Real) (x₀ : Real) : taylorWithinEval f n s x₀ x₀ = f x₀
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `uniqueDiffOn_uIcc`：uniqueDiffOn_uIcc {a b : Real} (hab : a != b) : Uniqu
eDiffOn Real (uIcc a b)
· 使用定理 `taylor_integral_remainder_aux`：taylor_integral_remainder_aux [NormedAddC
ommGroup F] [NormedSpace Real F] {f : Real -> F} {x x₀ : Real} {n : Nat} (hf : f
orall k <= n, let u
· 使用定理 `intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt`：integr
al_smul_deriv_eq_deriv_smul_of_hasDerivAt (hu : ContinuousOn u [[a, b]]) (hv : C
ontinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a…
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
**Taylor's theorem** with the Integral form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable on the closed set 
`uIcc x₀ x`. Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the
 $n+1$-th iterated
derivative.
-/
theorem taylor_integral_remainder [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (uIcc x₀ x)) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  have : UniqueDiffOn ℝ [[x₀, x]] := uniqueDiffOn_uIcc this
  apply taylor_integral_remainder_aux
  intro k hk
  apply intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t ↦ (x - t) ^ k / k !) (v := fun t ↦ iteratedDerivWithin k f (uIcc x₀ x) t)
  · fun_prop
  · exact hf.continuousOn_iteratedDerivWithin (by norm_cast; omega) this
  · intro t ht
    apply DifferentiableAt.hasDerivAt
    fun_prop
  · intro t ht
    refine DifferentiableOn.hasDerivAt (s := uIoo x₀ x) ?_ (by grind [Ioo_mem_nhds, uIoo])
    exact hf.differentiableOn_iteratedDerivWithin (by norm_cast; omega) this
      |>.mono (by grind [uIoo, uIcc])
  · apply ContinuousOn.intervalIntegrable
    fun_prop
  · apply IntervalIntegrable.congr_ae (f := iteratedDerivWithin (k + 1) f [[x₀, x]])
    · exact hf.continuousOn_iteratedDerivWithin (by norm_cast; omega) this |>.intervalIntegrable
    · rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
      filter_upwards [MeasureTheory.volume.ae_ne x₀, MeasureTheory.volume.ae_ne x] with _ _ _ _
      rw [iteratedDerivWithin_succ]
      grind [derivWithin_of_mem_nhds, Icc_mem_nhds, uIcc]
