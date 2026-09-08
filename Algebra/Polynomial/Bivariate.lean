/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Bivariate polynomials

This file introduces the notation `R[X][Y]` for the polynomial ring `R[X][X]` in two variables,
and the notation `Y` for the second variable, in the `Polynomial.Bivariate` scope.

It also defines `Polynomial.evalEval` for the evaluation of a bivariate polynomial at a point
on the affine plane, which is a ring homomorphism (`Polynomial.evalEvalRingHom`), as well as
the abbreviation `CC` to view a constant in the base ring `R` as a bivariate polynomial.
-/

@[expose] public section

/-- The notation `Y` for `X` in the `Polynomial` scope. -/
scoped[Polynomial.Bivariate] notation3:max "Y" => Polynomial.X (R := Polynomial _)

/-- The notation `R[X][Y]` for `R[X][X]` in the `Polynomial` scope. -/
scoped[Polynomial.Bivariate] notation3:max R "[X][Y]" => Polynomial (Polynomial R)

open scoped Polynomial.Bivariate

namespace Polynomial

noncomputable section

variable {R S : Type*}

section Semiring

variable [Semiring R]

/-- `evalEval x y p` is the evaluation `p(x,y)` of a two-variable polynomial `p : R[X][Y]`. -/
/-
**Polynomial.evalEval** 是 Mathlib 中的一个缩写定义，位于命名空间 `Polynomial`。
形式化陈述：evalEval (x y : R) (p : R[X][Y]) : R
参数：x y : R；p : R[X][Y]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`evalEval x y p` is the evaluation `p(x,y)` of a two-variable polynomial `p : R[
X][Y]`.
-/
abbrev evalEval (x y : R) (p : R[X][Y]) : R := eval x (eval (C y) p)

/-- A constant viewed as a polynomial in two variables. -/
/-
**Polynomial.CC** 是 Mathlib 中的一个缩写定义，位于命名空间 `Polynomial`。
形式化陈述：CC (r : R) : R[X][Y]
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant viewed as a polynomial in two variables.
-/
abbrev CC (r : R) : R[X][Y] := C (C r)
/-
**Polynomial.evalEval_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_C (x y : R) (p : R[X]) : (C p).evalEval x y = p.eval x
参数：x y : R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.evalEval.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (x y : R)
 (p : Polynomial (Polynomial R)),   Polynomial.evalEval x y p = Polynomial.eval 
x (Polynomial.…
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
lemma evalEval_C (x y : R) (p : R[X]) : (C p).evalEval x y = p.eval x := by
  rw [evalEval, eval_C]
/-
**Polynomial.evalEval_map_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_map_C (x y : R) (p : R[X]) : (p.map C).evalEval x y = p.eval y
参数：x y : R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.evalEval.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (x y : R)
 (p : Polynomial (Polynomial R)),   Polynomial.evalEval x y p = Polynomial.eval 
x (Polynomial.…
· 使用定理 `Polynomial.eval_map_apply`：∀ {R : Type u} {S : Type v} [inst : Semiring 
R] {p : Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (x : R),   Polynomial.
eval (f x) (Pol…
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
lemma evalEval_map_C (x y : R) (p : R[X]) : (p.map C).evalEval x y = p.eval y := by
  rw [evalEval, eval_map_apply, eval_C]

@[simp]
/-
**Polynomial.evalEval_CC** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_CC (x y : R) (p : R) : (CC p).evalEval x y = p
参数：x y : R；p : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.evalEval_C`：evalEval_C (x y : R) (p : R[X]) : (C p).evalEval 
x y = p.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
lemma evalEval_CC (x y : R) (p : R) : (CC p).evalEval x y = p := by
  rw [evalEval_C, eval_C]

@[simp]
/-
**Polynomial.evalEval_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_zero (x y : R) : (0 : R[X][Y]).evalEval x y = 0
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_zero (x y : R) : (0 : R[X][Y]).evalEval x y = 0 := by
  simp only [evalEval, eval_zero]

@[simp]
/-
**Polynomial.evalEval_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_one (x y : R) : (1 : R[X][Y]).evalEval x y = 1
参数：x y : R。
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
lemma evalEval_one (x y : R) : (1 : R[X][Y]).evalEval x y = 1 := by
  simp only [evalEval, eval_one]

@[simp]
/-
**Polynomial.evalEval_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_natCast (x y : R) (n : Nat) : (n : R[X][Y]).evalEval x y = n
参数：x y : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_natCast (x y : R) (n : ℕ) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_natCast]

@[simp]
/-
**Polynomial.evalEval_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_X (x y : R) : X.evalEval x y = y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.evalEval.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (x y : R)
 (p : Polynomial (Polynomial R)),   Polynomial.evalEval x y p = Polynomial.eval 
x (Polynomial.…
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
lemma evalEval_X (x y : R) : X.evalEval x y = y := by
  rw [evalEval, eval_X, eval_C]

@[simp]
/-
**Polynomial.evalEval_add** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_add (x y : R) (p q : R[X][Y]) : (p + q).evalEval x y = p.evalEval
 x y + q.evalEval x y
参数：x y : R；p q : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_add (x y : R) (p q : R[X][Y]) :
    (p + q).evalEval x y = p.evalEval x y + q.evalEval x y := by
  simp only [evalEval, eval_add]
/-
**Polynomial.evalEval_sum** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_sum (x y : R) (p : R[X]) (f : Nat -> R -> R[X][Y]) : (p.sum f).ev
alEval x y = p.sum fun n a => (f n a).evalEval x y
参数：x y : R；p : R[X]；f : Nat -> R -> R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_sum`：eval₂_sum (p : T[X]) (g : Nat -> T -> R[X]) (x : S
) : (p.sum g).eval₂ f x = p.sum fun n a => (g n a).eval₂ f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_sum (x y : R) (p : R[X]) (f : ℕ → R → R[X][Y]) :
    (p.sum f).evalEval x y = p.sum fun n a => (f n a).evalEval x y := by
  simp only [evalEval, eval, eval₂_sum]
/-
**Polynomial.evalEval_finsetSum** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_finsetSum {ι : Type*} (s : Finset ι) (x y : R) (f : ι -> R[X][Y])
 : (∑ i in s, f i).evalEval x y = ∑ i in s, (f i).evalEval x y
参数：s : Finset ι；x y : R；f : ι -> R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_finsetSum {ι : Type*} (s : Finset ι) (x y : R) (f : ι → R[X][Y]) :
    (∑ i ∈ s, f i).evalEval x y = ∑ i ∈ s, (f i).evalEval x y := by
  simp only [evalEval, eval_finsetSum]

@[deprecated (since := "2026-04-08")] alias evalEval_finset_sum := evalEval_finsetSum

@[simp]
/-
**Polynomial.evalEval_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_smul [DistribSMul S R] [IsScalarTower S R R] (x y : R) (s : S) (p
 : R[X][Y]) : (s • p).evalEval x y = s • p.evalEval x y
参数：x y : R；s : S；p : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_smul [DistribSMul S R] [IsScalarTower S R R] (x y : R) (s : S)
    (p : R[X][Y]) : (s • p).evalEval x y = s • p.evalEval x y := by
  simp only [evalEval, eval_smul]
/-
**Polynomial.evalEval_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_surjective (x y : R) : Function.Surjective evalEval x y
参数：x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.evalEval_CC`：evalEval_CC (x y : R) (p : R) : (CC p).evalEval 
x y = p
-/
lemma evalEval_surjective (x y : R) : Function.Surjective <| evalEval x y :=
  fun y => ⟨CC y, evalEval_CC ..⟩

end Semiring

section Ring

variable [Ring R]

@[simp]
/-
**Polynomial.evalEval_neg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_neg (x y : R) (p : R[X][Y]) : (-p).evalEval x y = -p.evalEval x y
参数：x y : R；p : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_neg (x y : R) (p : R[X][Y]) : (-p).evalEval x y = -p.evalEval x y := by
  simp only [evalEval, eval_neg]

@[simp]
/-
**Polynomial.evalEval_sub** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_sub (x y : R) (p q : R[X][Y]) : (p - q).evalEval x y = p.evalEval
 x y - q.evalEval x y
参数：x y : R；p q : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_sub (x y : R) (p q : R[X][Y]) :
    (p - q).evalEval x y = p.evalEval x y - q.evalEval x y := by
  simp only [evalEval, eval_sub]

@[simp]
/-
**Polynomial.evalEval_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_intCast (x y : R) (n : Int) : (n : R[X][Y]).evalEval x y = n
参数：x y : R；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_intCast`：eval_intCast {n : Int} {x : R} : (n : R[X]).eva
l x = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_intCast (x y : R) (n : ℤ) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_intCast]

end Ring

section CommSemiring

variable [CommSemiring R]

@[simp]
/-
**Polynomial.evalEval_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_mul (x y : R) (p q : R[X][Y]) : (p * q).evalEval x y = p.evalEval
 x y * q.evalEval x y
参数：x y : R；p q : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_mul (x y : R) (p q : R[X][Y]) :
    (p * q).evalEval x y = p.evalEval x y * q.evalEval x y := by
  simp only [evalEval, eval_mul]
/-
**Polynomial.evalEval_prod** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_prod {ι : Type*} (s : Finset ι) (x y : R) (p : ι -> R[X][Y]) : (∏
 j in s, p j).evalEval x y = ∏ j in s, (p j).evalEval x y
参数：s : Finset ι；x y : R；p : ι -> R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_prod {ι : Type*} (s : Finset ι) (x y : R) (p : ι → R[X][Y]) :
    (∏ j ∈ s, p j).evalEval x y = ∏ j ∈ s, (p j).evalEval x y := by
  simp only [evalEval, eval_prod]
/-
**Polynomial.evalEval_list_prod** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_list_prod (x y : R) (l : List R[X][Y]) : l.prod.evalEval x y = (l
.map <| evalEval x y).prod
参数：x y : R；l : List R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_list_prod`：eval_list_prod (l : List R[X]) (x : R) : eval
 x l.prod = (l.map (eval x)).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
lemma evalEval_list_prod (x y : R) (l : List R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simp only [evalEval, eval_list_prod, List.map_map]
  rfl -- todo: add the missing lemma
/-
**Polynomial.evalEval_multiset_prod** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_multiset_prod (x y : R) (l : Multiset R[X][Y]) : l.prod.evalEval 
x y = (l.map <| evalEval x y).prod
参数：x y : R；l : Multiset R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_multiset_prod`：eval_multiset_prod (s : Multiset R[X]) (x
 : R) : eval x s.prod = (s.map (eval x)).prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_multiset_prod (x y : R) (l : Multiset R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simp [evalEval, eval_multiset_prod, Multiset.map_map]

@[simp]
/-
**Polynomial.evalEval_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_pow (x y : R) (p : R[X][Y]) (n : Nat) : (p ^ n).evalEval x y = p.
evalEval x y ^ n
参数：x y : R；p : R[X][Y]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evalEval_pow (x y : R) (p : R[X][Y]) (n : ℕ) : (p ^ n).evalEval x y = p.evalEval x y ^ n := by
  simp only [evalEval, eval_pow]
/-
**Polynomial.evalEval_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEval_dvd (x y : R) {p q : R[X][Y]} : p ∣ q -> p.evalEval x y ∣ q.evalE
val x y
参数：x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval_dvd`：eval_dvd : p ∣ q -> eval x p ∣ eval x q
-/
lemma evalEval_dvd (x y : R) {p q : R[X][Y]} : p ∣ q → p.evalEval x y ∣ q.evalEval x y :=
  eval_dvd ∘ eval_dvd
/-
**Polynomial.coe_algebraMap_eq_CC** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R := R) := rfl

/-- `evalEval x y` as a ring homomorphism. -/
/-
**Polynomial.evalEvalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u_1} → [inst : CommSemiring R] → R → R → Polynomial (Polynomial 
R) →+* R
参数：Polynomial R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`evalEval x y` as a ring homomorphism.
-/
@[simps!] abbrev evalEvalRingHom (x y : R) : R[X][Y] →+* R :=
  (evalRingHom x).comp (evalRingHom <| C y)
/-
**Polynomial.coe_evalEvalRingHom** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y := rfl
/-
**Polynomial.evalEvalRingHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：evalEvalRingHom_eq (x : R) : evalEvalRingHom x = eval₂RingHom (evalRingHom
 x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.ringHom_ext'`：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* 
S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval₂RingHom_comp_C`：eval₂RingHom_comp_C (f : R ->+* S) (x : 
S) : (eval₂RingHom f x).comp C = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.evalEvalRingHom_apply`：∀ {R : Type u_1} [inst : CommSemiring 
R] (x y : R) (x_1 : Polynomial (Polynomial R)),   (Polynomial.evalEvalRingHom x 
y) x_1 = Polynomial.ev…
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
-/
lemma evalEvalRingHom_eq (x : R) : evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_evalRingHom (x : R) : eval₂ (evalRingHom x) = evalEval x := by
  ext1; rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]
/-
**Polynomial.map_evalRingHom_eval** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：map_evalRingHom_eval (x y : R) (p : R[X][Y]) : (p.map <| evalRingHom x).ev
al y = p.evalEval x y
参数：x y : R；p : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用引理 `Polynomial.eval₂_evalRingHom`：eval₂_evalRingHom (x : R) : eval₂ (evalRin
gHom x) = evalEval x
-/
lemma map_evalRingHom_eval (x y : R) (p : R[X][Y]) :
    (p.map <| evalRingHom x).eval y = p.evalEval x y := by
  rw [eval_map, eval₂_evalRingHom]

end CommSemiring

section

variable [Semiring R] [Semiring S] (f : R →+* S) (p : R[X][Y]) (q : R[X])

/-
**Polynomial.map_mapRingHom_eval_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：map_mapRingHom_eval_map : (p.map <| mapRingHom f).eval (q.map f) = (p.eval
 q).map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
-/
lemma map_mapRingHom_eval_map : (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f := by
  rw [eval_map, ← coe_mapRingHom, eval₂_hom]
/-
**Polynomial.map_mapRingHom_eval_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：map_mapRingHom_eval_map_eval (r : R) : ((p.map <| mapRingHom f).eval <| q.
map f).eval (f r) = f ((p.eval q).eval r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.map_mapRingHom_eval_map`：map_mapRingHom_eval_map : (p.map <| 
mapRingHom f).eval (q.map f) = (p.eval q).map f
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
-/
lemma map_mapRingHom_eval_map_eval (r : R) :
    ((p.map <| mapRingHom f).eval <| q.map f).eval (f r) = f ((p.eval q).eval r) := by
  rw [map_mapRingHom_eval_map, eval_map, eval₂_hom]
/-
**Polynomial.map_mapRingHom_evalEval** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：map_mapRingHom_evalEval (x y : R) : (p.map <| mapRingHom f).evalEval (f x)
 (f y) = f (p.evalEval x y)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.evalEval.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (x y : R)
 (p : Polynomial (Polynomial R)),   Polynomial.evalEval x y p = Polynomial.eval 
x (Polynomial.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.map_mapRingHom_eval_map_eval`：map_mapRingHom_eval_map_eval (r
 : R) : ((p.map <| mapRingHom f).eval <| q.map f).eval (f r) = f ((p.eval q).eva
l r)
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
-/
lemma map_mapRingHom_evalEval (x y : R) :
    (p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y) := by
  rw [evalEval, ← map_mapRingHom_eval_map_eval, map_C]

end

variable [CommSemiring R] [CommSemiring S]

/-- Two equivalent ways to express the evaluation of a bivariate polynomial over `R`
at a point in the affine plane over an `R`-algebra `S`. -/
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two equivalent ways to express the evaluation of a bivariate polynomial over `R`
at a point in the affine plane over an `R`-algebra `S`.
-/
lemma eval₂RingHom_eval₂RingHom (f : R →+* S) (x y : S) :
    eval₂RingHom (eval₂RingHom f x) y =
      (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom f) := by
  ext <;> simp
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_eval₂RingHom_apply (f : R →+* S) (x y : S) (p : R[X][Y]) :
    eval₂ (eval₂RingHom f x) y p = (p.map <| mapRingHom f).evalEval x y :=
  congr($(eval₂RingHom_eval₂RingHom f x y) p)
/-
**Polynomial.eval_C_X_comp_eval** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval_C_X_comp_eval₂_map_C_X :
    (evalRingHom (C X : R[X][Y])).comp (eval₂RingHom (mapRingHom <| algebraMap R R[X][Y]) (C Y)) =
      .id _ := by
  ext <;> simp

/-- Viewing `R[X,Y,X']` as an `R[X']`-algebra, a polynomial `p : R[X',Y']` can be evaluated at
`Y : R[X,Y,X']` (substitution of `Y'` by `Y`), obtaining another polynomial in `R[X,Y,X']`.
When this polynomial is then evaluated at `X' = X`, the original polynomial `p` is recovered. -/
/-
**Polynomial.eval_C_X_eval** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Viewing `R[X,Y,X']` as an `R[X']`-algebra, a polynomial `p : R[X',Y']` can be ev
aluated at
`Y : R[X,Y,X']` (substitution of `Y'` by `Y`), obtaining another polynomial in `
R[X,Y,X']`.
When this polynomial is then evaluated at `X' = X`, the original polynomial `p` 
is recovered.
-/
lemma eval_C_X_eval₂_map_C_X {p : R[X][Y]} :
    eval (C X) (eval₂ (mapRingHom <| algebraMap R R[X][Y]) (C Y) p) = p :=
  congr($eval_C_X_comp_eval₂_map_C_X p)

end

section aevalAeval

noncomputable section

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

variable (R A) in
/-- Given valuations `x` and `y` of the variables in an `R`-algebra `A`, the bijection induced by
the unique `R`-algebra homomorphism from `R[X][Y]` to `A` sending `X` to `x` and `Y` to `y`. -/
@[simps! apply_apply symm_apply]
/-
**Polynomial.aevalAevalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：aevalAevalEquiv : A × A ≃ (R[X][Y] ->ₐ[R] A) where .comp .restrictScalars 
R toFun xy
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given valuations `x` and `y` of the variables in an `R`-algebra `A`, the bijecti
on induced by
the unique `R`-algebra homomorphism from `R[X][Y]` to `A` sending `X` to `x` and
 `Y` to `y`.
-/
def aevalAevalEquiv : A × A ≃ (R[X][Y] →ₐ[R] A) where
  toFun xy := aeval xy.fst |>.restrictScalars R |>.comp <|
    let := Polynomial.algebra; aeval (R := R[X]) (C xy.snd) |>.restrictScalars R
  invFun f := ⟨f <| C X, f Y⟩
  left_inv f := by simp
  right_inv f := algHom_ext' (by ext; simp) (by simp)

/-- Given valuations `x` and `y` of the variables in an `R`-algebra `A`, `aevalAeval x y` is
the unique `R`-algebra homomorphism from `R[X][Y]` to `A` sending `X` to `x` and `Y` to `y`. -/
/-
**Polynomial.aevalAeval** 是 Mathlib 中的一个缩写定义，位于命名空间 `Polynomial`。
形式化陈述：aevalAeval (x y : A) : R[X][Y] ->ₐ[R] A
参数：x y : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given valuations `x` and `y` of the variables in an `R`-algebra `A`, `aevalAeval
 x y` is
the unique `R`-algebra homomorphism from `R[X][Y]` to `A` sending `X` to `x` and
 `Y` to `y`.
-/
abbrev aevalAeval (x y : A) : R[X][Y] →ₐ[R] A :=
  aevalAevalEquiv R A ⟨x, y⟩
/-
**Polynomial.aevalAevalEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aevalAevalEquiv_apply (xy : A × A) : aevalAevalEquiv R A xy = aevalAeval x
y.1 xy.2
参数：xy : A × A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aevalAevalEquiv_apply (xy : A × A) : aevalAevalEquiv R A xy = aevalAeval xy.1 xy.2 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.coe_aevalAeval_eq_evalEval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_aevalAeval_eq_evalEval (x y : A) : ⇑(aevalAeval x y) = evalEval x y
参数：x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Polynomial.eval₂AlgHom_apply`：∀ {R : Type u} {A : Type z} {B : Type u_2}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [ins…
· 使用定理 `Polynomial.mapRingHom_id`：mapRingHom_id : mapRingHom (RingHom.id R) = Ri
ngHom.id R[X]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_aevalAeval_eq_evalEval (x y : A) : ⇑(aevalAeval x y) = evalEval x y := by
  ext
  simp [aeval, aevalEquiv]
/-
**Polynomial.aevalAeval_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aevalAeval_C (x y : A) (p : R[X]) : (C p).aevalAeval x y = aeval x p
参数：x y : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aevalAeval_C (x y : A) (p : R[X]) : (C p).aevalAeval x y = aeval x p := by simp
/-
**Polynomial.aevalAeval_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aevalAeval_X (x y : A) : (C X : R[X][Y]).aevalAeval x y = x
参数：x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.aevalAeval_C`：aevalAeval_C (x y : A) (p : R[X]) : (C p).aeval
Aeval x y = aeval x p
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
lemma aevalAeval_X (x y : A) : (C X : R[X][Y]).aevalAeval x y = x := by rw [aevalAeval_C, aeval_X]
/-
**Polynomial.aevalAeval_Y** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aevalAeval_Y (x y : A) : (Y : R[X][Y]).aevalAeval x y = y
参数：x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aevalAeval_Y (x y : A) : (Y : R[X][Y]).aevalAeval x y = y := by simp

/-- The R-algebra automorphism given by `X ↦ Y` and `Y ↦ X`. -/
/-
**Polynomial.Bivariate.swap** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Bivariate`。
形式化陈述：{R : Type u_1} → [inst : CommSemiring R] → Polynomial (Polynomial R) ≃ₐ[R]
 Polynomial (Polynomial R)
参数：Polynomial R；Polynomial R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The R-algebra automorphism given by `X ↦ Y` and `Y ↦ X`.
-/
def Bivariate.swap : R[X][Y] ≃ₐ[R] R[X][Y] := by
  apply AlgEquiv.ofAlgHom (aevalAeval (Y : R[X][Y]) (C X)) (aevalAeval (Y : R[X][Y]) (C X))
    <;> (ext n m <;> simp)

@[simp]
/-
**Polynomial.Bivariate.swap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariate
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], Polynomial.Bivariate.swap.symm =
 Polynomial.Bivariate.swap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bivariate.swap_symm : swap.symm = (swap (R := R)) := rfl
/-
**Polynomial.Bivariate.swap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariat
e`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (p : Polynomial (Polynomial R)), 
  Polynomial.Bivariate.swap p = (Polynomial.aevalAeval Polynomial.X (Polynomial.
C Polynomial.X)) p
参数：p : Polynomial (Polynomial R)；Polynomial.aevalAeval Polynomial.X (Polynomial.
C Polynomial.X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bivariate.swap_apply (p : R[X][Y]) : swap p = p.aevalAeval (A := R[X][Y]) Y (C X) := rfl

attribute [local simp] Bivariate.swap_apply
/-
**Polynomial.Bivariate.swap_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariate`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], Polynomial.Bivariate.swap (Polyn
omial.C Polynomial.X) = Polynomial.X
参数：Polynomial.C Polynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Bivariate.swap_X : swap (R := R) (C X) = Y := by simp
/-
**Polynomial.Bivariate.swap_Y** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariate`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], Polynomial.Bivariate.swap Polyno
mial.X = Polynomial.C Polynomial.X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Bivariate.swap_Y : swap (R := R) Y = (C X) := by simp
/-
**Polynomial.Bivariate.swap_C_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariate`
。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (r : R),   Polynomial.Bivariate.s
wap (Polynomial.C (Polynomial.C r)) = Polynomial.C (Polynomial.C r)
参数：r : R；Polynomial.C (Polynomial.C r)；Polynomial.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Bivariate.swap_C_C (r : R) : swap (C (C r)) = C (C r) := by simp
/-
**Polynomial.Bivariate.swap_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariate`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (f : Polynomial R),   Polynomial.
Bivariate.swap (Polynomial.C f) = Polynomial.map Polynomial.C f
参数：f : Polynomial R；Polynomial.C f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用引理 `Polynomial.aeval_X_left_eq_map`：aeval_X_left_eq_map [CommSemiring S] [Al
gebra R S] (p : R[X]) : aeval X p = map (algebraMap R S) p
-/
theorem Bivariate.swap_C (f : R[X]) : swap (C f) = f.map C := by
  simpa [← algebraMap_eq] using aeval_X_left_eq_map f
/-
**Polynomial.Bivariate.swap_swap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Biv
ariate`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (p : Polynomial (Polynomial R)), 
  Polynomial.Bivariate.swap (Polynomial.Bivariate.swap p) = p
参数：p : Polynomial (Polynomial R)；Polynomial.Bivariate.swap p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
-/
theorem Bivariate.swap_swap_apply (p : R[X][Y]) : swap (swap p) = p :=
  AlgEquiv.symm_apply_apply swap p
/-
**Polynomial.Bivariate.swap_map_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivariat
e`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (f : Polynomial R),   Polynomial.
Bivariate.swap (Polynomial.map Polynomial.C f) = Polynomial.C f
参数：f : Polynomial R；Polynomial.map Polynomial.C f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.Bivariate.swap_Y`：∀ {R : Type u_1} [inst : CommSemiring R], P
olynomial.Bivariate.swap Polynomial.X = Polynomial.C Polynomial.X
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.C_pow`：C_pow : C (a ^ n) = C a ^ n
（共 31 条，此处仅展示前 30 条）
-/
theorem Bivariate.swap_map_C (f : R[X]) : swap (f.map C) = C f := by
  induction f using Polynomial.induction_on' with
  | add => aesop
  | monomial n a => rw [map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow, swap_Y, C_mul, C_pow, Bivariate.swap_C_C]
/-
**Polynomial.Bivariate.swap_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Bivar
iate`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (n : ℕ) (f : Polynomial R),   Pol
ynomial.Bivariate.swap ((Polynomial.monomial n) f) =     Polynomial.map Polynomi
al.C f * Polynomial.C (Polynomial.X ^ n)
参数：n : ℕ；f : Polynomial R；(Polynomial.monomial n) f；Polynomial.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Bivariate.swap_monomial (n : ℕ) (f : R[X]) :
    swap (monomial n f) = f.map C * C (X ^ n) := by
  simp [← C_mul_X_pow_eq_monomial, aeval_X_left_eq_map]
/-
**Polynomial.Bivariate.swap_monomial_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Bivariate`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (n m : ℕ) (r : R),   Polynomial.B
ivariate.swap ((Polynomial.monomial n) ((Polynomial.monomial m) r)) =     (Polyn
omial.monomial m) ((Polynomial.monomial n) r)
参数：n m : ℕ；r : R；(Polynomial.monomial n) ((Polynomial.monomial m) r)；Polynomial.
monomial m；(Polynomial.monomial n) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem Bivariate.swap_monomial_monomial (n m : ℕ) (r : R) :
    swap (monomial n (monomial m r)) = (monomial m (monomial n r)) := by
  simp [← C_mul_X_pow_eq_monomial]; ac_rfl

/-- Evaluating `swap p` at `x`, `y` is the same as evaluating `p` at `y` `x`. -/
/-
**Polynomial.Bivariate.aevalAeval_swap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Biv
ariate`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A] (x y : A)   (p : Polynomial (Polynomial R)),   (P
olynomial.aevalAeval x y) (Polynomial.Bivariate.swap p) = (Polynomial.aevalAeval
 y x) p
参数：x y : A；p : Polynomial (Polynomial R)；Polynomial.aevalAeval x y；Polynomial.Bi
variate.swap p；Polynomial.aevalAeval y x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Evaluating `swap p` at `x`, `y` is the same as evaluating `p` at `y` `x`.
-/
theorem Bivariate.aevalAeval_swap (x y : A) (p : R[X][Y]) :
    aevalAeval x y (swap p) = aevalAeval y x p := by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
    simp
    induction a using Polynomial.induction_on' <;> aesop (add norm add_mul)

attribute [local instance] Polynomial.algebra in
/-
**Polynomial.Bivariate.aveal_eq_map_swap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.B
ivariate`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A] (x : A)   (p : Polynomial (Polynomial R)),   (Pol
ynomial.aeval (Polynomial.C x)) p = (Polynomial.mapAlgHom (Polynomial.aeval x)) 
(Polynomial.Bivariate.swap p)
参数：x : A；p : Polynomial (Polynomial R)；Polynomial.aeval (Polynomial.C x)；Polynom
ial.mapAlgHom (Polynomial.aeval x)；Polynomial.Bivariate.swap p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
-/
theorem Bivariate.aveal_eq_map_swap (x : A) (p : R[X][Y]) :
    aeval (C x) p = mapAlgHom (aeval x) (swap p) := by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
      simp
      induction a using Polynomial.induction_on'
        <;> aesop (add norm [add_mul, C_mul_X_pow_eq_monomial])

end

end aevalAeval

namespace Bivariate
section MvPolynomial

variable {R : Type*} [CommSemiring R]

variable (R) in
/-- The equiv between `R[X][Y]` and `R[X, Y]`. -/
noncomputable
/-
**Polynomial.Bivariate.equivMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.B
ivariate`。
形式化陈述：equivMvPolynomial : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivMvPolynomial : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R :=
  .ofAlgHom (aevalAeval (.X 0) (.X 1)) (MvPolynomial.aeval ![.C X, X])
    (by ext i; fin_cases i <;> simp) (by ext <;> simp)

@[simp]
/-
**Polynomial.Bivariate.equivMvPolynomial_C_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al.Bivariate`。
形式化陈述：equivMvPolynomial_C_C {a} : equivMvPolynomial R (C (C a)) = .C a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivMvPolynomial_C_C {a} : equivMvPolynomial R (C (C a)) = .C a := by
  simp [equivMvPolynomial]

@[simp]
/-
**Polynomial.Bivariate.equivMvPolynomial_C_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al.Bivariate`。
形式化陈述：equivMvPolynomial_C_X : equivMvPolynomial R (C X) = .X 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivMvPolynomial_C_X : equivMvPolynomial R (C X) = .X 0 := by
  simp [equivMvPolynomial]

@[simp]
/-
**Polynomial.Bivariate.equivMvPolynomial_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
.Bivariate`。
形式化陈述：equivMvPolynomial_X : equivMvPolynomial R X = .X 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivMvPolynomial_X : equivMvPolynomial R X = .X 1 := by
  simp [equivMvPolynomial]

@[simp]
/-
**Polynomial.Bivariate.equivMvPolynomial_symm_X_0** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial.Bivariate`。
形式化陈述：equivMvPolynomial_symm_X_0 : (equivMvPolynomial R).symm (.X 0) = C X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivMvPolynomial_symm_X_0 : (equivMvPolynomial R).symm (.X 0) = C X := by
  simp [equivMvPolynomial]

@[simp]
/-
**Polynomial.Bivariate.equivMvPolynomial_symm_X_1** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial.Bivariate`。
形式化陈述：equivMvPolynomial_symm_X_1 : (equivMvPolynomial R).symm (.X 1) = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivMvPolynomial_symm_X_1 : (equivMvPolynomial R).symm (.X 1) = X := by
  simp [equivMvPolynomial]

@[simp]
/-
**Polynomial.Bivariate.equivMvPolynomial_symm_C** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omial.Bivariate`。
形式化陈述：equivMvPolynomial_symm_C (a : R) : (equivMvPolynomial R).symm (.C a) = C (
C a)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivMvPolynomial_symm_C (a : R) : (equivMvPolynomial R).symm (.C a) = C (C a) := by
  simp [equivMvPolynomial]
/-
**Polynomial.Bivariate.pderiv_zero_equivMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial.Bivariate`。
形式化陈述：pderiv_zero_equivMvPolynomial {R : Type*} [CommRing R] (p : R[X][Y]) : (eq
uivMvPolynomial R p).pderiv 0 = equivMvPolynomial R (PolynomialModule.equivPolyn
omialSelf (derivative'.mapCoeffs p))
参数：p : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Derivation.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : d.
mapCoeffs (monomial n x) = .single A n (d x)
· 使用定理 `Polynomial.derivative'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] (
a : Polynomial R), Polynomial.derivative' a = Polynomial.derivative a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_C_C`：equivMvPolynomial_C_C {a} : 
equivMvPolynomial R (C (C a)) = .C a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_C_X`：equivMvPolynomial_C_X : equi
vMvPolynomial R (C X) = .X 0
（共 59 条，此处仅展示前 30 条）
-/
lemma pderiv_zero_equivMvPolynomial {R : Type*} [CommRing R] (p : R[X][Y]) :
    (equivMvPolynomial R p).pderiv 0 = equivMvPolynomial R
      (PolynomialModule.equivPolynomialSelf (derivative'.mapCoeffs p)) := by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [map_nsmul]
/-
**Polynomial.Bivariate.pderiv_one_equivMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial.Bivariate`。
形式化陈述：pderiv_one_equivMvPolynomial (p : R[X][Y]) : (equivMvPolynomial R p).pderi
v 1 = equivMvPolynomial R (derivative p)
参数：p : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `Polynomial.derivative_add`：derivative_add {f g : R[X]} : derivative (f +
 g) = derivative f + derivative g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_C_C`：equivMvPolynomial_C_C {a} : 
equivMvPolynomial R (C (C a)) = .C a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_C_X`：equivMvPolynomial_C_X : equi
vMvPolynomial R (C X) = .X 0
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_X`：equivMvPolynomial_X : equivMvP
olynomial R X = .X 1
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `Derivation.leibniz_pow`：leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n -
 1) • D a
（共 48 条，此处仅展示前 30 条）
-/
lemma pderiv_one_equivMvPolynomial (p : R[X][Y]) :
    (equivMvPolynomial R p).pderiv 1 = equivMvPolynomial R (derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [derivative_pow]

end MvPolynomial

end Bivariate

end Polynomial

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {x y : R} {p : R[X][Y]} (h : p.evalEval x y = 0)

/-- If the evaluation (`evalEval`) of a bivariate polynomial `p : R[X][Y]` at a point (x,y)
is zero, then `Polynomial.evalEval x y` factors through `AdjoinRoot.evalEval`, a ring homomorphism
from `AdjoinRoot p` to `R`. -/
/-
**AdjoinRoot.evalEval** 是 Mathlib 中的一个定义，位于命名空间 `AdjoinRoot`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] → {x y : R} → {p : Polynomial (Poly
nomial R)} → Polynomial.evalEval x y p = 0 → AdjoinRoot p →+* R
参数：Polynomial R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the evaluation (`evalEval`) of a bivariate polynomial `p : R[X][Y]` at a poin
t (x,y)
is zero, then `Polynomial.evalEval x y` factors through `AdjoinRoot.evalEval`, a
 ring homomorphism
from `AdjoinRoot p` to `R`.
-/
@[simps!] noncomputable def evalEval : AdjoinRoot p →+* R :=
  lift (evalRingHom x) y <| eval₂_evalRingHom x ▸ h
/-
**AdjoinRoot.evalEval_mk** 是 Mathlib 中的一个引理，位于命名空间 `AdjoinRoot`。
形式化陈述：evalEval_mk (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y
参数：g : R[X][Y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdjoinRoot.evalEval.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {x y : R}
 {p : Polynomial (Polynomial R)} (h : Polynomial.evalEval x y p = 0),   AdjoinRo
ot.evalEval h …
· 使用定理 `AdjoinRoot.lift_mk`：lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i
 a
· 使用引理 `Polynomial.eval₂_evalRingHom`：eval₂_evalRingHom (x : R) : eval₂ (evalRin
gHom x) = evalEval x
-/
lemma evalEval_mk (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y := by
  rw [evalEval, lift_mk, eval₂_evalRingHom]

end AdjoinRoot

