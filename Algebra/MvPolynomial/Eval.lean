/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Multivariate polynomials

This file defines functions for evaluating multivariate polynomials.
These include generically evaluating a polynomial given a valuation of all its variables,
and more advanced evaluations that allow one to map the coefficients to different rings.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)
+ `R : Type*` `[CommSemiring R]` (the coefficients)
+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`
+ `a : R`
+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians
+ `p : MvPolynomial σ R`

### Definitions

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.
* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`
* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`
* `aeval (g : σ → S₁) p` : evaluates the multivariate polynomial obtained from `p` by the change
  of coefficient semiring corresponding to `g` (`a` stands for `Algebra`)

-/

@[expose] public section

noncomputable section

open Set Function Finsupp AddMonoidAlgebra
open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

section Eval₂

variable (f : R →+* S₁) (g : σ → S₁)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target
-/
def eval₂ (p : MvPolynomial σ R) : S₁ :=
  (AddMonoidAlgebra.coeff p).sum fun s a => f a * s.prod fun n e => g n ^ e
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_eq (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i ∈ d.support, X i ^ d i :=
  rfl
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_eq' [Fintype σ] (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i, X i ^ d i := by
  simp only [eval₂_eq, ← Finsupp.prod_pow]
  rfl

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g = 0 :=
  Finsupp.sum_zero_index

section

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g := by
  classical exact Finsupp.sum_add_index (by simp [f.map_zero]) (by simp [add_mul, f.map_add])

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod fun n e => g n ^ e :=
  Finsupp.sum_single_index (by simp [f.map_zero])

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C (a) : (C a).eval₂ f g = f a := by
  rw [C_apply, eval₂_monomial, prod_zero_index, mul_one]

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_one : (1 : MvPolynomial σ R).eval₂ f g = 1 :=
  (eval₂_C _ _ _).trans f.map_one
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem eval₂_natCast (n : Nat) : (n : MvPolynomial σ R).eval₂ f g = n :=
  (eval₂_C _ _ _).trans (map_natCast f n)
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem eval₂_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval₂ f g = ofNat(n) :=
  eval₂_natCast f g n

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_X (n) : (X n).eval₂ f g = g n := by
  simp [eval₂_monomial, f.map_one, X, prod_single_index, pow_one]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_X_pow {s : σ} {n : ℕ} : ((X s) ^ n).eval₂ f g = (g s) ^ n := by
  simp [X_pow_eq_monomial, eval₂_monomial f g]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_mul_monomial :
    ∀ {s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod fun n e => g n ^ e := by
  classical
  apply MvPolynomial.induction_on p
  · intro a' s a
    simp [C_mul_monomial, eval₂_monomial, f.map_mul]
  · intro p q ih_p ih_q
    simp [add_mul, eval₂_add, ih_p, ih_q]
  · intro p n ih s a
    exact
      calc (p * X n * monomial s a).eval₂ f g
        _ = (p * monomial (Finsupp.single n 1 + s) a).eval₂ f g := by
          rw [monomial_single_add, pow_one, mul_assoc]
        _ = (p * monomial (Finsupp.single n 1) 1).eval₂ f g * f a * s.prod fun n e => g n ^ e := by
          simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
            f.map_one]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_mul_C : (p * C a).eval₂ f g = p.eval₂ f g * f a :=
  (eval₂_mul_monomial _ _).trans <| by simp

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_mul : ∀ {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g := by
  apply MvPolynomial.induction_on q
  · simp [eval₂_C, eval₂_mul_C]
  · simp +contextual [mul_add, eval₂_add]
  · simp +contextual [X, eval₂_mul_monomial, ← mul_assoc]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_mul_eq_zero_of_left (hp : p.eval₂ f g = 0) : (p * q).eval₂ f g = 0 := by
  simp [eval₂_mul f g, hp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_mul_eq_zero_of_right (hq : q.eval₂ f g = 0) : (p * q).eval₂ f g = 0 := by
  simp [eval₂_mul f g, hq]

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_pow {p : MvPolynomial σ R} : ∀ {n : ℕ}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n
  | 0 => by
    rw [pow_zero, pow_zero]
    exact eval₂_one _ _
  | n + 1 => by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

/-- `MvPolynomial.eval₂` as a `RingHom`. -/
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.eval₂` as a `RingHom`.
-/
def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁ where
  toFun := eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _

@[gcongr]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_dvd (f : R →+* S₁) (g : σ → S₁) {p q : MvPolynomial σ R} (h : p ∣ q) :
    p.eval₂ f g ∣ q.eval₂ f g :=
  map_dvd (eval₂Hom f g) h

@[simp]
/-
**MvPolynomial.coe_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eval₂Hom (f : R →+* S₁) (g : σ → S₁) : ⇑(eval₂Hom f g) = eval₂ f g :=
  rfl
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_congr {f₁ f₂ : R →+* S₁} {g₁ g₂ : σ → S₁} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ → g₁ = g₂ → p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl rfl rfl; rfl

end

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_C (f : R →+* S₁) (g : σ → S₁) (r : R) : eval₂Hom f g (C r) = f r :=
  eval₂_C f g r

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_X' (f : R →+* S₁) (g : σ → S₁) (i : σ) : eval₂Hom f g (X i) = g i :=
  eval₂_X f g i

@[simp]
/-
**MvPolynomial.comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) :
    φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f) fun i => φ (g i) := by
  ext <;> simp
/-
**MvPolynomial.map_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ ->+* S₂) (g : σ -> S₁) (p 
: MvPolynomial σ S₁) : q (eval g p) = eval (q ∘ g) (map q p)
参数：q : S₁ ->+* S₂；g : σ -> S₁；p : MvPolynomial σ S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map (g : σ -> S₁) (p : MvP
olynomial σ R) : p.eval₂ f g = eval g (map f p)
· 使用定理 `MvPolynomial.eval₂_id`：eval₂_id {g : σ -> R} (p : MvPolynomial σ R) : ev
al₂ (RingHom.id _) g p = eval g p
· 使用定理 `MvPolynomial.eval₂_comp_right`：eval₂_comp_right {S₂} [CommSemiring S₂] (
k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p) : k (eval₂ f g p) = eval₂ k (k
 ∘ g) (map f p)
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p
-/
theorem map_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = eval₂Hom (φ.comp f) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl
/-
**MvPolynomial.hom_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_eval₂ [CommSemiring S₂] (p : MvPolynomial σ R) (f : R →+* S₁)
    (φ : S₁ →+* S₂) (g : σ → S₁) :
    φ (p.eval₂ f g) = p.eval₂ (φ.comp f) (fun i => φ (g i)) :=
  map_eval₂Hom f g φ p
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_monomial (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    eval₂Hom f g (monomial d r) = f r * d.prod fun i k => g i ^ k := by
  simp only [coe_eval₂Hom, eval₂_monomial]

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_smul (f : R →+* S₁) (g : σ → S₁) (r : R) (P : MvPolynomial σ R) :
    eval₂Hom f g (r • P) = f r • eval₂Hom f g P := by
  simp [smul_eq_C_mul]

section

/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_comp_left {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, k.map_add, eval₂_mul, k.map_mul]

end

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_eta (p : MvPolynomial σ R) : eval₂ C X p = p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, eval₂_mul]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_congr (g₁ g₂ : σ → S₁)
    (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
    p.eval₂ f g₁ = p.eval₂ f g₂ := by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem eval₂_sum (s : Finset S₂) (p : S₂ → MvPolynomial σ R) :
    eval₂ f g (∑ x ∈ s, p x) = ∑ x ∈ s, eval₂ f g (p x) :=
  map_sum (eval₂Hom f g) _ s
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem eval₂_prod (s : Finset S₂) (p : S₂ → MvPolynomial σ R) :
    eval₂ f g (∏ x ∈ s, p x) = ∏ x ∈ s, eval₂ f g (p x) :=
  map_prod (eval₂Hom f g) _ s
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_assoc (q : S₂ → MvPolynomial σ R) (p : MvPolynomial S₂ R) :
    eval₂ f (fun t => eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) := by
  change _ = eval₂Hom f g (eval₂ C q p)
  rw [eval₂_comp_left (eval₂Hom f g)]; congr with a; simp

end Eval₂

section Eval

variable {f : σ → R}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a polynomial `p` given a valuation `f` of all the variables
-/
def eval (f : σ → R) : MvPolynomial σ R →+* R :=
  eval₂Hom (RingHom.id _) f
/-
**MvPolynomial.eval_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_eq (X : σ -> R) (f : MvPolynomial σ R) : eval X f = ∑ d in f.support,
 f.coeff d * ∏ i in d.support, X i ^ d i
参数：X : σ -> R；f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_eq (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i ∈ d.support, X i ^ d i :=
  rfl
/-
**MvPolynomial.eval_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_eq' [Fintype σ] (X : σ -> R) (f : MvPolynomial σ R) : eval X f = ∑ d 
in f.support, f.coeff d * ∏ i, X i ^ d i
参数：X : σ -> R；f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_eq'`：eval₂_eq' [Fintype σ] (g : R ->+* S₁) (X : σ -> 
S₁) (f : MvPolynomial σ R) : f.eval₂ g X = ∑ d in f.support, g (f.coeff d) * ∏ i
, X i ^ d i
-/
theorem eval_eq' [Fintype σ] (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i, X i ^ d i :=
  eval₂_eq' (RingHom.id R) X f
/-
**MvPolynomial.eval_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_monomial : eval f (monomial s a) = a * s.prod fun n e => f n ^ e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_monomial`：eval₂_monomial : (monomial s a).eval₂ f g =
 f a * s.prod fun n e => g n ^ e
-/
theorem eval_monomial : eval f (monomial s a) = a * s.prod fun n e => f n ^ e :=
  eval₂_monomial _ _

@[simp]
/-
**MvPolynomial.eval_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_C : forall a, eval f (C a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
-/
theorem eval_C : ∀ a, eval f (C a) = a :=
  eval₂_C _ _

@[simp]
/-
**MvPolynomial.eval_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_X : forall n, eval f (X n) = f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem eval_X : ∀ n, eval f (X n) = f n :=
  eval₂_X _ _
/-
**MvPolynomial.eval_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R] {f : σ → R} (n : ℕ) 
[inst_1 : n.AtLeastTwo],   (MvPolynomial.eval f) (OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；MvPolynomial.eval f；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
-/
@[simp] theorem eval_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval f = ofNat(n) :=
  map_ofNat _ n

@[simp]
/-
**MvPolynomial.smul_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：smul_eval (x) (p : MvPolynomial σ R) (s) : eval x (s • p) = s * eval x p
参数：x；p : MvPolynomial σ R；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.smul_eq_C_mul`：smul_eq_C_mul (p : MvPolynomial σ R) (a : R)
 : a • p = C a * p
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
-/
theorem smul_eval (x) (p : MvPolynomial σ R) (s) : eval x (s • p) = s * eval x p := by
  rw [smul_eq_C_mul, (eval x).map_mul, eval_C]
/-
**MvPolynomial.eval_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_add : eval f (p + q) = eval f p + eval f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.
eval₂ f g
-/
theorem eval_add : eval f (p + q) = eval f p + eval f q :=
  eval₂_add _ _
/-
**MvPolynomial.eval_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_mul : eval f (p * q) = eval f p * eval f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_mul`：eval₂_mul : forall {p}, (p * q).eval₂ f g = p.ev
al₂ f g * q.eval₂ f g
-/
theorem eval_mul : eval f (p * q) = eval f p * eval f q :=
  eval₂_mul _ _
/-
**MvPolynomial.eval_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_pow : forall n, eval f (p ^ n) = eval f p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_pow`：∀ {R : Type u} {S₁ : Type v} {σ : Type u_1} [ins
t : CommSemiring R] [inst_1 : CommSemiring S₁] (f : R →+* S₁)   (g : σ → S₁) {p 
: MvPolynomi…
-/
theorem eval_pow : ∀ n, eval f (p ^ n) = eval f p ^ n :=
  fun _ => eval₂_pow _ _
/-
**MvPolynomial.eval_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_sum {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> 
R) : eval g (∑ i in s, f i) = ∑ i in s, eval g (f i)
参数：s : Finset ι；f : ι -> MvPolynomial σ R；g : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∑ i ∈ s, f i) = ∑ i ∈ s, eval g (f i) :=
  map_sum (eval g) _ _
/-
**MvPolynomial.eval_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_prod {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ ->
 R) : eval g (∏ i in s, f i) = ∏ i in s, eval g (f i)
参数：s : Finset ι；f : ι -> MvPolynomial σ R；g : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∏ i ∈ s, f i) = ∏ i ∈ s, eval g (f i) :=
  map_prod (eval g) _ _
/-
**MvPolynomial.eval_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_assoc {τ} (f : σ -> MvPolynomial τ R) (g : τ -> R) (p : MvPolynomial 
σ R) : eval (eval g ∘ f) p = eval g (eval₂ C f p)
参数：f : σ -> MvPolynomial τ R；g : τ -> R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.eval₂_comp_left`：eval₂_comp_left {S₂} [CommSemiring S₂] (k 
: S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p) : k (eval₂ f g p) = eval₂ (k.com
p f) (k ∘ g) p
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_assoc {τ} (f : σ → MvPolynomial τ R) (g : τ → R) (p : MvPolynomial σ R) :
    eval (eval g ∘ f) p = eval g (eval₂ C f p) := by
  rw [eval₂_comp_left (eval g)]
  unfold eval; simp only [coe_eval₂Hom]
  congr with a; simp

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_id {g : σ → R} (p : MvPolynomial σ R) : eval₂ (RingHom.id _) g p = eval g p :=
  rfl
/-
**MvPolynomial.eval_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_eval₂ {S τ : Type*} {x : τ → S} [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S) (p : MvPolynomial σ R) :
    eval x (eval₂ f g p) = eval₂ ((eval x).comp f) (fun s => eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

end Eval

section Map

variable (f : R →+* S₁)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
/-
**MvPolynomial.map** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：map : MvPolynomial σ R ->+* MvPolynomial σ S₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map f p` maps a polynomial `p` across a ring hom `f`
-/
def map : MvPolynomial σ R →+* MvPolynomial σ S₁ := AddMonoidAlgebra.mapRingHom _ f

@[simp]
/-
**MvPolynomial.map_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_monomial (s : σ ->₀ Nat) (a : R) : map f (monomial s a) = monomial s (
f a)
参数：s : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.map_single`：∀ {R : Type u_3} {S : Type u_4} {M : Type u
_6} [inst : Semiring R] [inst_1 : Semiring S] (f : R →+ S) (r : R) (m : M),   Ad
dMonoidAlgebra.ma…
-/
theorem map_monomial (s : σ →₀ ℕ) (a : R) : map f (monomial s a) = monomial s (f a) :=
  AddMonoidAlgebra.map_single ..

@[simp]
/-
**MvPolynomial.map_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_C : forall a : R, map f (C a : MvPolynomial σ R) = C (f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_monomial`：map_monomial (s : σ ->₀ Nat) (a : R) : map f 
(monomial s a) = monomial s (f a)
-/
theorem map_C : ∀ a : R, map f (C a : MvPolynomial σ R) = C (f a) :=
  map_monomial _ _
/-
**MvPolynomial.map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {S₁ : Type v} {σ : Type u_1} [inst : CommSemiring R] [inst_
1 : CommSemiring S₁] (f : R →+* S₁) (n : ℕ)   [inst_2 : n.AtLeastTwo], (MvPolyno
mial.map f) (OfNat.ofNat n) = OfNat.ofNat n
参数：f : R →+* S₁；n : ℕ；MvPolynomial.map f；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
-/
@[simp] protected theorem map_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).map f = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
/-
**MvPolynomial.map_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
参数：n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_monomial`：map_monomial (s : σ ->₀ Nat) (a : R) : map f 
(monomial s a) = monomial s (f a)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n := by simp [X]
/-
**MvPolynomial.map_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_id : forall p : MvPolynomial σ R, map (RingHom.id R) p = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.map_id`：∀ {R : Type u_3} {M : Type u_6} [inst : Semirin
g R] (x : AddMonoidAlgebra R M),   AddMonoidAlgebra.map (AddMonoidHom.id R) x = 
x
-/
theorem map_id : ∀ p : MvPolynomial σ R, map (RingHom.id R) p = p := AddMonoidAlgebra.map_id
/-
**MvPolynomial.map_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_map [CommSemiring S₂] (g : S₁ ->+* S₂) (p : MvPolynomial σ R) : map g 
(map f p) = map (g.comp f) p
参数：g : S₁ ->+* S₂；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.map_map`：∀ {R : Type u_3} {S : Type u_4} {T : Type u_5}
 {M : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Semiring T
] (f : S →+ T)…
-/
theorem map_map [CommSemiring S₂] (g : S₁ →+* S₂) (p : MvPolynomial σ R) :
    map g (map f p) = map (g.comp f) p := AddMonoidAlgebra.map_map ..
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_eq_eval_map (g : σ → S₁) (p : MvPolynomial σ R) : p.eval₂ f g = eval g (map f p) := by
  simp [eval₂, eval]; simp [map, MvPolynomial, Finsupp.sum_mapRange_index, mapRingHom]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_comp_right {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, eval₂_C]
  · intro p q hp hq
    rw [eval₂_add, k.map_add, (map f).map_add, eval₂_add, hp, hq]
  · intro p s hp
    rw [eval₂_mul, k.map_mul, (map f).map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X, comp_apply]
/-
**MvPolynomial.map_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ ->+* S₂) (g : σ -> S₁) (p 
: MvPolynomial σ S₁) : q (eval g p) = eval (q ∘ g) (map q p)
参数：q : S₁ ->+* S₂；g : σ -> S₁；p : MvPolynomial σ S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map (g : σ -> S₁) (p : MvP
olynomial σ R) : p.eval₂ f g = eval g (map f p)
· 使用定理 `MvPolynomial.eval₂_id`：eval₂_id {g : σ -> R} (p : MvPolynomial σ R) : ev
al₂ (RingHom.id _) g p = eval g p
· 使用定理 `MvPolynomial.eval₂_comp_right`：eval₂_comp_right {S₂} [CommSemiring S₂] (
k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p) : k (eval₂ f g p) = eval₂ k (k
 ∘ g) (map f p)
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p
-/
theorem map_eval₂ (f : R →+* S₁) (g : S₂ → MvPolynomial S₃ R) (p : MvPolynomial S₂ R) :
    map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, map_C, eval₂_C]
  · intro p q hp hq
    rw [eval₂_add, (map f).map_add, hp, hq, (map f).map_add, eval₂_add]
  · intro p s hp
    rw [eval₂_mul, (map f).map_mul, hp, (map f).map_mul, map_X, eval₂_mul, eval₂_X, eval₂_X,
      comp_apply]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_map_comp_C {ι : Type*} (f : R →+* S₁) (h : ι → MvPolynomial σ S₁)
    (p : MvPolynomial ι R) : eval₂ ((map f).comp C) h p = eval₂ C h (map f p) := by
  induction p using MvPolynomial.induction_on <;> simp_all
/-
**MvPolynomial.map_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ ->+* S₂) (g : σ -> S₁) (p 
: MvPolynomial σ S₁) : q (eval g p) = eval (q ∘ g) (map q p)
参数：q : S₁ ->+* S₂；g : σ -> S₁；p : MvPolynomial σ S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map (g : σ -> S₁) (p : MvP
olynomial σ R) : p.eval₂ f g = eval g (map f p)
· 使用定理 `MvPolynomial.eval₂_id`：eval₂_id {g : σ -> R} (p : MvPolynomial σ R) : ev
al₂ (RingHom.id _) g p = eval g p
· 使用定理 `MvPolynomial.eval₂_comp_right`：eval₂_comp_right {S₂} [CommSemiring S₂] (
k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p) : k (eval₂ f g p) = eval₂ k (k
 ∘ g) (map f p)
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p
-/
lemma map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ →+* S₂) (g : σ → S₁) (p : MvPolynomial σ S₁) :
    q (eval g p) = eval (q ∘ g) (map q p) := by
  rw [← eval₂_eq_eval_map, ← eval₂_id, eval₂_comp_right, map_id]
/-
**MvPolynomial.coeff_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_map (p : MvPolynomial σ R) : forall m : σ ->₀ Nat, coeff m (map f p)
 = f (coeff m p)
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.coeff_mul_X'`：coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p :
 MvPolynomial σ R) : coeff m (p * X s) = if s in m.support then coeff (m - Finsu
pp.single s 1) …
-/
theorem coeff_map (p : MvPolynomial σ R) : ∀ m : σ →₀ ℕ, coeff m (map f p) = f (coeff m p) := by
  classical
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    simp_rw [map_C, coeff_C, apply_ite f, f.map_zero]
  · intro p q hp hq m
    simp only [hp, hq, (map f).map_add, coeff_add, f.map_add]
  · intro p i hp m
    simp only [(map f).map_mul, map_X, hp, coeff_mul_X', f.map_zero, apply_ite f]
/-
**MvPolynomial.map_eq_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_eq_eval₂Hom_C_comp : map (σ := σ) f = eval₂Hom (C.comp f) X := by ext a x <;> simp
/-
**MvPolynomial.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_injective (hf : Function.Injective f) : Function.Injective (map f : Mv
Polynomial σ R -> MvPolynomial σ S₁)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
-/
theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := by
  intro p q h
  simp only [MvPolynomial.ext_iff, coeff_map] at h ⊢
  intro m
  exact hf (h m)
/-
**MvPolynomial.map_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_injective_iff : Function.Injective (map (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
-/
theorem map_injective_iff : Function.Injective (map (σ := σ) f) ↔ Function.Injective f :=
  ⟨fun h r r' eq ↦ by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩
/-
**MvPolynomial.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_surjective (hf : Function.Surjective f) : Function.Surjective (map f :
 MvPolynomial σ R -> MvPolynomial σ S₁)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `MvPolynomial.map_monomial`：map_monomial (s : σ ->₀ Nat) (a : R) : map f 
(monomial s a) = monomial s (f a)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := fun p => by
  induction p using MvPolynomial.induction_on' with
  | monomial i fr =>
    obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, map_monomial _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
/-
**MvPolynomial.map_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_surjective_iff : Function.Surjective (map (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
· 使用定理 `MvPolynomial.map_surjective`：map_surjective (hf : Function.Surjective f)
 : Function.Surjective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
-/
theorem map_surjective_iff : Function.Surjective (map (σ := σ) f) ↔ Function.Surjective f :=
  ⟨fun h s ↦ let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa [coeff_map] using congr(coeff 0 $h)⟩,
    map_surjective f⟩

/-- If `f` is a left-inverse of `g` then `map f` is a left-inverse of `map g`. -/
/-
**MvPolynomial.map_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_leftInverse {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.LeftInverse
 f g) : Function.LeftInverse (map f : MvPolynomial σ R -> MvPolynomial σ S₁) (ma
p g)
参数：hf : Function.LeftInverse f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_map`：map_map [CommSemiring S₂] (g : S₁ ->+* S₂) (p : Mv
Polynomial σ R) : map g (map f p) = map (g.comp f) p
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p

--- 原说明 ---
If `f` is a left-inverse of `g` then `map f` is a left-inverse of `map g`.
-/
theorem map_leftInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) := fun X => by
  rw [map_map, (RingHom.ext hf : f.comp g = RingHom.id _), map_id]

/-- If `f` is a right-inverse of `g` then `map f` is a right-inverse of `map g`. -/
/-
**MvPolynomial.map_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_rightInverse {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.RightInver
se f g) : Function.RightInverse (map f : MvPolynomial σ R -> MvPolynomial σ S₁) 
(map g)
参数：hf : Function.RightInverse f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInverse`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β} {g : β → α}, Function.LeftInverse g f → Function.RightInverse f g
· 使用定理 `MvPolynomial.map_leftInverse`：map_leftInverse {f : R ->+* S₁} {g : S₁ ->
+* R} (hf : Function.LeftInverse f g) : Function.LeftInverse (map f : MvPolynomi
al σ R -> MvPolyno…
· 使用定理 `Function.RightInverse.leftInverse`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β} {g : β → α}, Function.RightInverse g f → Function.LeftInverse f g

--- 原说明 ---
If `f` is a right-inverse of `g` then `map f` is a right-inverse of `map g`.
-/
theorem map_rightInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.RightInverse f g) :
    Function.RightInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) :=
  (map_leftInverse hf.leftInverse).rightInverse

@[simp]
/-
**MvPolynomial.eval_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_map (f : R ->+* S₁) (g : σ -> S₁) (p : MvPolynomial σ R) : eval g (ma
p f p) = eval₂ f g p
参数：f : R ->+* S₁；g : σ -> S₁；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.
eval₂ f g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `MvPolynomial.eval₂_mul`：eval₂_mul : forall {p}, (p * q).eval₂ f g = p.ev
al₂ f g * q.eval₂ f g
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem eval_map (f : R →+* S₁) (g : σ → S₁) (p : MvPolynomial σ R) :
    eval g (map f p) = eval₂ f g p := by
  apply MvPolynomial.induction_on p <;> · simp +contextual
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_comp (f : R →+* S₁) (g : σ → R) (p : MvPolynomial σ R) :
    f (eval g p) = eval₂ f (f ∘ g) p := by
  rw [← p.map_id, eval_map, eval₂_comp_right]

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_map [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : eval₂ φ g (map f p) = eval₂ (φ.comp f) g p := by
  rw [← eval_map, ← eval_map, map_map]

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_map_hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : eval₂Hom φ g (map f p) = eval₂Hom (φ.comp f) g p :=
  eval₂_map f g φ p

@[simp]
/-
**MvPolynomial.constantCoeff_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_map (f : R ->+* S₁) (φ : MvPolynomial σ R) : constantCoeff (
MvPolynomial.map f φ) = f (constantCoeff φ)
参数：f : R ->+* S₁；φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
-/
theorem constantCoeff_map (f : R →+* S₁) (φ : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ) :=
  coeff_map f φ 0
/-
**MvPolynomial.constantCoeff_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：constantCoeff_comp_map (f : R ->+* S₁) : (constantCoeff : MvPolynomial σ S
₁ ->+* S₁).comp (MvPolynomial.map f) = f.comp constantCoeff
参数：f : R ->+* S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.constantCoeff_C`：constantCoeff_C (r : R) : constantCoeff (C
 r : MvPolynomial σ R) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem constantCoeff_comp_map (f : R →+* S₁) :
    (constantCoeff : MvPolynomial σ S₁ →+* S₁).comp (MvPolynomial.map f) =
      f.comp constantCoeff := by
  ext <;> simp
/-
**MvPolynomial.support_map_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_map_subset (p : MvPolynomial σ R) : (map f p).support subseteq p.s
upport
参数：p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem support_map_subset (p : MvPolynomial σ R) : (map f p).support ⊆ p.support := by
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map, hx, map_zero]
/-
**MvPolynomial.support_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：support_map_of_injective (p : MvPolynomial σ R) {f : R ->+* S₁} (hf : Inje
ctive f) : (map f p).support = p.support
参数：p : MvPolynomial σ R；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `MvPolynomial.support_map_subset`：support_map_subset (p : MvPolynomial σ 
R) : (map f p).support subseteq p.support
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
-/
theorem support_map_of_injective (p : MvPolynomial σ R) {f : R →+* S₁} (hf : Injective f) :
    (map f p).support = p.support := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_map_subset _ _
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map, ← f.map_zero] at hx
  exact hf hx
/-
**MvPolynomial.C_dvd_iff_map_hom_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：C_dvd_iff_map_hom_eq_zero (q : R ->+* S₁) (r : R) (hr : forall r' : R, q r
' = 0 ↔ r ∣ r') (φ : MvPolynomial σ R) : C r ∣ φ ↔ map q φ = 0
参数：q : R ->+* S₁；r : R；hr : forall r' : R, q r' = 0 ↔ r ∣ r'；φ : MvPolynomial σ 
R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.C_dvd_iff_dvd_coeff`：C_dvd_iff_dvd_coeff (r : R) (φ : MvPol
ynomial σ R) : C r ∣ φ ↔ forall i, r ∣ φ.coeff i
· 使用定理 `MvPolynomial.ext_iff`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring
 R] {p q : MvPolynomial σ R},   p = q ↔ ∀ (m : σ →₀ ℕ), MvPolynomial.coeff m p =
 MvPolynom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem C_dvd_iff_map_hom_eq_zero (q : R →+* S₁) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
    (φ : MvPolynomial σ R) : C r ∣ φ ↔ map q φ = 0 := by
  rw [C_dvd_iff_dvd_coeff, MvPolynomial.ext_iff]
  simp only [coeff_map, coeff_zero, hr]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.map_mapRange_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_mapRange_eq_iff (f : R ->+* S₁) (g : S₁ -> R) (hg : g 0 = 0) (φ : MvPo
lynomial σ S₁) : map f (.ofCoeff <| Finsupp.mapRange g hg <| AddMonoidAlgebra.co
eff φ) = φ ↔ forall d, f (g (coeff d φ)) = coeff d φ
参数：f : R ->+* S₁；g : S₁ -> R；hg : g 0 = 0；φ : MvPolynomial σ S₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_mapRange_eq_iff (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) :
    map f (.ofCoeff <| Finsupp.mapRange g hg <| AddMonoidAlgebra.coeff φ) = φ ↔
      ∀ d, f (g (coeff d φ)) = coeff d φ := by
  simp_rw [MvPolynomial.ext_iff, coeff_map]; rfl
/-
**MvPolynomial.coeffs_map** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coeffs_map (f : R ->+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁] : (map 
f p).coeffs subseteq p.coeffs.image f
参数：f : R ->+* S₁；p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on''`：induction_on'' {motive : MvPolynomial σ R -
> Prop} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (monomial_add : fora
ll (a : σ ->₀ Nat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用引理 `MvPolynomial.coeffs_C`：coeffs_C [DecidableEq R] (r : R) : (C (σ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPolynomial.coeffs_add`：coeffs_add [DecidableEq R] {p q : MvPolynomial 
σ R} (h : Disjoint p.support q.support) : (p + q).coeffs = p.coeffs union q.coef
fs
· 使用引理 `MvPolynomial.disjoint_support_monomial`：disjoint_support_monomial {a : σ
 ->₀ Nat} {p : MvPolynomial σ R} {s : R} (ha : a ∉ p.support) (hs : s != 0) : Di
sjoint (monomial a s).suppor…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq 
u) (d : Disjoint u t) : Disjoint s t
· 使用定理 `MvPolynomial.support_map_subset`：support_map_subset (p : MvPolynomial σ 
R) : (map f p).support subseteq p.support
· 使用定理 `Finset.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subsete
q u) (d : Disjoint s u) : Disjoint s t
· 使用定理 `Finset.image_union`：image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Fi
nset α) : (s₁ union s₂).image f = s₁.image f union s₂.image f
· 使用定理 `Finset.union_subset_iff`：union_subset_iff : s union t subseteq u ↔ s sub
seteq u ∧ t subseteq u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
（共 33 条，此处仅展示前 30 条）
-/
lemma coeffs_map (f : R →+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁] :
    (map f p).coeffs ⊆ p.coeffs.image f := by
  classical
  induction p using induction_on'' with
  | C a => aesop (add simp coeffs_C)
  | mul_X p n ih => simpa
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add (disjoint_support_monomial ha hs), map_add, coeffs_add]
    · rw [Finset.image_union, Finset.union_subset_iff]
      exact ⟨ih.trans (by simp), hp.trans (by simp)⟩
    · exact Finset.disjoint_of_subset_left (support_map_subset _ _) <|
        Finset.disjoint_of_subset_right (support_map_subset _ _) <|
          disjoint_support_monomial ha hs

@[simp]
/-
**MvPolynomial.coe_coeffs_map** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_coeffs_map (f : R ->+* S₁) (p : MvPolynomial σ R) : ((map f p).coeffs 
: Set S₁) subseteq f '' p.coeffs
参数：f : R ->+* S₁；p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `MvPolynomial.coeffs_map`：coeffs_map (f : R ->+* S₁) (p : MvPolynomial σ 
R) [DecidableEq S₁] : (map f p).coeffs subseteq p.coeffs.image f
-/
lemma coe_coeffs_map (f : R →+* S₁) (p : MvPolynomial σ R) :
    ((map f p).coeffs : Set S₁) ⊆ f '' p.coeffs := by
  classical
  exact mod_cast coeffs_map f p
/-
**MvPolynomial.mem_range_map_iff_coeffs_subset** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：mem_range_map_iff_coeffs_subset {f : R ->+* S₁} {x : MvPolynomial σ S₁} : 
x in Set.range (MvPolynomial.map f) ↔ (x.coeffs : Set _) subseteq .range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `MvPolynomial.coe_coeffs_map`：coe_coeffs_map (f : R ->+* S₁) (p : MvPolyn
omial σ R) : ((map f p).coeffs : Set S₁) subseteq f '' p.coeffs
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `MvPolynomial.induction_on''`：induction_on'' {motive : MvPolynomial σ R -
> Prop} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (monomial_add : fora
ll (a : σ ->₀ Nat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.coeffs_C`：coeffs_C [DecidableEq R] (r : R) : (C (σ
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用引理 `MvPolynomial.coeffs_add`：coeffs_add [DecidableEq R] {p q : MvPolynomial 
σ R} (h : Disjoint p.support q.support) : (p + q).coeffs = p.coeffs union q.coef
fs
· 使用引理 `MvPolynomial.disjoint_support_monomial`：disjoint_support_monomial {a : σ
 ->₀ Nat} {p : MvPolynomial σ R} {s : R} (ha : a ∉ p.support) (hs : s != 0) : Di
sjoint (monomial a s).suppor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `MvPolynomial.coeffs_mul_X`：coeffs_mul_X (p : MvPolynomial σ R) (n : σ) :
 (p * X n).coeffs = p.coeffs
（共 34 条，此处仅展示前 30 条）
-/
lemma mem_range_map_iff_coeffs_subset {f : R →+* S₁} {x : MvPolynomial σ S₁} :
    x ∈ Set.range (MvPolynomial.map f) ↔ (x.coeffs : Set _) ⊆ .range f := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := hx
    exact subset_trans (coe_coeffs_map f p) (by simp)
  · induction x using induction_on'' with
    | C a =>
      by_cases h : a = 0
      · subst h
        exact ⟨0, by simp⟩
      · simp only [coeffs_C, h, reduceIte, Finset.coe_singleton, Set.singleton_subset_iff] at hx
        obtain ⟨b, rfl⟩ := hx
        exact ⟨C b, by simp⟩
    | mul_X p n ih =>
      rw [coeffs_mul_X] at hx
      obtain ⟨q, rfl⟩ := ih hx
      exact ⟨q * X n, by simp⟩
    | monomial_add a s p ha hs hp ih =>
      rw [coeffs_add (disjoint_support_monomial ha hs)] at hx
      simp only [Finset.coe_union, Set.union_subset_iff] at hx
      obtain ⟨q, hq⟩ := ih hx.1
      obtain ⟨u, hu⟩ := hp hx.2
      exact ⟨q + u, by simp [hq, hu]⟩

section Algebra

variable [Algebra R S₁] (g : σ → S₁)

variable (R) in
/-- `MvPolynomial.eval₂ (algebraMap R S) g` as an `R`-algebra homomorphism. -/
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.eval₂ (algebraMap R S) g` as an `R`-algebra homomorphism.
-/
def eval₂AlgHom : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) g with
    commutes' r := by simp }
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂AlgHom_apply (P : MvPolynomial σ R) :
    eval₂AlgHom R g P = eval₂Hom (algebraMap R S₁) g P := rfl

@[simp]
/-
**MvPolynomial.coe_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eval₂AlgHom : ⇑(eval₂AlgHom R g) = eval₂ (algebraMap R S₁) g := rfl

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂AlgHom_X (i : σ) :
    eval₂AlgHom R g (X i : MvPolynomial σ R) = g i := eval₂_X (algebraMap R S₁) g i

end Algebra

/-- If `f : S₁ →ₐ[R] S₂` is a morphism of `R`-algebras, then so is `MvPolynomial.map f`. -/
/-
**MvPolynomial.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S
₂) : MvPolynomial σ S₁ ->ₐ[R] MvPolynomial σ S₂
参数：f : S₁ ->ₐ[R] S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : S₁ →ₐ[R] S₂` is a morphism of `R`-algebras, then so is `MvPolynomial.map
 f`.
-/
def mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    MvPolynomial σ S₁ →ₐ[R] MvPolynomial σ S₂ := AddMonoidAlgebra.mapAlgHom _ f

@[simp]
/-
**MvPolynomial.mapAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgHom_apply [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->
ₐ[R] S₂) (x : MvPolynomial σ S₁) : mapAlgHom f x = map f x
参数：f : S₁ ->ₐ[R] S₂；x : MvPolynomial σ S₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAlgHom_apply [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂)
    (x : MvPolynomial σ S₁) : mapAlgHom f x = map f x := rfl

@[simp]
/-
**MvPolynomial.mapAlgHom_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgHom_id [Algebra R S₁] : mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (Mv
Polynomial σ S₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MvPolynomial.map_id`：map_id : forall p : MvPolynomial σ R, map (RingHom.
id R) p = p
-/
theorem mapAlgHom_id [Algebra R S₁] :
    mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (MvPolynomial σ S₁) :=
  AlgHom.ext map_id

@[simp]
/-
**MvPolynomial.mapAlgHom_coe_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mapAlgHom_coe_ringHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f :
 S₁ ->ₐ[R] S₂) : ↑(mapAlgHom f : _ ->ₐ[R] MvPolynomial σ S₂) = (map ↑f : MvPolyn
omial σ S₁ ->+* MvPolynomial σ S₂)
参数：f : S₁ ->ₐ[R] S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.mk_coe`：mk_coe (f : α ->+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁
⟩, h₂⟩ h₃ h₄ = f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem mapAlgHom_coe_ringHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    ↑(mapAlgHom f : _ →ₐ[R] MvPolynomial σ S₂) =
      (map ↑f : MvPolynomial σ S₁ →+* MvPolynomial σ S₂) :=
  RingHom.mk_coe _ _ _ _ _
/-
**MvPolynomial.range_mapAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：range_mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->
ₐ[R] S₂) : (mapAlgHom f).range.toSubmodule = coeffsIn σ f.range.toSubmodule
参数：f : S₁ ->ₐ[R] S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `MvPolynomial.mem_range_map_iff_coeffs_subset`：mem_range_map_iff_coeffs_s
ubset {f : R ->+* S₁} {x : MvPolynomial σ S₁} : x in Set.range (MvPolynomial.map
 f) ↔ (x.coeffs : Set _) subseteq …
· 使用引理 `MvPolynomial.mem_coeffsIn_iff_coeffs_subset`：mem_coeffsIn_iff_coeffs_sub
set : p in coeffsIn σ M ↔ (p.coeffs : Set S) subseteq M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    (mapAlgHom f).range.toSubmodule = coeffsIn σ f.range.toSubmodule := by
  simp only [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range]
  ext
  erw [mem_range_map_iff_coeffs_subset, mem_coeffsIn_iff_coeffs_subset]
  simp [Set.subset_def]

end Map

section Aeval

/-! ### The algebra of multivariate polynomials -/


variable [Algebra R S₁] [CommSemiring S₂]
variable (f : σ → S₁)

/-- A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism
from multivariate polynomials over `σ` to `S₁`. -/
/-
**MvPolynomial.aeval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：aeval : MvPolynomial σ R ->ₐ[R] S₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomo
rphism
from multivariate polynomials over `σ` to `S₁`.
-/
def aeval : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }
/-
**MvPolynomial.aeval_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p :=
  rfl
/-
**MvPolynomial.aeval_eq_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_eq_eval : (aeval f : MvPolynomial σ S₁ -> S₁) = eval f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_eq_eval₂Hom (p : MvPolynomial σ R) : aeval f p = eval₂Hom (algebraMap R S₁) f p :=
  rfl

@[simp]
/-
**MvPolynomial.coe_aeval_eq_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_aeval_eq_eval : RingHomClass.toRingHom (aeval f : MvPolynomial σ S₁ ->
ₐ[S₁] S₁) = eval f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma coe_aeval_eq_eval :
    RingHomClass.toRingHom (aeval f : MvPolynomial σ S₁ →ₐ[S₁] S₁) = eval f :=
  rfl

@[simp]
/-
**MvPolynomial.aeval_eq_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_eq_eval : (aeval f : MvPolynomial σ S₁ -> S₁) = eval f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aeval_eq_eval : (aeval f : MvPolynomial σ S₁ → S₁) = eval f := rfl

@[simp]
/-
**MvPolynomial.aeval_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R) = f s
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R) = f s :=
  eval₂_X _ _ _
/-
**MvPolynomial.aeval_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
-/
theorem aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ r :=
  eval₂_C _ _ _
/-
**MvPolynomial.aeval_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {S₁ : Type v} {σ : Type u_1} [inst : CommSemiring R] [inst_
1 : CommSemiring S₁] [inst_2 : Algebra R S₁]   (f : σ → S₁) (n : ℕ) [inst_3 : n.
AtLeastTwo], (MvPolynomial.aeval f) (OfNat.ofNat n) = OfNat.ofNat n
参数：f : σ → S₁；n : ℕ；MvPolynomial.aeval f；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
@[simp] theorem aeval_ofNat (n : Nat) [n.AtLeastTwo] :
    aeval f (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  map_ofNat _ _
/-
**MvPolynomial.aeval_unique** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_unique (φ : MvPolynomial σ R ->ₐ[R] S₁) : φ = aeval (φ ∘ X)
参数：φ : MvPolynomial σ R ->ₐ[R] S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_unique (φ : MvPolynomial σ R →ₐ[R] S₁) : φ = aeval (φ ∘ X) := by
  ext i
  simp
/-
**MvPolynomial.aeval_X_left** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_X_left : aeval X = AlgHom.id R (MvPolynomial σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.aeval_unique`：aeval_unique (φ : MvPolynomial σ R ->ₐ[R] S₁)
 : φ = aeval (φ ∘ X)
-/
theorem aeval_X_left : aeval X = AlgHom.id R (MvPolynomial σ R) :=
  (aeval_unique (AlgHom.id R _)).symm
/-
**MvPolynomial.aeval_X_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_X_left_apply (p : MvPolynomial σ R) : aeval X p = p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `MvPolynomial.aeval_X_left`：aeval_X_left : aeval X = AlgHom.id R (MvPolyn
omial σ R)
-/
theorem aeval_X_left_apply (p : MvPolynomial σ R) : aeval X p = p :=
  AlgHom.congr_fun aeval_X_left p
/-
**MvPolynomial.comp_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comp_aeval {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B) : 
φ.comp (aeval f) = aeval fun i => φ (f i)
参数：φ : S₁ ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_aeval {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B) :
    φ.comp (aeval f) = aeval fun i => φ (f i) := by
  ext i
  simp
/-
**MvPolynomial.comp_aeval_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：comp_aeval_apply {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R]
 B) (p : MvPolynomial σ R) : φ (aeval f p) = aeval (fun i => φ (f i)) p
参数：φ : S₁ ->ₐ[R] B；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.comp_aeval`：comp_aeval {B : Type*} [CommSemiring B] [Algebr
a R B] (φ : S₁ ->ₐ[R] B) : φ.comp (aeval f) = aeval fun i => φ (f i)
· 使用定理 `AlgHom.coe_comp`：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.com
p φ₂) = φ₁ ∘ φ₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma comp_aeval_apply {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B)
    (p : MvPolynomial σ R) :
    φ (aeval f p) = aeval (fun i ↦ φ (f i)) p := by
  rw [← comp_aeval, AlgHom.coe_comp, comp_apply]

@[simp]
/-
**MvPolynomial.map_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_aeval {B : Type*} [CommSemiring B] (g : σ -> S₁) (φ : S₁ ->+* B) (p : 
MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (algebraMap R S₁)) (fun i =
> φ (g i)) p
参数：g : σ -> S₁；φ : S₁ ->+* B；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.comp_eval₂Hom`：comp_eval₂Hom [CommSemiring S₂] (f : R ->+* 
S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂) : φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f)
 fun i => φ (g i…
-/
theorem map_aeval {B : Type*} [CommSemiring B] (g : σ → S₁) (φ : S₁ →+* B) (p : MvPolynomial σ R) :
    φ (aeval g p) = eval₂Hom (φ.comp (algebraMap R S₁)) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl
/-
**MvPolynomial.aeval_range** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_range : (aeval f).range = Algebra.adjoin R (Set.range f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
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
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_range : (aeval f).range = Algebra.adjoin R (Set.range f) := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | C a => exact aeval_C f a ▸ Subsemiring.subset_closure (Or.inl (Set.mem_range_self a))
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p n h =>
      simp only [map_mul, aeval_X]
      exact Subalgebra.mul_mem _ h (Algebra.subset_adjoin (Set.mem_range_self n))
  · rw [Algebra.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    use X i, by aesop

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_zero (f : R →+* S₂) : eval₂Hom f (0 : σ → S₂) = f.comp constantCoeff := by
  ext <;> simp

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_zero' (f : R →+* S₂) : eval₂Hom f (fun _ => 0 : σ → S₂) = f.comp constantCoeff :=
  eval₂Hom_zero f
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_zero_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (0 : σ → S₂) p = f (constantCoeff p) :=
  RingHom.congr_fun (eval₂Hom_zero f) p
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂Hom_zero_apply f p

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_zero_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂Hom_zero_apply _ _

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂_zero_apply f p

@[simp]
/-
**MvPolynomial.aeval_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_zero (p : MvPolynomial σ R) : aeval (0 : σ -> S₁) p = algebraMap _ _
 (constantCoeff p)
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_zero_apply`：eval₂Hom_zero_apply (f : R ->+* S₂) (p
 : MvPolynomial σ R) : eval₂Hom f (0 : σ -> S₂) p = f (constantCoeff p)
-/
theorem aeval_zero (p : MvPolynomial σ R) :
    aeval (0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_zero_apply (algebraMap R S₁) p

@[simp]
/-
**MvPolynomial.aeval_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_zero' (p : MvPolynomial σ R) : aeval (fun _ => 0 : σ -> S₁) p = alge
braMap _ _ (constantCoeff p)
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.aeval_zero`：aeval_zero (p : MvPolynomial σ R) : aeval (0 : 
σ -> S₁) p = algebraMap _ _ (constantCoeff p)
-/
theorem aeval_zero' (p : MvPolynomial σ R) :
    aeval (fun _ => 0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  aeval_zero p

@[simp]
/-
**MvPolynomial.eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_zero : eval (0 : σ -> R) = constantCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_zero`：eval₂Hom_zero (f : R ->+* S₂) : eval₂Hom f (
0 : σ -> S₂) = f.comp constantCoeff
-/
theorem eval_zero : eval (0 : σ → R) = constantCoeff :=
  eval₂Hom_zero _

@[simp]
/-
**MvPolynomial.eval_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_zero' : eval (fun _ => 0 : σ -> R) = constantCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_zero`：eval₂Hom_zero (f : R ->+* S₂) : eval₂Hom f (
0 : σ -> S₂) = f.comp constantCoeff
-/
theorem eval_zero' : eval (fun _ => 0 : σ → R) = constantCoeff :=
  eval₂Hom_zero _
/-
**MvPolynomial.aeval_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat) (r : R) : aeval g (monomial d
 r) = algebraMap _ _ r * d.prod fun i k => g i ^ k
参数：g : σ -> S₁；d : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_monomial`：eval₂Hom_monomial (f : R ->+* S₁) (g : σ
 -> S₁) (d : σ ->₀ Nat) (r : R) : eval₂Hom f g (monomial d r) = f r * d.prod fun
 i k => g i ^ k
-/
theorem aeval_monomial (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ k :=
  eval₂Hom_monomial _ _ _ _
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_eq_zero (f : R →+* S₂) (g : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, g i = 0) : eval₂Hom f g φ = 0 := by
  rw [φ.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨i, hi, hgi⟩ : ∃ i ∈ d.support, g i = 0 := h d (Finsupp.mem_support_iff.mp hd)
  rw [eval₂Hom_monomial, Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
  rw [hgi, zero_pow]
  rwa [← Finsupp.mem_support_iff]
/-
**MvPolynomial.aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_eq_zero [Algebra R S₂] (f : σ -> S₂) (φ : MvPolynomial σ R) (h : for
all d, φ.coeff d != 0 -> exists i in d.support, f i = 0) : aeval f φ = 0
参数：f : σ -> S₂；φ : MvPolynomial σ R；h : forall d, φ.coeff d != 0 -> exists i in 
d.support, f i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_eq_zero`：eval₂Hom_eq_zero (f : R ->+* S₂) (g : σ -
> S₂) (φ : MvPolynomial σ R) (h : forall d, φ.coeff d != 0 -> exists i in d.supp
ort, g i = 0) : eva…
-/
theorem aeval_eq_zero [Algebra R S₂] (f : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, f i = 0) : aeval f φ = 0 :=
  eval₂Hom_eq_zero _ _ _ h
/-
**MvPolynomial.aeval_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_sum {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) : aeval f
 (∑ i in s, φ i) = ∑ i in s, aeval f (φ i)
参数：s : Finset ι；φ : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem aeval_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∑ i ∈ s, φ i) = ∑ i ∈ s, aeval f (φ i) :=
  map_sum (MvPolynomial.aeval f) _ _
/-
**MvPolynomial.aeval_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_prod {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) : aeval 
f (∏ i in s, φ i) = ∏ i in s, aeval f (φ i)
参数：s : Finset ι；φ : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem aeval_prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∏ i ∈ s, φ i) = ∏ i ∈ s, aeval f (φ i) :=
  map_prod (MvPolynomial.aeval f) _ _

variable (R)
/-
**MvPolynomial._root_.Algebra.adjoin_range_eq_range_aeval** 是 Mathlib 中的一个定理，位于命
名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.adjoin_range_eq_range_aeval :
    Algebra.adjoin R (Set.range f) = (MvPolynomial.aeval f).range := by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]
/-
**MvPolynomial._root_.Algebra.adjoin_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.adjoin_eq_range (s : Set S₁) :
    Algebra.adjoin R s = (MvPolynomial.aeval ((↑) : s → S₁)).range := by
  rw [← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe]

end Aeval

section AevalTower

variable {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
variable [Algebra S R] [Algebra S A] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `MvPolynomial σ R` over a smaller base ring
  than `R`. -/
/-
**MvPolynomial.aevalTower** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower (f : R ->ₐ[S] A) (X : σ -> A) : MvPolynomial σ R ->ₐ[S] A
参数：f : R ->ₐ[S] A；X : σ -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `aeval` for defining algebra homs out of `MvPolynomial σ R` over a sm
aller base ring
  than `R`.
-/
def aevalTower (f : R →ₐ[S] A) (X : σ → A) : MvPolynomial σ R →ₐ[S] A :=
  { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }

variable (g : R →ₐ[S] A) (y : σ → A)

@[simp]
/-
**MvPolynomial.aevalTower_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_X (i : σ) : aevalTower g y (X i) = y i
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
-/
theorem aevalTower_X (i : σ) : aevalTower g y (X i) = y i :=
  eval₂_X _ _ _

@[simp]
/-
**MvPolynomial.aevalTower_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_C (x : R) : aevalTower g y (C x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
-/
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _ _

@[simp]
/-
**MvPolynomial.aevalTower_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_ofNat (n : Nat) [n.AtLeastTwo] : aevalTower g y (ofNat(n) : MvP
olynomial σ R) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem aevalTower_ofNat (n : Nat) [n.AtLeastTwo] :
    aevalTower g y (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
/-
**MvPolynomial.aevalTower_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_comp_C : (aevalTower g y : MvPolynomial σ R ->+* A).comp C = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.aevalTower_C`：aevalTower_C (x : R) : aevalTower g y (C x) =
 g x
-/
theorem aevalTower_comp_C : (aevalTower g y : MvPolynomial σ R →+* A).comp C = g :=
  RingHom.ext <| aevalTower_C _ _
/-
**MvPolynomial.aevalTower_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R (MvPolynomial
 σ R) x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
-/
theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x :=
  eval₂_C _ _ _
/-
**MvPolynomial.aevalTower_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：aevalTower_comp_algebraMap : (aevalTower g y : MvPolynomial σ R ->+* A).co
mp (algebraMap R (MvPolynomial σ R)) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.aevalTower_comp_C`：aevalTower_comp_C : (aevalTower g y : Mv
Polynomial σ R ->+* A).comp C = g
-/
theorem aevalTower_comp_algebraMap :
    (aevalTower g y : MvPolynomial σ R →+* A).comp (algebraMap R (MvPolynomial σ R)) = g :=
  aevalTower_comp_C _ _
/-
**MvPolynomial.aevalTower_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R (
MvPolynomial σ R) x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.aevalTower_algebraMap`：aevalTower_algebraMap (x : R) : aeva
lTower g y (algebraMap R (MvPolynomial σ R) x) = g x
-/
theorem aevalTower_toAlgHom (x : R) :
    aevalTower g y (IsScalarTower.toAlgHom S R (MvPolynomial σ R) x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
/-
**MvPolynomial.aevalTower_comp_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S
 R (MvPolynomial σ R)) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.aevalTower_comp_algebraMap`：aevalTower_comp_algebraMap : (a
evalTower g y : MvPolynomial σ R ->+* A).comp (algebraMap R (MvPolynomial σ R)) 
= g
-/
theorem aevalTower_comp_toAlgHom :
    (aevalTower g y).comp (IsScalarTower.toAlgHom S R (MvPolynomial σ R)) = g :=
  AlgHom.coe_ringHom_injective <| aevalTower_comp_algebraMap _ _

@[simp]
/-
**MvPolynomial.aevalTower_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_id : aevalTower (AlgHom.id S S) = (aeval : (σ -> S) -> MvPolyno
mial σ S ->ₐ[S] S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aevalTower_X`：aevalTower_X (i : σ) : aevalTower g y (X i) =
 y i
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aevalTower_id :
    aevalTower (AlgHom.id S S) = (aeval : (σ → S) → MvPolynomial σ S →ₐ[S] S) := by
  ext
  simp only [aevalTower_X, aeval_X]

@[simp]
/-
**MvPolynomial.aevalTower_ofId** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aevalTower_ofId : aevalTower (Algebra.ofId S A) = (aeval : (σ -> A) -> MvP
olynomial σ S ->ₐ[S] A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aevalTower_X`：aevalTower_X (i : σ) : aevalTower g y (X i) =
 y i
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aevalTower_ofId :
    aevalTower (Algebra.ofId S A) = (aeval : (σ → A) → MvPolynomial σ S →ₐ[S] A) := by
  ext
  simp only [aeval_X, aevalTower_X]

end AevalTower

section EvalMem

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_mem {f : R →+* S} {p : MvPolynomial σ R} {s : subS}
    (hs : ∀ i ∈ p.support, f (p.coeff i) ∈ s) {v : σ → S} (hv : ∀ i, v i ∈ s) :
    MvPolynomial.eval₂ f v p ∈ s := by
  classical
  replace hs : ∀ i, f (p.coeff i) ∈ s := by
    intro i
    by_cases hi : i ∈ p.support
    · exact hs i hi
    · rw [MvPolynomial.notMem_support_iff.1 hi, f.map_zero]
      exact zero_mem s
  induction p using MvPolynomial.monomial_add_induction_on with
  | C a =>
    simpa using hs 0
  | monomial_add a b f ha _ ih =>
    rw [eval₂_add, eval₂_monomial]
    refine add_mem (mul_mem ?_ <| prod_mem fun i _ => pow_mem (hv _) _) (ih fun i => ?_)
    · simpa [MvPolynomial.notMem_support_iff.1 ha] using hs a
    have := hs i
    rw [coeff_add, coeff_monomial] at this
    split_ifs at this with h
    · subst h
      rw [MvPolynomial.notMem_support_iff.1 ha, map_zero]
      exact zero_mem _
    · rwa [zero_add] at this
/-
**MvPolynomial.eval_mem** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_mem {p : MvPolynomial σ S} {s : subS} (hs : forall i in p.support, p.
coeff i in s) {v : σ -> S} (hv : forall i, v i in s) : MvPolynomial.eval v p in 
s
参数：hs : forall i in p.support, p.coeff i in s；hv : forall i, v i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_mem`：eval₂_mem {f : R ->+* S} {p : MvPolynomial σ R} 
{s : subS} (hs : forall i in p.support, f (p.coeff i) in s) {v : σ -> S} (hv : f
orall i, v i…
-/
theorem eval_mem {p : MvPolynomial σ S} {s : subS} (hs : ∀ i ∈ p.support, p.coeff i ∈ s) {v : σ → S}
    (hv : ∀ i, v i ∈ s) : MvPolynomial.eval v p ∈ s :=
  eval₂_mem hs hv

end EvalMem

variable {S T : Type*} [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

/-
**MvPolynomial.aeval_sumElim** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_sumElim {σ τ : Type*} (p : MvPolynomial (σ oplus τ) R) (f : τ -> S) 
(g : σ -> T) : (aeval (Sum.elim g (algebraMap S T ∘ f))) p = (aeval g) ((aeval (
Sum.elim X (C ∘ f))) p)
参数：p : MvPolynomial (σ oplus τ) R；f : τ -> S；g : σ -> T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma aeval_sumElim {σ τ : Type*} (p : MvPolynomial (σ ⊕ τ) R) (f : τ → S) (g : σ → T) :
    (aeval (Sum.elim g (algebraMap S T ∘ f))) p =
      (aeval g) ((aeval (Sum.elim X (C ∘ f))) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [← IsScalarTower.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i h => cases i <;> simp [h]

end CommSemiring

section Algebra

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

open scoped AlgebraMonoidAlgebra in
/--
If `S` is an `R`-algebra, then `MvPolynomial σ S` is a `MvPolynomial σ R` algebra.

Warning: This produces a diamond for
`Algebra (MvPolynomial σ R) (MvPolynomial σ (MvPolynomial σ S))`. That's why it is not a
global instance.
-/
@[instance_reducible]
/-
**MvPolynomial.algebraMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPolynomial σ S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an `R`-algebra, then `MvPolynomial σ S` is a `MvPolynomial σ R` algebr
a.

Warning: This produces a diamond for
`Algebra (MvPolynomial σ R) (MvPolynomial σ (MvPolynomial σ S))`. That's why it 
is not a
global instance.
-/
noncomputable def algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPolynomial σ S) :=
  inferInstanceAs <| Algebra (AddMonoidAlgebra _ _) (AddMonoidAlgebra _ _)

attribute [local instance] algebraMvPolynomial

-- We want this to have higher priority than `AddMonoidAlgebra.algebraMap_def`.
-- TODO: Unify `MvPolynomial.map` and `AddMonoidAlgebra.mapRingHom` so that this becomes useless.
@[simp high]
/-
**MvPolynomial.algebraMap_def** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：algebraMap_def : algebraMap (MvPolynomial σ R) (MvPolynomial σ S) = MvPoly
nomial.map (algebraMap R S)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_def :
    algebraMap (MvPolynomial σ R) (MvPolynomial σ S) = MvPolynomial.map (algebraMap R S) :=
  rfl
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ S) :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp [C, monomial, map])
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FaithfulSMul R S] : FaithfulSMul (MvPolynomial σ R) (MvPolynomial σ S) :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

end Algebra

end MvPolynomial

