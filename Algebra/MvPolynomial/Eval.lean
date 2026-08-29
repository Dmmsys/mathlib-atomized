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

variable {σ : Type*} {a a' a₁ a₂ : R} {e : Nat} {n m : σ} {s : σ ->₀ Nat}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

section Eval₂

variable (f : R ->+* S₁) (g : σ -> S₁)

/--
Definition of `eval₂` / `eval₂` 的定义

English:
definition eval₂
  signature: (p : MvPolynomial σ R)
  body: (AddMonoidAlgebra.coeff p).sum fun s a => f a * s.prod fun n e => g n ^ e

中文:
定义 eval₂
  签名: (p : MvPolynomial σ R)
  定义体: (AddMonoidAlgebra.coeff p).sum fun s a => f a * s.prod fun n e => g n ^ e

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff, s.prod
-/
def eval₂ (p : MvPolynomial σ R) : S₁ :=
  (AddMonoidAlgebra.coeff p).sum fun s a => f a * s.prod fun n e => g n ^ e

/--
theorem `eval₂_eq` / 定理 `eval₂_eq`

English:
theorem eval₂_eq
  given: (g : R ->+* S₁) (X : σ -> S₁) (f : MvPolynomial σ R)
  proof: rfl

中文:
定理 eval₂_eq
  条件: (g : R ->+* S₁) (X : σ -> S₁) (f : MvPolynomial σ R)
  证明: rfl
-/
theorem eval₂_eq (g : R ->+* S₁) (X : σ -> S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d in f.support, g (f.coeff d) * ∏ i in d.support, X i ^ d i :=
  rfl

/--
theorem `eval₂_eq'` / 定理 `eval₂_eq'`

English:
theorem eval₂_eq'
  given: [Fintype σ] (g : R ->+* S₁) (X : σ -> S₁) (f : MvPolynomial σ R)
  proof: by
  simp only [eval₂_eq, ← Finsupp.prod_pow]
  rfl

@[simp]

中文:
定理 eval₂_eq'
  条件: [Fintype σ] (g : R ->+* S₁) (X : σ -> S₁) (f : MvPolynomial σ R)
  证明: by
  simp only [eval₂_eq, ← Finsupp.prod_pow]
  rfl

@[simp]

Depends on / 依赖: Finsupp, Finsupp.prod_pow, prod_pow
-/
theorem eval₂_eq' [Fintype σ] (g : R ->+* S₁) (X : σ -> S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d in f.support, g (f.coeff d) * ∏ i, X i ^ d i := by
  simp only [eval₂_eq, ← Finsupp.prod_pow]
  rfl

@[simp]
/--
theorem `eval₂_zero` / 定理 `eval₂_zero`

English:
theorem eval₂_zero
  statement: (0 : MvPolynomial σ R).eval₂ f g = 0
  proof: Finsupp.sum_zero_index

中文:
定理 eval₂_zero
  结论: (0 : MvPolynomial σ R).eval₂ f g = 0
  证明: Finsupp.sum_zero_index

Depends on / 依赖: Finsupp, Finsupp.sum_zero_index, sum_zero_index
-/
theorem eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g = 0 :=
  Finsupp.sum_zero_index

section

@[simp]
/--
theorem `eval₂_add` / 定理 `eval₂_add`

English:
theorem eval₂_add
  statement: (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g
  proof: by
  classical exact Finsupp.sum_add_index (by simp [f.map_zero]) (by simp [add_mul, f.map_add])

@[simp]

中文:
定理 eval₂_add
  结论: (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g
  证明: by
  classical exact Finsupp.sum_add_index (by simp [f.map_zero]) (by simp [add_mul, f.map_add])

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, add_mul, classical, f.map_add, f.map_zero, map_add, map_zero, sum_add_index
-/
theorem eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g := by
  classical exact Finsupp.sum_add_index (by simp [f.map_zero]) (by simp [add_mul, f.map_add])

@[simp]
/--
theorem `eval₂_monomial` / 定理 `eval₂_monomial`

English:
theorem eval₂_monomial
  statement: (monomial s a).eval₂ f g = f a * s.prod fun n e => g n ^ e
  proof: Finsupp.sum_single_index (by simp [f.map_zero])

@[simp]

中文:
定理 eval₂_monomial
  结论: (monomial s a).eval₂ f g = f a * s.prod fun n e => g n ^ e
  证明: Finsupp.sum_single_index (by simp [f.map_zero])

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_single_index, f.map_zero, map_zero, sum_single_index
-/
theorem eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod fun n e => g n ^ e :=
  Finsupp.sum_single_index (by simp [f.map_zero])

@[simp]
/--
theorem `eval₂_C` / 定理 `eval₂_C`

English:
theorem eval₂_C
  given: (a)
  statement: (C a).eval₂ f g = f a
  proof: by
  rw [C_apply]; rw [eval₂_monomial]; rw [prod_zero_index]; rw [mul_one]

@[simp]

中文:
定理 eval₂_C
  条件: (a)
  结论: (C a).eval₂ f g = f a
  证明: by
  rw [C_apply]; rw [eval₂_monomial]; rw [prod_zero_index]; rw [mul_one]

@[simp]

Depends on / 依赖: C_apply, mul_one, prod_zero_index
-/
theorem eval₂_C (a) : (C a).eval₂ f g = f a := by
  rw [C_apply]; rw [eval₂_monomial]; rw [prod_zero_index]; rw [mul_one]

@[simp]
/--
theorem `eval₂_one` / 定理 `eval₂_one`

English:
theorem eval₂_one
  statement: (1 : MvPolynomial σ R).eval₂ f g = 1
  proof: (eval₂_C _ _ _).trans f.map_one

中文:
定理 eval₂_one
  结论: (1 : MvPolynomial σ R).eval₂ f g = 1
  证明: (eval₂_C _ _ _).trans f.map_one

Depends on / 依赖: f.map_one, map_one
-/
theorem eval₂_one : (1 : MvPolynomial σ R).eval₂ f g = 1 :=
  (eval₂_C _ _ _).trans f.map_one

/--
theorem `eval₂_natCast` / 定理 `eval₂_natCast`

English:
theorem eval₂_natCast
  given: (n : Nat)
  statement: (n : MvPolynomial σ R).eval₂ f g = n
  proof: (eval₂_C _ _ _).trans (map_natCast f n)

中文:
定理 eval₂_natCast
  条件: (n : 自然数)
  结论: (n : MvPolynomial σ R).eval₂ f g = n
  证明: (eval₂_C _ _ _).trans (map_natCast f n)
-/
@[simp] theorem eval₂_natCast (n : Nat) : (n : MvPolynomial σ R).eval₂ f g = n :=
  (eval₂_C _ _ _).trans (map_natCast f n)

/--
theorem `eval₂_ofNat` / 定理 `eval₂_ofNat`

English:
theorem eval₂_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: eval₂_natCast f g n

@[simp]

中文:
定理 eval₂_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: eval₂_natCast f g n

@[simp]
-/
@[simp] theorem eval₂_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval₂ f g = ofNat(n) :=
  eval₂_natCast f g n

@[simp]
/--
theorem `eval₂_X` / 定理 `eval₂_X`

English:
theorem eval₂_X
  given: (n)
  statement: (X n).eval₂ f g = g n
  proof: by
  simp [eval₂_monomial, f.map_one, X, prod_single_index, pow_one]

中文:
定理 eval₂_X
  条件: (n)
  结论: (X n).eval₂ f g = g n
  证明: by
  simp [eval₂_monomial, f.map_one, X, prod_single_index, pow_one]

Depends on / 依赖: f.map_one, map_one, pow_one, prod_single_index
-/
theorem eval₂_X (n) : (X n).eval₂ f g = g n := by
  simp [eval₂_monomial, f.map_one, X, prod_single_index, pow_one]

/--
theorem `eval₂_X_pow` / 定理 `eval₂_X_pow`

English:
theorem eval₂_X_pow
  given: {s : σ} {n : Nat}
  statement: ((X s) ^ n).eval₂ f g = (g s) ^ n
  proof: by
  simp [X_pow_eq_monomial, eval₂_monomial f g]

中文:
定理 eval₂_X_pow
  条件: {s : σ} {n : 自然数}
  结论: ((X s) ^ n).eval₂ f g = (g s) ^ n
  证明: by
  simp [X_pow_eq_monomial, eval₂_monomial f g]

Depends on / 依赖: X_pow_eq_monomial
-/
theorem eval₂_X_pow {s : σ} {n : Nat} : ((X s) ^ n).eval₂ f g = (g s) ^ n := by
  simp [X_pow_eq_monomial, eval₂_monomial f g]

/--
theorem `eval₂_mul_monomial` / 定理 `eval₂_mul_monomial`

English:
theorem eval₂_mul_monomial
  proof: by
  classical
  apply MvPolynomial.induction_on p
  · intro a' s a
    simp [C_mul_monomial, eval₂_monomial, f.map_mul]
  · intro p q ih_p ih_q
    simp [add_mul, eval₂_add, ih_p, ih_q]
  · intro p n ih s a
    exact
      calc (p * X n * monomial s a).eval₂ f g
        _ = (p * monomial (Finsupp.s

中文:
定理 eval₂_mul_monomial
  证明: by
  classical
  apply MvPolynomial.induction_on p
  · intro a' s a
    simp [C_mul_monomial, eval₂_monomial, f.map_mul]
  · intro p q ih_p ih_q
    simp [add_mul, eval₂_add, ih_p, ih_q]
  · intro p n ih s a
    exact
      calc (p * X n * monomial s a).eval₂ f g
        _ = (p * monomial (Finsupp.s

Depends on / 依赖: C_mul_monomial, Finsupp, Finsupp.single, MvPolynomial, MvPolynomial.induction_on, add_mul, classical, f.map_mul, ih_p, ih_q, induction_on, map_mul, monomial, monomial_single_add, mul_assoc, pow_one, prod_add_index, prod_single_index, s.prod, single
-/
theorem eval₂_mul_monomial :
    forall {s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod fun n e => g n ^ e := by
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
          rw [monomial_single_add]; rw [pow_one]; rw [mul_assoc]
        _ = (p * monomial (Finsupp.single n 1) 1).eval₂ f g * f a * s.prod fun n e => g n ^ e := by
          simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
            f.map_one]

/--
theorem `eval₂_mul_C` / 定理 `eval₂_mul_C`

English:
theorem eval₂_mul_C
  statement: (p * C a).eval₂ f g = p.eval₂ f g * f a
  proof: (eval₂_mul_monomial _ _).trans by simp

@[simp]

中文:
定理 eval₂_mul_C
  结论: (p * C a).eval₂ f g = p.eval₂ f g * f a
  证明: (eval₂_mul_monomial _ _).trans by simp

@[simp]
-/
theorem eval₂_mul_C : (p * C a).eval₂ f g = p.eval₂ f g * f a :=
(eval₂_mul_monomial _ _).trans by simp

@[simp]
/--
theorem `eval₂_mul` / 定理 `eval₂_mul`

English:
theorem eval₂_mul
  statement: forall {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g
  proof: by
  apply MvPolynomial.induction_on q
  · simp [eval₂_C, eval₂_mul_C]
  · simp +contextual [mul_add, eval₂_add]
  · simp +contextual [X, eval₂_mul_monomial, ← mul_assoc]

中文:
定理 eval₂_mul
  结论: 对任意 {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g
  证明: by
  apply MvPolynomial.induction_on q
  · simp [eval₂_C, eval₂_mul_C]
  · simp +contextual [mul_add, eval₂_add]
  · simp +contextual [X, eval₂_mul_monomial, ← mul_assoc]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, contextual, induction_on, mul_add, mul_assoc
-/
theorem eval₂_mul : forall {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g := by
  apply MvPolynomial.induction_on q
  · simp [eval₂_C, eval₂_mul_C]
  · simp +contextual [mul_add, eval₂_add]
  · simp +contextual [X, eval₂_mul_monomial, ← mul_assoc]

/--
theorem `eval₂_mul_eq_zero_of_left` / 定理 `eval₂_mul_eq_zero_of_left`

English:
theorem eval₂_mul_eq_zero_of_left
  given: (hp : p.eval₂ f g = 0)
  statement: (p * q).eval₂ f g = 0
  proof: by
  simp [eval₂_mul f g, hp]

中文:
定理 eval₂_mul_eq_zero_of_left
  条件: (hp : p.eval₂ f g = 0)
  结论: (p * q).eval₂ f g = 0
  证明: by
  simp [eval₂_mul f g, hp]
-/
theorem eval₂_mul_eq_zero_of_left (hp : p.eval₂ f g = 0) : (p * q).eval₂ f g = 0 := by
  simp [eval₂_mul f g, hp]

/--
theorem `eval₂_mul_eq_zero_of_right` / 定理 `eval₂_mul_eq_zero_of_right`

English:
theorem eval₂_mul_eq_zero_of_right
  given: (hq : q.eval₂ f g = 0)
  statement: (p * q).eval₂ f g = 0
  proof: by
  simp [eval₂_mul f g, hq]

@[simp]

中文:
定理 eval₂_mul_eq_zero_of_right
  条件: (hq : q.eval₂ f g = 0)
  结论: (p * q).eval₂ f g = 0
  证明: by
  simp [eval₂_mul f g, hq]

@[simp]
-/
theorem eval₂_mul_eq_zero_of_right (hq : q.eval₂ f g = 0) : (p * q).eval₂ f g = 0 := by
  simp [eval₂_mul f g, hq]

@[simp]
/--
theorem `eval₂_pow` / 定理 `eval₂_pow`

English:
theorem eval₂_pow
  given: {p : MvPolynomial σ R}
  statement: forall {n : Nat}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n

中文:
定理 eval₂_pow
  条件: {p : MvPolynomial σ R}
  结论: 对任意 {n : 自然数}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n
-/
theorem eval₂_pow {p : MvPolynomial σ R} : forall {n : Nat}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n
  | 0 => by
    rw [pow_zero]; rw [pow_zero]
    exact eval₂_one _ _
  | n + 1 => by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

/--
Definition of `eval₂Hom` / `eval₂Hom` 的定义

English:
definition eval₂Hom
  signature: (f : R ->+* S₁) (g : σ -> S₁)
  body: eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _

@[gcongr]

中文:
定义 eval₂Hom
  签名: (f : R ->+* S₁) (g : σ -> S₁)
  定义体: eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _

@[gcongr]
-/
def eval₂Hom (f : R ->+* S₁) (g : σ -> S₁) : MvPolynomial σ R ->+* S₁ where
  toFun := eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _

@[gcongr]
/--
lemma `eval₂_dvd` / 引理 `eval₂_dvd`

English:
lemma eval₂_dvd
  given: (f : R ->+* S₁) (g : σ -> S₁) {p q : MvPolynomial σ R} (h : p ∣ q)
  proof: map_dvd (eval₂Hom f g) h

@[simp]

中文:
引理 eval₂_dvd
  条件: (f : R ->+* S₁) (g : σ -> S₁) {p q : MvPolynomial σ R} (h : p ∣ q)
  证明: map_dvd (eval₂Hom f g) h

@[simp]

Depends on / 依赖: map_dvd
-/
lemma eval₂_dvd (f : R ->+* S₁) (g : σ -> S₁) {p q : MvPolynomial σ R} (h : p ∣ q) :
    p.eval₂ f g ∣ q.eval₂ f g :=
  map_dvd (eval₂Hom f g) h

@[simp]
/--
theorem `coe_eval₂Hom` / 定理 `coe_eval₂Hom`

English:
theorem coe_eval₂Hom
  given: (f : R ->+* S₁) (g : σ -> S₁)
  statement: ⇑(eval₂Hom f g) = eval₂ f g
  proof: rfl

中文:
定理 coe_eval₂Hom
  条件: (f : R ->+* S₁) (g : σ -> S₁)
  结论: ⇑(eval₂Hom f g) = eval₂ f g
  证明: rfl
-/
theorem coe_eval₂Hom (f : R ->+* S₁) (g : σ -> S₁) : ⇑(eval₂Hom f g) = eval₂ f g :=
  rfl

/--
theorem `eval₂Hom_congr` / 定理 `eval₂Hom_congr`

English:
theorem eval₂Hom_congr
  given: {f₁ f₂ : R ->+* S₁} {g₁ g₂ : σ -> S₁} {p₁ p₂ : MvPolynomial σ R}
  proof: by
  rintro rfl rfl rfl; rfl

中文:
定理 eval₂Hom_congr
  条件: {f₁ f₂ : R ->+* S₁} {g₁ g₂ : σ -> S₁} {p₁ p₂ : MvPolynomial σ R}
  证明: by
  rintro rfl rfl rfl; rfl
-/
theorem eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ : σ -> S₁} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl rfl rfl; rfl

end

@[simp]
/--
theorem `eval₂Hom_C` / 定理 `eval₂Hom_C`

English:
theorem eval₂Hom_C
  given: (f : R ->+* S₁) (g : σ -> S₁) (r : R)
  statement: eval₂Hom f g (C r) = f r
  proof: eval₂_C f g r

@[simp]

中文:
定理 eval₂Hom_C
  条件: (f : R ->+* S₁) (g : σ -> S₁) (r : R)
  结论: eval₂Hom f g (C r) = f r
  证明: eval₂_C f g r

@[simp]
-/
theorem eval₂Hom_C (f : R ->+* S₁) (g : σ -> S₁) (r : R) : eval₂Hom f g (C r) = f r :=
  eval₂_C f g r

@[simp]
/--
theorem `eval₂Hom_X'` / 定理 `eval₂Hom_X'`

English:
theorem eval₂Hom_X'
  given: (f : R ->+* S₁) (g : σ -> S₁) (i : σ)
  statement: eval₂Hom f g (X i) = g i
  proof: eval₂_X f g i

@[simp]

中文:
定理 eval₂Hom_X'
  条件: (f : R ->+* S₁) (g : σ -> S₁) (i : σ)
  结论: eval₂Hom f g (X i) = g i
  证明: eval₂_X f g i

@[simp]
-/
theorem eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i : σ) : eval₂Hom f g (X i) = g i :=
  eval₂_X f g i

@[simp]
/--
theorem `comp_eval₂Hom` / 定理 `comp_eval₂Hom`

English:
theorem comp_eval₂Hom
  given: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂)
  proof: by
  ext <;> simp

中文:
定理 comp_eval₂Hom
  条件: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂)
  证明: by
  ext <;> simp
-/
theorem comp_eval₂Hom [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂) :
    φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f) fun i => φ (g i) := by
  ext <;> simp

/--
theorem `map_eval₂Hom` / 定理 `map_eval₂Hom`

English:
theorem map_eval₂Hom
  statement: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂)
  proof: by
  rw [← comp_eval₂Hom]
  rfl

中文:
定理 map_eval₂Hom
  结论: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂)
  证明: by
  rw [← comp_eval₂Hom]
  rfl
-/
theorem map_eval₂Hom [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂)
    (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = eval₂Hom (φ.comp f) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl

/--
theorem `hom_eval₂` / 定理 `hom_eval₂`

English:
theorem hom_eval₂
  statement: [CommSemiring S₂] (p : MvPolynomial σ R) (f : R ->+* S₁)
  proof: map_eval₂Hom f g φ p

中文:
定理 hom_eval₂
  结论: [CommSemiring S₂] (p : MvPolynomial σ R) (f : R ->+* S₁)
  证明: map_eval₂Hom f g φ p
-/
theorem hom_eval₂ [CommSemiring S₂] (p : MvPolynomial σ R) (f : R ->+* S₁)
    (φ : S₁ ->+* S₂) (g : σ -> S₁) :
    φ (p.eval₂ f g) = p.eval₂ (φ.comp f) (fun i => φ (g i)) :=
  map_eval₂Hom f g φ p

/--
theorem `eval₂Hom_monomial` / 定理 `eval₂Hom_monomial`

English:
theorem eval₂Hom_monomial
  given: (f : R ->+* S₁) (g : σ -> S₁) (d : σ ->₀ Nat) (r : R)
  proof: by
  simp only [coe_eval₂Hom, eval₂_monomial]

@[simp]

中文:
定理 eval₂Hom_monomial
  条件: (f : R ->+* S₁) (g : σ -> S₁) (d : σ ->₀ 自然数) (r : R)
  证明: by
  simp only [coe_eval₂Hom, eval₂_monomial]

@[simp]
-/
theorem eval₂Hom_monomial (f : R ->+* S₁) (g : σ -> S₁) (d : σ ->₀ Nat) (r : R) :
    eval₂Hom f g (monomial d r) = f r * d.prod fun i k => g i ^ k := by
  simp only [coe_eval₂Hom, eval₂_monomial]

@[simp]
/--
theorem `eval₂Hom_smul` / 定理 `eval₂Hom_smul`

English:
theorem eval₂Hom_smul
  given: (f : R ->+* S₁) (g : σ -> S₁) (r : R) (P : MvPolynomial σ R)
  proof: by
  simp [smul_eq_C_mul]

中文:
定理 eval₂Hom_smul
  条件: (f : R ->+* S₁) (g : σ -> S₁) (r : R) (P : MvPolynomial σ R)
  证明: by
  simp [smul_eq_C_mul]

Depends on / 依赖: smul_eq_C_mul
-/
theorem eval₂Hom_smul (f : R ->+* S₁) (g : σ -> S₁) (r : R) (P : MvPolynomial σ R) :
    eval₂Hom f g (r • P) = f r • eval₂Hom f g P := by
  simp [smul_eq_C_mul]

section

/--
theorem `eval₂_comp_left` / 定理 `eval₂_comp_left`

English:
theorem eval₂_comp_left
  given: {S₂} [CommSemiring S₂] (k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p)
  proof: by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, k.map_add, eval₂_mul, k.map_mul]

中文:
定理 eval₂_comp_left
  条件: {S₂} [CommSemiring S₂] (k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p)
  证明: by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, k.map_add, eval₂_mul, k.map_mul]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, contextual, induction_on, k.map_add, k.map_mul, map_add, map_mul
-/
theorem eval₂_comp_left {S₂} [CommSemiring S₂] (k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p) :
    k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, k.map_add, eval₂_mul, k.map_mul]

end

@[simp]
/--
theorem `eval₂_eta` / 定理 `eval₂_eta`

English:
theorem eval₂_eta
  given: (p : MvPolynomial σ R)
  statement: eval₂ C X p = p
  proof: by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, eval₂_mul]

中文:
定理 eval₂_eta
  条件: (p : MvPolynomial σ R)
  结论: eval₂ C X p = p
  证明: by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, eval₂_mul]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, contextual, induction_on
-/
theorem eval₂_eta (p : MvPolynomial σ R) : eval₂ C X p = p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, eval₂_mul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eval₂_congr` / 定理 `eval₂_congr`

English:
theorem eval₂_congr
  statement: (g₁ g₂ : σ -> S₁)
  proof: by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

中文:
定理 eval₂_congr
  结论: (g₁ g₂ : σ -> S₁)
  证明: by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

Depends on / 依赖: Finset, Finset.prod_congr, Finset.sum_congr, Finsupp, Finsupp.mem_support_iff, mem_support_iff, prod_congr, sum_congr
-/
theorem eval₂_congr (g₁ g₂ : σ -> S₁)
    (h : forall {i : σ} {c : σ ->₀ Nat}, i in c.support -> coeff c p != 0 -> g₁ i = g₂ i) :
    p.eval₂ f g₁ = p.eval₂ f g₂ := by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

/--
theorem `eval₂_sum` / 定理 `eval₂_sum`

English:
theorem eval₂_sum
  given: (s : Finset S₂) (p : S₂ -> MvPolynomial σ R)
  proof: map_sum (eval₂Hom f g) _ s

中文:
定理 eval₂_sum
  条件: (s : Finset S₂) (p : S₂ -> MvPolynomial σ R)
  证明: map_sum (eval₂Hom f g) _ s
-/
@[simp] theorem eval₂_sum (s : Finset S₂) (p : S₂ -> MvPolynomial σ R) :
    eval₂ f g (∑ x in s, p x) = ∑ x in s, eval₂ f g (p x) :=
  map_sum (eval₂Hom f g) _ s

/--
theorem `eval₂_prod` / 定理 `eval₂_prod`

English:
theorem eval₂_prod
  given: (s : Finset S₂) (p : S₂ -> MvPolynomial σ R)
  proof: map_prod (eval₂Hom f g) _ s

中文:
定理 eval₂_prod
  条件: (s : Finset S₂) (p : S₂ -> MvPolynomial σ R)
  证明: map_prod (eval₂Hom f g) _ s
-/
@[simp] theorem eval₂_prod (s : Finset S₂) (p : S₂ -> MvPolynomial σ R) :
    eval₂ f g (∏ x in s, p x) = ∏ x in s, eval₂ f g (p x) :=
  map_prod (eval₂Hom f g) _ s

/--
theorem `eval₂_assoc` / 定理 `eval₂_assoc`

English:
theorem eval₂_assoc
  given: (q : S₂ -> MvPolynomial σ R) (p : MvPolynomial S₂ R)
  proof: by
  change _ = eval₂Hom f g (eval₂ C q p)
  rw [eval₂_comp_left (eval₂Hom f g)]; congr with a; simp

中文:
定理 eval₂_assoc
  条件: (q : S₂ -> MvPolynomial σ R) (p : MvPolynomial S₂ R)
  证明: by
  change _ = eval₂Hom f g (eval₂ C q p)
  rw [eval₂_comp_left (eval₂Hom f g)]; congr with a; simp
-/
theorem eval₂_assoc (q : S₂ -> MvPolynomial σ R) (p : MvPolynomial S₂ R) :
    eval₂ f (fun t => eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) := by
  change _ = eval₂Hom f g (eval₂ C q p)
  rw [eval₂_comp_left (eval₂Hom f g)]; congr with a; simp

end Eval₂

section Eval

variable {f : σ -> R}

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (f : σ -> R)
  body: eval₂Hom (RingHom.id _) f

中文:
定义 eval
  签名: (f : σ -> R)
  定义体: eval₂Hom (RingHom.id _) f

Depends on / 依赖: RingHom, RingHom.id
-/
def eval (f : σ -> R) : MvPolynomial σ R ->+* R :=
  eval₂Hom (RingHom.id _) f

/--
theorem `eval_eq` / 定理 `eval_eq`

English:
theorem eval_eq
  given: (X : σ -> R) (f : MvPolynomial σ R)
  proof: rfl

中文:
定理 eval_eq
  条件: (X : σ -> R) (f : MvPolynomial σ R)
  证明: rfl
-/
theorem eval_eq (X : σ -> R) (f : MvPolynomial σ R) :
    eval X f = ∑ d in f.support, f.coeff d * ∏ i in d.support, X i ^ d i :=
  rfl

/--
theorem `eval_eq'` / 定理 `eval_eq'`

English:
theorem eval_eq'
  given: [Fintype σ] (X : σ -> R) (f : MvPolynomial σ R)
  proof: eval₂_eq' (RingHom.id R) X f

中文:
定理 eval_eq'
  条件: [Fintype σ] (X : σ -> R) (f : MvPolynomial σ R)
  证明: eval₂_eq' (RingHom.id R) X f

Depends on / 依赖: RingHom, RingHom.id
-/
theorem eval_eq' [Fintype σ] (X : σ -> R) (f : MvPolynomial σ R) :
    eval X f = ∑ d in f.support, f.coeff d * ∏ i, X i ^ d i :=
  eval₂_eq' (RingHom.id R) X f

/--
theorem `eval_monomial` / 定理 `eval_monomial`

English:
theorem eval_monomial
  statement: eval f (monomial s a) = a * s.prod fun n e => f n ^ e
  proof: eval₂_monomial _ _

@[simp]

中文:
定理 eval_monomial
  结论: eval f (monomial s a) = a * s.prod fun n e => f n ^ e
  证明: eval₂_monomial _ _

@[simp]
-/
theorem eval_monomial : eval f (monomial s a) = a * s.prod fun n e => f n ^ e :=
  eval₂_monomial _ _

@[simp]
/--
theorem `eval_C` / 定理 `eval_C`

English:
theorem eval_C
  statement: forall a, eval f (C a) = a
  proof: eval₂_C _ _

@[simp]

中文:
定理 eval_C
  结论: 对任意 a, eval f (C a) = a
  证明: eval₂_C _ _

@[simp]
-/
theorem eval_C : forall a, eval f (C a) = a :=
  eval₂_C _ _

@[simp]
/--
theorem `eval_X` / 定理 `eval_X`

English:
theorem eval_X
  statement: forall n, eval f (X n) = f n
  proof: eval₂_X _ _

中文:
定理 eval_X
  结论: 对任意 n, eval f (X n) = f n
  证明: eval₂_X _ _
-/
theorem eval_X : forall n, eval f (X n) = f n :=
  eval₂_X _ _

/--
theorem `eval_ofNat` / 定理 `eval_ofNat`

English:
theorem eval_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: map_ofNat _ n

@[simp]

中文:
定理 eval_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: map_ofNat _ n

@[simp]
-/
@[simp] theorem eval_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval f = ofNat(n) :=
  map_ofNat _ n

@[simp]
/--
theorem `smul_eval` / 定理 `smul_eval`

English:
theorem smul_eval
  given: (x) (p : MvPolynomial σ R) (s)
  statement: eval x (s • p) = s * eval x p
  proof: by
  rw [smul_eq_C_mul]; rw [(eval x).map_mul]; rw [eval_C]

中文:
定理 smul_eval
  条件: (x) (p : MvPolynomial σ R) (s)
  结论: eval x (s • p) = s * eval x p
  证明: by
  rw [smul_eq_C_mul]; rw [(eval x).map_mul]; rw [eval_C]

Depends on / 依赖: eval_C, map_mul, smul_eq_C_mul
-/
theorem smul_eval (x) (p : MvPolynomial σ R) (s) : eval x (s • p) = s * eval x p := by
  rw [smul_eq_C_mul]; rw [(eval x).map_mul]; rw [eval_C]

/--
theorem `eval_add` / 定理 `eval_add`

English:
theorem eval_add
  statement: eval f (p + q) = eval f p + eval f q
  proof: eval₂_add _ _

中文:
定理 eval_add
  结论: eval f (p + q) = eval f p + eval f q
  证明: eval₂_add _ _
-/
theorem eval_add : eval f (p + q) = eval f p + eval f q :=
  eval₂_add _ _

/--
theorem `eval_mul` / 定理 `eval_mul`

English:
theorem eval_mul
  statement: eval f (p * q) = eval f p * eval f q
  proof: eval₂_mul _ _

中文:
定理 eval_mul
  结论: eval f (p * q) = eval f p * eval f q
  证明: eval₂_mul _ _
-/
theorem eval_mul : eval f (p * q) = eval f p * eval f q :=
  eval₂_mul _ _

/--
theorem `eval_pow` / 定理 `eval_pow`

English:
theorem eval_pow
  statement: forall n, eval f (p ^ n) = eval f p ^ n
  proof: fun _ => eval₂_pow _ _

中文:
定理 eval_pow
  结论: 对任意 n, eval f (p ^ n) = eval f p ^ n
  证明: fun _ => eval₂_pow _ _
-/
theorem eval_pow : forall n, eval f (p ^ n) = eval f p ^ n :=
  fun _ => eval₂_pow _ _

/--
theorem `eval_sum` / 定理 `eval_sum`

English:
theorem eval_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> R)
  proof: map_sum (eval g) _ _

中文:
定理 eval_sum
  条件: {ι : 类型} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> R)
  证明: map_sum (eval g) _ _

Depends on / 依赖: map_sum
-/
theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> R) :
    eval g (∑ i in s, f i) = ∑ i in s, eval g (f i) :=
  map_sum (eval g) _ _

/--
theorem `eval_prod` / 定理 `eval_prod`

English:
theorem eval_prod
  given: {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> R)
  proof: map_prod (eval g) _ _

中文:
定理 eval_prod
  条件: {ι : 类型} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> R)
  证明: map_prod (eval g) _ _

Depends on / 依赖: map_prod
-/
theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (g : σ -> R) :
    eval g (∏ i in s, f i) = ∏ i in s, eval g (f i) :=
  map_prod (eval g) _ _

/--
theorem `eval_assoc` / 定理 `eval_assoc`

English:
theorem eval_assoc
  given: {τ} (f : σ -> MvPolynomial τ R) (g : τ -> R) (p : MvPolynomial σ R)
  proof: by
  rw [eval₂_comp_left (eval g)]
  unfold eval; simp only [coe_eval₂Hom]
  congr with a; simp

@[simp]

中文:
定理 eval_assoc
  条件: {τ} (f : σ -> MvPolynomial τ R) (g : τ -> R) (p : MvPolynomial σ R)
  证明: by
  rw [eval₂_comp_left (eval g)]
  unfold eval; simp only [coe_eval₂Hom]
  congr with a; simp

@[simp]
-/
theorem eval_assoc {τ} (f : σ -> MvPolynomial τ R) (g : τ -> R) (p : MvPolynomial σ R) :
    eval (eval g ∘ f) p = eval g (eval₂ C f p) := by
  rw [eval₂_comp_left (eval g)]
  unfold eval; simp only [coe_eval₂Hom]
  congr with a; simp

@[simp]
/--
theorem `eval₂_id` / 定理 `eval₂_id`

English:
theorem eval₂_id
  given: {g : σ -> R} (p : MvPolynomial σ R)
  statement: eval₂ (RingHom.id _) g p = eval g p
  proof: rfl

中文:
定理 eval₂_id
  条件: {g : σ -> R} (p : MvPolynomial σ R)
  结论: eval₂ (RingHom.id _) g p = eval g p
  证明: rfl
-/
theorem eval₂_id {g : σ -> R} (p : MvPolynomial σ R) : eval₂ (RingHom.id _) g p = eval g p :=
  rfl

/--
theorem `eval_eval₂` / 定理 `eval_eval₂`

English:
theorem eval_eval₂
  statement: {S τ : Type*} {x : τ -> S} [CommSemiring S]
  proof: by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

中文:
定理 eval_eval₂
  结论: {S τ : 类型} {x : τ -> S} [CommSemiring S]
  证明: by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

Depends on / 依赖: induction_on
-/
theorem eval_eval₂ {S τ : Type*} {x : τ -> S} [CommSemiring S]
    (f : R ->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S) (p : MvPolynomial σ R) :
    eval x (eval₂ f g p) = eval₂ ((eval x).comp f) (fun s => eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

end Eval

section Map

variable (f : R ->+* S₁)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : MvPolynomial σ R ->+* MvPolynomial σ S₁
  body: AddMonoidAlgebra.mapRingHom _ f

@[simp]

中文:
定义 map
  签名: : MvPolynomial σ R ->+* MvPolynomial σ S₁
  定义体: AddMonoidAlgebra.mapRingHom _ f

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapRingHom, mapRingHom
-/
def map : MvPolynomial σ R ->+* MvPolynomial σ S₁ := AddMonoidAlgebra.mapRingHom _ f

@[simp]
/--
theorem `map_monomial` / 定理 `map_monomial`

English:
theorem map_monomial
  given: (s : σ ->₀ Nat) (a : R)
  statement: map f (monomial s a) = monomial s (f a)
  proof: AddMonoidAlgebra.map_single ..

@[simp]

中文:
定理 map_monomial
  条件: (s : σ ->₀ 自然数) (a : R)
  结论: map f (monomial s a) = monomial s (f a)
  证明: AddMonoidAlgebra.map_single ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.map_single, map_single
-/
theorem map_monomial (s : σ ->₀ Nat) (a : R) : map f (monomial s a) = monomial s (f a) :=
  AddMonoidAlgebra.map_single ..

@[simp]
/--
theorem `map_C` / 定理 `map_C`

English:
theorem map_C
  statement: forall a : R, map f (C a : MvPolynomial σ R) = C (f a)
  proof: map_monomial _ _

中文:
定理 map_C
  结论: 对任意 a : R, map f (C a : MvPolynomial σ R) = C (f a)
  证明: map_monomial _ _

Depends on / 依赖: map_monomial
-/
theorem map_C : forall a : R, map f (C a : MvPolynomial σ R) = C (f a) :=
  map_monomial _ _

/--
theorem `map_ofNat` / 定理 `map_ofNat`

English:
theorem map_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: _root_.map_ofNat _ _

@[simp]

中文:
定理 map_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: _root_.map_ofNat _ _

@[simp]
-/
@[simp] protected theorem map_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).map f = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
/--
theorem `map_X` / 定理 `map_X`

English:
theorem map_X
  given: (n : σ)
  statement: map f (X n : MvPolynomial σ R) = X n
  proof: by simp [X]

中文:
定理 map_X
  条件: (n : σ)
  结论: map f (X n : MvPolynomial σ R) = X n
  证明: by simp [X]
-/
theorem map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n := by simp [X]

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: forall p : MvPolynomial σ R, map (RingHom.id R) p = p
  proof: AddMonoidAlgebra.map_id

中文:
定理 map_id
  结论: 对任意 p : MvPolynomial σ R, map (RingHom.id R) p = p
  证明: AddMonoidAlgebra.map_id

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.map_id, map_id
-/
theorem map_id : forall p : MvPolynomial σ R, map (RingHom.id R) p = p := AddMonoidAlgebra.map_id

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: [CommSemiring S₂] (g : S₁ ->+* S₂) (p : MvPolynomial σ R)
  proof: AddMonoidAlgebra.map_map ..

中文:
定理 map_map
  条件: [CommSemiring S₂] (g : S₁ ->+* S₂) (p : MvPolynomial σ R)
  证明: AddMonoidAlgebra.map_map ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.map_map, map_map
-/
theorem map_map [CommSemiring S₂] (g : S₁ ->+* S₂) (p : MvPolynomial σ R) :
    map g (map f p) = map (g.comp f) p := AddMonoidAlgebra.map_map ..

/--
theorem `eval₂_eq_eval_map` / 定理 `eval₂_eq_eval_map`

English:
theorem eval₂_eq_eval_map
  given: (g : σ -> S₁) (p : MvPolynomial σ R)
  statement: p.eval₂ f g = eval g (map f p)
  proof: by
  simp [eval₂, eval]; simp [map, MvPolynomial, Finsupp.sum_mapRange_index, mapRingHom]

中文:
定理 eval₂_eq_eval_map
  条件: (g : σ -> S₁) (p : MvPolynomial σ R)
  结论: p.eval₂ f g = eval g (map f p)
  证明: by
  simp [eval₂, eval]; simp [map, MvPolynomial, Finsupp.sum_mapRange_index, mapRingHom]

Depends on / 依赖: Finsupp, Finsupp.sum_mapRange_index, MvPolynomial, mapRingHom, sum_mapRange_index
-/
theorem eval₂_eq_eval_map (g : σ -> S₁) (p : MvPolynomial σ R) : p.eval₂ f g = eval g (map f p) := by
  simp [eval₂, eval]; simp [map, MvPolynomial, Finsupp.sum_mapRange_index, mapRingHom]

/--
theorem `eval₂_comp_right` / 定理 `eval₂_comp_right`

English:
theorem eval₂_comp_right
  given: {S₂} [CommSemiring S₂] (k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p)
  proof: by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C]; rw [map_C]; rw [eval₂_C]
  · intro p q hp hq
    rw [eval₂_add]; rw [k.map_add]; rw [(map f).map_add]; rw [eval₂_add]; rw [hp]; rw [hq]
  · intro p s hp
    rw [eval₂_mul]; rw [k.map_mul]; rw [(map f).map_mul]; rw [eval₂_mul]; rw [

中文:
定理 eval₂_comp_right
  条件: {S₂} [CommSemiring S₂] (k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p)
  证明: by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C]; rw [map_C]; rw [eval₂_C]
  · intro p q hp hq
    rw [eval₂_add]; rw [k.map_add]; rw [(map f).map_add]; rw [eval₂_add]; rw [hp]; rw [hq]
  · intro p s hp
    rw [eval₂_mul]; rw [k.map_mul]; rw [(map f).map_mul]; rw [eval₂_mul]; rw [

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, comp_apply, induction_on, k.map_add, k.map_mul, map_C, map_X, map_add, map_mul
-/
theorem eval₂_comp_right {S₂} [CommSemiring S₂] (k : S₁ ->+* S₂) (f : R ->+* S₁) (g : σ -> S₁) (p) :
    k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C]; rw [map_C]; rw [eval₂_C]
  · intro p q hp hq
    rw [eval₂_add]; rw [k.map_add]; rw [(map f).map_add]; rw [eval₂_add]; rw [hp]; rw [hq]
  · intro p s hp
    rw [eval₂_mul]; rw [k.map_mul]; rw [(map f).map_mul]; rw [eval₂_mul]; rw [map_X]; rw [hp]; rw [eval₂_X]; rw [eval₂_X]; rw [comp_apply]

/--
theorem `map_eval₂` / 定理 `map_eval₂`

English:
theorem map_eval₂
  given: (f : R ->+* S₁) (g : S₂ -> MvPolynomial S₃ R) (p : MvPolynomial S₂ R)
  proof: by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C]; rw [map_C]; rw [map_C]; rw [eval₂_C]
  · intro p q hp hq
    rw [eval₂_add]; rw [(map f).map_add]; rw [hp]; rw [hq]; rw [(map f).map_add]; rw [eval₂_add]
  · intro p s hp
    rw [eval₂_mul]; rw [(map f).map_mul]; rw [hp]; rw [(map 

中文:
定理 map_eval₂
  条件: (f : R ->+* S₁) (g : S₂ -> MvPolynomial S₃ R) (p : MvPolynomial S₂ R)
  证明: by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C]; rw [map_C]; rw [map_C]; rw [eval₂_C]
  · intro p q hp hq
    rw [eval₂_add]; rw [(map f).map_add]; rw [hp]; rw [hq]; rw [(map f).map_add]; rw [eval₂_add]
  · intro p s hp
    rw [eval₂_mul]; rw [(map f).map_mul]; rw [hp]; rw [(map 

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, comp_apply, induction_on, map_C, map_X, map_add, map_mul
-/
theorem map_eval₂ (f : R ->+* S₁) (g : S₂ -> MvPolynomial S₃ R) (p : MvPolynomial S₂ R) :
    map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C]; rw [map_C]; rw [map_C]; rw [eval₂_C]
  · intro p q hp hq
    rw [eval₂_add]; rw [(map f).map_add]; rw [hp]; rw [hq]; rw [(map f).map_add]; rw [eval₂_add]
  · intro p s hp
    rw [eval₂_mul]; rw [(map f).map_mul]; rw [hp]; rw [(map f).map_mul]; rw [map_X]; rw [eval₂_mul]; rw [eval₂_X]; rw [eval₂_X]; rw [comp_apply]

/--
lemma `eval₂_map_comp_C` / 引理 `eval₂_map_comp_C`

English:
lemma eval₂_map_comp_C
  statement: {ι : Type*} (f : R ->+* S₁) (h : ι -> MvPolynomial σ S₁)
  proof: by
  induction p using MvPolynomial.induction_on <;> simp_all

中文:
引理 eval₂_map_comp_C
  结论: {ι : 类型} (f : R ->+* S₁) (h : ι -> MvPolynomial σ S₁)
  证明: by
  induction p using MvPolynomial.induction_on <;> simp_all

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on
-/
lemma eval₂_map_comp_C {ι : Type*} (f : R ->+* S₁) (h : ι -> MvPolynomial σ S₁)
    (p : MvPolynomial ι R) : eval₂ ((map f).comp C) h p = eval₂ C h (map f p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

/--
lemma `map_eval` / 引理 `map_eval`

English:
lemma map_eval
  given: {S₂ : Type*} [CommSemiring S₂] (q : S₁ ->+* S₂) (g : σ -> S₁) (p : MvPolynomial σ S₁)
  proof: by
  rw [← eval₂_eq_eval_map]; rw [← eval₂_id]; rw [eval₂_comp_right]; rw [map_id]

中文:
引理 map_eval
  条件: {S₂ : 类型} [CommSemiring S₂] (q : S₁ ->+* S₂) (g : σ -> S₁) (p : MvPolynomial σ S₁)
  证明: by
  rw [← eval₂_eq_eval_map]; rw [← eval₂_id]; rw [eval₂_comp_right]; rw [map_id]

Depends on / 依赖: map_id
-/
lemma map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ ->+* S₂) (g : σ -> S₁) (p : MvPolynomial σ S₁) :
    q (eval g p) = eval (q ∘ g) (map q p) := by
  rw [← eval₂_eq_eval_map]; rw [← eval₂_id]; rw [eval₂_comp_right]; rw [map_id]

/--
theorem `coeff_map` / 定理 `coeff_map`

English:
theorem coeff_map
  given: (p : MvPolynomial σ R)
  statement: forall m : σ ->₀ Nat, coeff m (map f p) = f (coeff m p)
  proof: by
  classical
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    simp_rw [map_C, coeff_C, apply_ite f, f.map_zero]
  · intro p q hp hq m
    simp only [hp, hq, (map f).map_add, coeff_add, f.map_add]
  · intro p i hp m
    simp only [(map f).map_mul, map_X, hp, coeff_mul_X', f.map_zer

中文:
定理 coeff_map
  条件: (p : MvPolynomial σ R)
  结论: 对任意 m : σ ->₀ 自然数, coeff m (map f p) = f (coeff m p)
  证明: by
  classical
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    simp_rw [map_C, coeff_C, apply_ite f, f.map_zero]
  · intro p q hp hq m
    simp only [hp, hq, (map f).map_add, coeff_add, f.map_add]
  · intro p i hp m
    simp only [(map f).map_mul, map_X, hp, coeff_mul_X', f.map_zer

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, apply_ite, classical, coeff_C, coeff_add, coeff_mul_X, f.map_add, f.map_zero, induction_on, map_C, map_X, map_add, map_mul, map_zero, simp_rw
-/
theorem coeff_map (p : MvPolynomial σ R) : forall m : σ ->₀ Nat, coeff m (map f p) = f (coeff m p) := by
  classical
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    simp_rw [map_C, coeff_C, apply_ite f, f.map_zero]
  · intro p q hp hq m
    simp only [hp, hq, (map f).map_add, coeff_add, f.map_add]
  · intro p i hp m
    simp only [(map f).map_mul, map_X, hp, coeff_mul_X', f.map_zero, apply_ite f]

/--
lemma `map_eq_eval₂Hom_C_comp` / 引理 `map_eq_eval₂Hom_C_comp`

English:
lemma map_eq_eval₂Hom_C_comp
  statement: map (σ := σ) f = eval₂Hom (C.comp f) X
  proof: by ext a x <;> simp

中文:
引理 map_eq_eval₂Hom_C_comp
  结论: map (σ := σ) f = eval₂Hom (C.comp f) X
  证明: by ext a x <;> simp

Depends on / 依赖: C.comp
-/
lemma map_eq_eval₂Hom_C_comp : map (σ := σ) f = eval₂Hom (C.comp f) X := by ext a x <;> simp

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (hf : Function.Injective f)
  proof: by
  intro p q h
  simp only [MvPolynomial.ext_iff, coeff_map] at h ⊢
  intro m
  exact hf (h m)

中文:
定理 map_injective
  条件: (hf : Function.Injective f)
  证明: by
  intro p q h
  simp only [MvPolynomial.ext_iff, coeff_map] at h ⊢
  intro m
  exact hf (h m)

Depends on / 依赖: MvPolynomial, MvPolynomial.ext_iff, coeff_map, ext_iff
-/
theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁) := by
  intro p q h
  simp only [MvPolynomial.ext_iff, coeff_map] at h ⊢
  intro m
  exact hf (h m)

/--
theorem `map_injective_iff` / 定理 `map_injective_iff`

English:
theorem map_injective_iff
  statement: Function.Injective (map (σ := σ) f) ↔ Function.Injective f
  proof: ⟨fun h r r' eq => by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

中文:
定理 map_injective_iff
  结论: Function.Injective (map (σ := σ) f) ↔ Function.Injective f
  证明: ⟨fun h r r' eq => by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

Depends on / 依赖: Function, Function.Injective, Injective
-/
theorem map_injective_iff : Function.Injective (map (σ := σ) f) ↔ Function.Injective f :=
  ⟨fun h r r' eq => by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (hf : Function.Surjective f)
  proof: fun p => by
  induction p using MvPolynomial.induction_on' with
  | monomial i fr =>
    obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, map_monomial _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩

中文:
定理 map_surjective
  条件: (hf : Function.Surjective f)
  证明: fun p => by
  induction p using MvPolynomial.induction_on' with
  | monomial i fr =>
    obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, map_monomial _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, map_add, map_monomial, monomial
-/
theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f : MvPolynomial σ R -> MvPolynomial σ S₁) := fun p => by
  induction p using MvPolynomial.induction_on' with
  | monomial i fr =>
    obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, map_monomial _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩

/--
theorem `map_surjective_iff` / 定理 `map_surjective_iff`

English:
theorem map_surjective_iff
  statement: Function.Surjective (map (σ := σ) f) ↔ Function.Surjective f
  proof: ⟨fun h s => let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa [coeff_map] using congr(coeff 0 $h)⟩,
    map_surjective f⟩

中文:
定理 map_surjective_iff
  结论: Function.Surjective (map (σ := σ) f) ↔ Function.Surjective f
  证明: ⟨fun h s => let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa [coeff_map] using congr(coeff 0 $h)⟩,
    map_surjective f⟩

Depends on / 依赖: Function, Function.Surjective, Surjective
-/
theorem map_surjective_iff : Function.Surjective (map (σ := σ) f) ↔ Function.Surjective f :=
  ⟨fun h s => let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa [coeff_map] using congr(coeff 0 $h)⟩,
    map_surjective f⟩

/--
theorem `map_leftInverse` / 定理 `map_leftInverse`

English:
theorem map_leftInverse
  given: {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.LeftInverse f g)
  proof: fun X => by
  rw [map_map]; rw [(RingHom.ext hf : f.comp g = RingHom.id _)]; rw [map_id]

中文:
定理 map_leftInverse
  条件: {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.LeftInverse f g)
  证明: fun X => by
  rw [map_map]; rw [(RingHom.ext hf : f.comp g = RingHom.id _)]; rw [map_id]

Depends on / 依赖: RingHom, RingHom.ext, RingHom.id, f.comp, map_id, map_map
-/
theorem map_leftInverse {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (map f : MvPolynomial σ R -> MvPolynomial σ S₁) (map g) := fun X => by
  rw [map_map]; rw [(RingHom.ext hf : f.comp g = RingHom.id _)]; rw [map_id]

/--
theorem `map_rightInverse` / 定理 `map_rightInverse`

English:
theorem map_rightInverse
  given: {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.RightInverse f g)
  proof: (map_leftInverse hf.leftInverse).rightInverse

@[simp]

中文:
定理 map_rightInverse
  条件: {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.RightInverse f g)
  证明: (map_leftInverse hf.leftInverse).rightInverse

@[simp]

Depends on / 依赖: hf.leftInverse, leftInverse, map_leftInverse, rightInverse
-/
theorem map_rightInverse {f : R ->+* S₁} {g : S₁ ->+* R} (hf : Function.RightInverse f g) :
    Function.RightInverse (map f : MvPolynomial σ R -> MvPolynomial σ S₁) (map g) :=
  (map_leftInverse hf.leftInverse).rightInverse

@[simp]
/--
theorem `eval_map` / 定理 `eval_map`

English:
theorem eval_map
  given: (f : R ->+* S₁) (g : σ -> S₁) (p : MvPolynomial σ R)
  proof: by
  apply MvPolynomial.induction_on p <;> · simp +contextual

中文:
定理 eval_map
  条件: (f : R ->+* S₁) (g : σ -> S₁) (p : MvPolynomial σ R)
  证明: by
  apply MvPolynomial.induction_on p <;> · simp +contextual

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, contextual, induction_on
-/
theorem eval_map (f : R ->+* S₁) (g : σ -> S₁) (p : MvPolynomial σ R) :
    eval g (map f p) = eval₂ f g p := by
  apply MvPolynomial.induction_on p <;> · simp +contextual

/--
theorem `eval₂_comp` / 定理 `eval₂_comp`

English:
theorem eval₂_comp
  given: (f : R ->+* S₁) (g : σ -> R) (p : MvPolynomial σ R)
  proof: by
  rw [← p.map_id]; rw [eval_map]; rw [eval₂_comp_right]

@[simp]

中文:
定理 eval₂_comp
  条件: (f : R ->+* S₁) (g : σ -> R) (p : MvPolynomial σ R)
  证明: by
  rw [← p.map_id]; rw [eval_map]; rw [eval₂_comp_right]

@[simp]

Depends on / 依赖: eval_map, map_id, p.map_id
-/
theorem eval₂_comp (f : R ->+* S₁) (g : σ -> R) (p : MvPolynomial σ R) :
    f (eval g p) = eval₂ f (f ∘ g) p := by
  rw [← p.map_id]; rw [eval_map]; rw [eval₂_comp_right]

@[simp]
/--
theorem `eval₂_map` / 定理 `eval₂_map`

English:
theorem eval₂_map
  statement: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂)
  proof: by
  rw [← eval_map]; rw [← eval_map]; rw [map_map]

@[simp]

中文:
定理 eval₂_map
  结论: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂)
  证明: by
  rw [← eval_map]; rw [← eval_map]; rw [map_map]

@[simp]

Depends on / 依赖: eval_map, map_map
-/
theorem eval₂_map [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂)
    (p : MvPolynomial σ R) : eval₂ φ g (map f p) = eval₂ (φ.comp f) g p := by
  rw [← eval_map]; rw [← eval_map]; rw [map_map]

@[simp]
/--
theorem `eval₂Hom_map_hom` / 定理 `eval₂Hom_map_hom`

English:
theorem eval₂Hom_map_hom
  statement: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂)
  proof: eval₂_map f g φ p

@[simp]

中文:
定理 eval₂Hom_map_hom
  结论: [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂)
  证明: eval₂_map f g φ p

@[simp]
-/
theorem eval₂Hom_map_hom [CommSemiring S₂] (f : R ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂)
    (p : MvPolynomial σ R) : eval₂Hom φ g (map f p) = eval₂Hom (φ.comp f) g p :=
  eval₂_map f g φ p

@[simp]
/--
theorem `constantCoeff_map` / 定理 `constantCoeff_map`

English:
theorem constantCoeff_map
  given: (f : R ->+* S₁) (φ : MvPolynomial σ R)
  proof: coeff_map f φ 0

中文:
定理 constantCoeff_map
  条件: (f : R ->+* S₁) (φ : MvPolynomial σ R)
  证明: coeff_map f φ 0

Depends on / 依赖: coeff_map
-/
theorem constantCoeff_map (f : R ->+* S₁) (φ : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ) :=
  coeff_map f φ 0

/--
theorem `constantCoeff_comp_map` / 定理 `constantCoeff_comp_map`

English:
theorem constantCoeff_comp_map
  given: (f : R ->+* S₁)
  proof: by
  ext <;> simp

中文:
定理 constantCoeff_comp_map
  条件: (f : R ->+* S₁)
  证明: by
  ext <;> simp
-/
theorem constantCoeff_comp_map (f : R ->+* S₁) :
    (constantCoeff : MvPolynomial σ S₁ ->+* S₁).comp (MvPolynomial.map f) =
      f.comp constantCoeff := by
  ext <;> simp

/--
theorem `support_map_subset` / 定理 `support_map_subset`

English:
theorem support_map_subset
  given: (p : MvPolynomial σ R)
  statement: (map f p).support subseteq p.support
  proof: by
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map]; rw [hx]; rw [map_zero]

中文:
定理 support_map_subset
  条件: (p : MvPolynomial σ R)
  结论: (map f p).support subseteq p.support
  证明: by
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map]; rw [hx]; rw [map_zero]

Depends on / 依赖: Finset, Finset.subset_iff, coeff_map, contrapose, map_zero, mem_support_iff, subset_iff
-/
theorem support_map_subset (p : MvPolynomial σ R) : (map f p).support subseteq p.support := by
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map]; rw [hx]; rw [map_zero]

/--
theorem `support_map_of_injective` / 定理 `support_map_of_injective`

English:
theorem support_map_of_injective
  given: (p : MvPolynomial σ R) {f : R ->+* S₁} (hf : Injective f)
  proof: by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_map_subset _ _
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map]; rw [← f.map_zero] at hx
  exact hf hx

中文:
定理 support_map_of_injective
  条件: (p : MvPolynomial σ R) {f : R ->+* S₁} (hf : Injective f)
  证明: by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_map_subset _ _
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map]; rw [← f.map_zero] at hx
  exact hf hx

Depends on / 依赖: Finset, Finset.Subset.antisymm, Finset.subset_iff, MvPolynomial, MvPolynomial.support_map_subset, Subset, antisymm, coeff_map, contrapose, f.map_zero, map_zero, mem_support_iff, subset_iff, support_map_subset
-/
theorem support_map_of_injective (p : MvPolynomial σ R) {f : R ->+* S₁} (hf : Injective f) :
    (map f p).support = p.support := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_map_subset _ _
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose hx
  rw [coeff_map]; rw [← f.map_zero] at hx
  exact hf hx

/--
theorem `C_dvd_iff_map_hom_eq_zero` / 定理 `C_dvd_iff_map_hom_eq_zero`

English:
theorem C_dvd_iff_map_hom_eq_zero
  statement: (q : R ->+* S₁) (r : R) (hr : forall r' : R, q r' = 0 ↔ r ∣ r')
  proof: by
  rw [C_dvd_iff_dvd_coeff]; rw [MvPolynomial.ext_iff]
  simp only [coeff_map, coeff_zero, hr]

中文:
定理 C_dvd_iff_map_hom_eq_zero
  结论: (q : R ->+* S₁) (r : R) (hr : 对任意 r' : R, q r' = 0 ↔ r ∣ r')
  证明: by
  rw [C_dvd_iff_dvd_coeff]; rw [MvPolynomial.ext_iff]
  simp only [coeff_map, coeff_zero, hr]

Depends on / 依赖: C_dvd_iff_dvd_coeff, MvPolynomial, MvPolynomial.ext_iff, coeff_map, coeff_zero, ext_iff
-/
theorem C_dvd_iff_map_hom_eq_zero (q : R ->+* S₁) (r : R) (hr : forall r' : R, q r' = 0 ↔ r ∣ r')
    (φ : MvPolynomial σ R) : C r ∣ φ ↔ map q φ = 0 := by
  rw [C_dvd_iff_dvd_coeff]; rw [MvPolynomial.ext_iff]
  simp only [coeff_map, coeff_zero, hr]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_mapRange_eq_iff` / 定理 `map_mapRange_eq_iff`

English:
theorem map_mapRange_eq_iff
  given: (f : R ->+* S₁) (g : S₁ -> R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁)
  proof: by
  simp_rw [MvPolynomial.ext_iff, coeff_map]; rfl

中文:
定理 map_mapRange_eq_iff
  条件: (f : R ->+* S₁) (g : S₁ -> R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁)
  证明: by
  simp_rw [MvPolynomial.ext_iff, coeff_map]; rfl

Depends on / 依赖: MvPolynomial, MvPolynomial.ext_iff, coeff_map, ext_iff, simp_rw
-/
theorem map_mapRange_eq_iff (f : R ->+* S₁) (g : S₁ -> R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) :
    map f (.ofCoeff <| Finsupp.mapRange g hg <| AddMonoidAlgebra.coeff φ) = φ ↔
      forall d, f (g (coeff d φ)) = coeff d φ := by
  simp_rw [MvPolynomial.ext_iff, coeff_map]; rfl

/--
lemma `coeffs_map` / 引理 `coeffs_map`

English:
lemma coeffs_map
  given: (f : R ->+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁]
  proof: by
  classical
  induction p using induction_on'' with
  | C a => aesop (add simp coeffs_C)
  | mul_X p n ih => simpa
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add (disjoint_support_monomial ha hs)]; rw [map_add]; rw [coeffs_add]
    · rw [Finset.image_union, Finset.union_subset_iff]
    

中文:
引理 coeffs_map
  条件: (f : R ->+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁]
  证明: by
  classical
  induction p using induction_on'' with
  | C a => aesop (add simp coeffs_C)
  | mul_X p n ih => simpa
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add (disjoint_support_monomial ha hs)]; rw [map_add]; rw [coeffs_add]
    · rw [Finset.image_union, Finset.union_subset_iff]
    

Depends on / 依赖: Finset, Finset.disjoint_of_subset_left, Finset.disjoint_of_subset_right, Finset.image_union, Finset.union_subset_iff, classical, coeffs_C, coeffs_add, disjoint_of_subset_left, disjoint_of_subset_right, disjoint_support_monomial, hp.trans, ih.trans, image_union, induction_on, map_add, monomial_add, mul_X, support_map_subset, union_subset_iff
-/
lemma coeffs_map (f : R ->+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁] :
    (map f p).coeffs subseteq p.coeffs.image f := by
  classical
  induction p using induction_on'' with
  | C a => aesop (add simp coeffs_C)
  | mul_X p n ih => simpa
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add (disjoint_support_monomial ha hs)]; rw [map_add]; rw [coeffs_add]
    · rw [Finset.image_union, Finset.union_subset_iff]
      exact ⟨ih.trans (by simp), hp.trans (by simp)⟩
· exact Finset.disjoint_of_subset_left (support_map_subset _ _)
Finset.disjoint_of_subset_right (support_map_subset _ _)
          disjoint_support_monomial ha hs

@[simp]
/--
lemma `coe_coeffs_map` / 引理 `coe_coeffs_map`

English:
lemma coe_coeffs_map
  given: (f : R ->+* S₁) (p : MvPolynomial σ R)
  proof: by
  classical
  exact mod_cast coeffs_map f p

中文:
引理 coe_coeffs_map
  条件: (f : R ->+* S₁) (p : MvPolynomial σ R)
  证明: by
  classical
  exact mod_cast coeffs_map f p

Depends on / 依赖: classical, coeffs_map, mod_cast
-/
lemma coe_coeffs_map (f : R ->+* S₁) (p : MvPolynomial σ R) :
    ((map f p).coeffs : Set S₁) subseteq f '' p.coeffs := by
  classical
  exact mod_cast coeffs_map f p

/--
lemma `mem_range_map_iff_coeffs_subset` / 引理 `mem_range_map_iff_coeffs_subset`

English:
lemma mem_range_map_iff_coeffs_subset
  given: {f : R ->+* S₁} {x : MvPolynomial σ S₁}
  proof: by
  classical
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨p, rfl⟩ := hx
    exact subset_trans (coe_coeffs_map f p) (by simp)
  · induction x using induction_on'' with
    | C a =>
      by_cases h : a = 0
      · subst h
        exact ⟨0, by simp⟩
      · simp only [coeffs_C, h, reduceIte, F

中文:
引理 mem_range_map_iff_coeffs_subset
  条件: {f : R ->+* S₁} {x : MvPolynomial σ S₁}
  证明: by
  classical
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨p, rfl⟩ := hx
    exact subset_trans (coe_coeffs_map f p) (by simp)
  · induction x using induction_on'' with
    | C a =>
      by_cases h : a = 0
      · subst h
        exact ⟨0, by simp⟩
      · simp only [coeffs_C, h, reduceIte, F

Depends on / 依赖: Finset, Finset.coe_singleton, Set.singleton_subset_iff, classical, coe_coeffs_map, coe_singleton, coeffs_C, coeffs_add, coeffs_mul_X, induction_on, monomial_add, mul_X, reduceIte, singleton_subset_iff, subset_trans
-/
lemma mem_range_map_iff_coeffs_subset {f : R ->+* S₁} {x : MvPolynomial σ S₁} :
    x in Set.range (MvPolynomial.map f) ↔ (x.coeffs : Set _) subseteq .range f := by
  classical
  refine ⟨fun hx => ?_, fun hx => ?_⟩
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

variable [Algebra R S₁] (g : σ -> S₁)

variable (R) in
/--
Definition of `eval₂AlgHom` / `eval₂AlgHom` 的定义

English:
definition eval₂AlgHom
  signature: : MvPolynomial σ R ->ₐ[R] S₁
  body: { eval₂Hom (algebraMap R S₁) g with
    commutes' r := by simp }

中文:
定义 eval₂AlgHom
  签名: : MvPolynomial σ R ->ₐ[R] S₁
  定义体: { eval₂Hom (algebraMap R S₁) g with
    commutes' r := by simp }

Depends on / 依赖: algebraMap, commutes
-/
def eval₂AlgHom : MvPolynomial σ R ->ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) g with
    commutes' r := by simp }

/--
theorem `eval₂AlgHom_apply` / 定理 `eval₂AlgHom_apply`

English:
theorem eval₂AlgHom_apply
  given: (P : MvPolynomial σ R)
  proof: rfl

@[simp]

中文:
定理 eval₂AlgHom_apply
  条件: (P : MvPolynomial σ R)
  证明: rfl

@[simp]
-/
theorem eval₂AlgHom_apply (P : MvPolynomial σ R) :
    eval₂AlgHom R g P = eval₂Hom (algebraMap R S₁) g P := rfl

@[simp]
/--
theorem `coe_eval₂AlgHom` / 定理 `coe_eval₂AlgHom`

English:
theorem coe_eval₂AlgHom
  statement: ⇑(eval₂AlgHom R g) = eval₂ (algebraMap R S₁) g
  proof: rfl

@[simp]

中文:
定理 coe_eval₂AlgHom
  结论: ⇑(eval₂AlgHom R g) = eval₂ (algebraMap R S₁) g
  证明: rfl

@[simp]
-/
theorem coe_eval₂AlgHom : ⇑(eval₂AlgHom R g) = eval₂ (algebraMap R S₁) g := rfl

@[simp]
/--
theorem `eval₂AlgHom_X` / 定理 `eval₂AlgHom_X`

English:
theorem eval₂AlgHom_X
  given: (i : σ)
  proof: eval₂_X (algebraMap R S₁) g i

中文:
定理 eval₂AlgHom_X
  条件: (i : σ)
  证明: eval₂_X (algebraMap R S₁) g i

Depends on / 依赖: algebraMap
-/
theorem eval₂AlgHom_X (i : σ) :
    eval₂AlgHom R g (X i : MvPolynomial σ R) = g i := eval₂_X (algebraMap R S₁) g i

end Algebra

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  body: AddMonoidAlgebra.mapAlgHom _ f

@[simp]

中文:
定义 mapAlgHom
  签名: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  定义体: AddMonoidAlgebra.mapAlgHom _ f

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapAlgHom, mapAlgHom
-/
def mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂) :
    MvPolynomial σ S₁ ->ₐ[R] MvPolynomial σ S₂ := AddMonoidAlgebra.mapAlgHom _ f

@[simp]
/--
lemma `mapAlgHom_apply` / 引理 `mapAlgHom_apply`

English:
lemma mapAlgHom_apply
  statement: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  proof: rfl

@[simp]

中文:
引理 mapAlgHom_apply
  结论: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  证明: rfl

@[simp]
-/
lemma mapAlgHom_apply [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
    (x : MvPolynomial σ S₁) : mapAlgHom f x = map f x := rfl

@[simp]
/--
theorem `mapAlgHom_id` / 定理 `mapAlgHom_id`

English:
theorem mapAlgHom_id
  given: [Algebra R S₁]
  proof: AlgHom.ext map_id

@[simp]

中文:
定理 mapAlgHom_id
  条件: [Algebra R S₁]
  证明: AlgHom.ext map_id

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext, map_id
-/
theorem mapAlgHom_id [Algebra R S₁] :
    mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (MvPolynomial σ S₁) :=
  AlgHom.ext map_id

@[simp]
/--
theorem `mapAlgHom_coe_ringHom` / 定理 `mapAlgHom_coe_ringHom`

English:
theorem mapAlgHom_coe_ringHom
  given: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  proof: RingHom.mk_coe _ _ _ _ _

中文:
定理 mapAlgHom_coe_ringHom
  条件: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  证明: RingHom.mk_coe _ _ _ _ _

Depends on / 依赖: RingHom, RingHom.mk_coe, mk_coe
-/
theorem mapAlgHom_coe_ringHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂) :
    ↑(mapAlgHom f : _ ->ₐ[R] MvPolynomial σ S₂) =
      (map ↑f : MvPolynomial σ S₁ ->+* MvPolynomial σ S₂) :=
  RingHom.mk_coe _ _ _ _ _

/--
lemma `range_mapAlgHom` / 引理 `range_mapAlgHom`

English:
lemma range_mapAlgHom
  given: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  proof: by
  simp only [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range]
  ext
  erw [mem_range_map_iff_coeffs_subset, mem_coeffsIn_iff_coeffs_subset]
  simp [Set.subset_def]

中文:
引理 range_mapAlgHom
  条件: [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂)
  证明: by
  simp only [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range]
  ext
  erw [mem_range_map_iff_coeffs_subset, mem_coeffsIn_iff_coeffs_subset]
  simp [Set.subset_def]

Depends on / 依赖: AlgHom, AlgHom.coe_range, Set.subset_def, SetLike, SetLike.coe_set_eq, Subalgebra, Subalgebra.coe_toSubmodule, coe_range, coe_set_eq, coe_toSubmodule, mem_coeffsIn_iff_coeffs_subset, mem_range_map_iff_coeffs_subset, subset_def
-/
lemma range_mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂) :
    (mapAlgHom f).range.toSubmodule = coeffsIn σ f.range.toSubmodule := by
  simp only [← SetLike.coe_set_eq, Subalgebra.coe_toSubmodule, AlgHom.coe_range]
  ext
  erw [mem_range_map_iff_coeffs_subset, mem_coeffsIn_iff_coeffs_subset]
  simp [Set.subset_def]

end Map

section Aeval

/-! ### The algebra of multivariate polynomials -/


variable [Algebra R S₁] [CommSemiring S₂]
variable (f : σ -> S₁)

/--
Definition of `aeval` / `aeval` 的定义

English:
definition aeval
  signature: : MvPolynomial σ R ->ₐ[R] S₁
  body: { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }

中文:
定义 aeval
  签名: : MvPolynomial σ R ->ₐ[R] S₁
  定义体: { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }

Depends on / 依赖: algebraMap, commutes
-/
def aeval : MvPolynomial σ R ->ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }

/--
theorem `aeval_def` / 定理 `aeval_def`

English:
theorem aeval_def
  given: (p : MvPolynomial σ R)
  statement: aeval f p = eval₂ (algebraMap R S₁) f p
  proof: rfl

中文:
定理 aeval_def
  条件: (p : MvPolynomial σ R)
  结论: aeval f p = eval₂ (algebraMap R S₁) f p
  证明: rfl
-/
theorem aeval_def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p :=
  rfl

/--
theorem `aeval_eq_eval₂Hom` / 定理 `aeval_eq_eval₂Hom`

English:
theorem aeval_eq_eval₂Hom
  given: (p : MvPolynomial σ R)
  statement: aeval f p = eval₂Hom (algebraMap R S₁) f p
  proof: rfl

@[simp]

中文:
定理 aeval_eq_eval₂Hom
  条件: (p : MvPolynomial σ R)
  结论: aeval f p = eval₂Hom (algebraMap R S₁) f p
  证明: rfl

@[simp]
-/
theorem aeval_eq_eval₂Hom (p : MvPolynomial σ R) : aeval f p = eval₂Hom (algebraMap R S₁) f p :=
  rfl

@[simp]
/--
lemma `coe_aeval_eq_eval` / 引理 `coe_aeval_eq_eval`

English:
lemma coe_aeval_eq_eval
  proof: rfl

@[simp]

中文:
引理 coe_aeval_eq_eval
  证明: rfl

@[simp]
-/
lemma coe_aeval_eq_eval :
    RingHomClass.toRingHom (aeval f : MvPolynomial σ S₁ ->ₐ[S₁] S₁) = eval f :=
  rfl

@[simp]
/--
lemma `aeval_eq_eval` / 引理 `aeval_eq_eval`

English:
lemma aeval_eq_eval
  statement: (aeval f : MvPolynomial σ S₁ -> S₁) = eval f
  proof: rfl

@[simp]

中文:
引理 aeval_eq_eval
  结论: (aeval f : MvPolynomial σ S₁ -> S₁) = eval f
  证明: rfl

@[simp]
-/
lemma aeval_eq_eval : (aeval f : MvPolynomial σ S₁ -> S₁) = eval f := rfl

@[simp]
/--
theorem `aeval_X` / 定理 `aeval_X`

English:
theorem aeval_X
  given: (s : σ)
  statement: aeval f (X s : MvPolynomial σ R) = f s
  proof: eval₂_X _ _ _

中文:
定理 aeval_X
  条件: (s : σ)
  结论: aeval f (X s : MvPolynomial σ R) = f s
  证明: eval₂_X _ _ _
-/
theorem aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R) = f s :=
  eval₂_X _ _ _

/--
theorem `aeval_C` / 定理 `aeval_C`

English:
theorem aeval_C
  given: (r : R)
  statement: aeval f (C r) = algebraMap R S₁ r
  proof: eval₂_C _ _ _

中文:
定理 aeval_C
  条件: (r : R)
  结论: aeval f (C r) = algebraMap R S₁ r
  证明: eval₂_C _ _ _
-/
theorem aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ r :=
  eval₂_C _ _ _

/--
theorem `aeval_ofNat` / 定理 `aeval_ofNat`

English:
theorem aeval_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: map_ofNat _ _

中文:
定理 aeval_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: map_ofNat _ _
-/
@[simp] theorem aeval_ofNat (n : Nat) [n.AtLeastTwo] :
    aeval f (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  map_ofNat _ _

/--
theorem `aeval_unique` / 定理 `aeval_unique`

English:
theorem aeval_unique
  given: (φ : MvPolynomial σ R ->ₐ[R] S₁)
  statement: φ = aeval (φ ∘ X)
  proof: by
  ext i
  simp

中文:
定理 aeval_unique
  条件: (φ : MvPolynomial σ R ->ₐ[R] S₁)
  结论: φ = aeval (φ ∘ X)
  证明: by
  ext i
  simp
-/
theorem aeval_unique (φ : MvPolynomial σ R ->ₐ[R] S₁) : φ = aeval (φ ∘ X) := by
  ext i
  simp

/--
theorem `aeval_X_left` / 定理 `aeval_X_left`

English:
theorem aeval_X_left
  statement: aeval X = AlgHom.id R (MvPolynomial σ R)
  proof: (aeval_unique (AlgHom.id R _)).symm

中文:
定理 aeval_X_left
  结论: aeval X = AlgHom.id R (MvPolynomial σ R)
  证明: (aeval_unique (AlgHom.id R _)).symm

Depends on / 依赖: AlgHom, AlgHom.id, aeval_unique
-/
theorem aeval_X_left : aeval X = AlgHom.id R (MvPolynomial σ R) :=
  (aeval_unique (AlgHom.id R _)).symm

/--
theorem `aeval_X_left_apply` / 定理 `aeval_X_left_apply`

English:
theorem aeval_X_left_apply
  given: (p : MvPolynomial σ R)
  statement: aeval X p = p
  proof: AlgHom.congr_fun aeval_X_left p

中文:
定理 aeval_X_left_apply
  条件: (p : MvPolynomial σ R)
  结论: aeval X p = p
  证明: AlgHom.congr_fun aeval_X_left p

Depends on / 依赖: AlgHom, AlgHom.congr_fun, aeval_X_left, congr_fun
-/
theorem aeval_X_left_apply (p : MvPolynomial σ R) : aeval X p = p :=
  AlgHom.congr_fun aeval_X_left p

/--
theorem `comp_aeval` / 定理 `comp_aeval`

English:
theorem comp_aeval
  given: {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B)
  proof: by
  ext i
  simp

中文:
定理 comp_aeval
  条件: {B : 类型} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B)
  证明: by
  ext i
  simp
-/
theorem comp_aeval {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B) :
    φ.comp (aeval f) = aeval fun i => φ (f i) := by
  ext i
  simp

/--
lemma `comp_aeval_apply` / 引理 `comp_aeval_apply`

English:
lemma comp_aeval_apply
  statement: {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B)
  proof: by
  rw [← comp_aeval]; rw [AlgHom.coe_comp]; rw [comp_apply]

@[simp]

中文:
引理 comp_aeval_apply
  结论: {B : 类型} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B)
  证明: by
  rw [← comp_aeval]; rw [AlgHom.coe_comp]; rw [comp_apply]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, coe_comp, comp_aeval, comp_apply
-/
lemma comp_aeval_apply {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ ->ₐ[R] B)
    (p : MvPolynomial σ R) :
    φ (aeval f p) = aeval (fun i => φ (f i)) p := by
  rw [← comp_aeval]; rw [AlgHom.coe_comp]; rw [comp_apply]

@[simp]
/--
theorem `map_aeval` / 定理 `map_aeval`

English:
theorem map_aeval
  given: {B : Type*} [CommSemiring B] (g : σ -> S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R)
  proof: by
  rw [← comp_eval₂Hom]
  rfl

中文:
定理 map_aeval
  条件: {B : 类型} [CommSemiring B] (g : σ -> S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R)
  证明: by
  rw [← comp_eval₂Hom]
  rfl
-/
theorem map_aeval {B : Type*} [CommSemiring B] (g : σ -> S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) :
    φ (aeval g p) = eval₂Hom (φ.comp (algebraMap R S₁)) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl

/--
theorem `aeval_range` / 定理 `aeval_range`

English:
theorem aeval_range
  statement: (aeval f).range = Algebra.adjoin R (Set.range f)
  proof: by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | C a => exact aeval_C f a ▸ Subsemiring.subset_closure (Or.inl (Set.mem_range_self a))
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp

中文:
定理 aeval_range
  结论: (aeval f).range = Algebra.adjoin R (Set.range f)
  证明: by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | C a => exact aeval_C f a ▸ Subsemiring.subset_closure (Or.inl (Set.mem_range_self a))
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Algebra, Algebra.adjoin_le_iff, Algebra.subset_adjoin, Or.inl, RingHom, RingHom.coe_coe, Set.mem_range_self, Subalgebra, Subalgebra.add_mem, Subalgebra.mul_mem, Subsemiring, Subsemiring.subset_closure, add_mem, adjoin_le_iff, aeval_C, aeval_X, coe_coe, induction_on
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
/--
theorem `eval₂Hom_zero` / 定理 `eval₂Hom_zero`

English:
theorem eval₂Hom_zero
  given: (f : R ->+* S₂)
  statement: eval₂Hom f (0 : σ -> S₂) = f.comp constantCoeff
  proof: by
  ext <;> simp

@[simp]

中文:
定理 eval₂Hom_zero
  条件: (f : R ->+* S₂)
  结论: eval₂Hom f (0 : σ -> S₂) = f.comp constantCoeff
  证明: by
  ext <;> simp

@[simp]
-/
theorem eval₂Hom_zero (f : R ->+* S₂) : eval₂Hom f (0 : σ -> S₂) = f.comp constantCoeff := by
  ext <;> simp

@[simp]
/--
theorem `eval₂Hom_zero'` / 定理 `eval₂Hom_zero'`

English:
theorem eval₂Hom_zero'
  given: (f : R ->+* S₂)
  statement: eval₂Hom f (fun _ => 0 : σ -> S₂) = f.comp constantCoeff
  proof: eval₂Hom_zero f

中文:
定理 eval₂Hom_zero'
  条件: (f : R ->+* S₂)
  结论: eval₂Hom f (fun _ => 0 : σ -> S₂) = f.comp constantCoeff
  证明: eval₂Hom_zero f
-/
theorem eval₂Hom_zero' (f : R ->+* S₂) : eval₂Hom f (fun _ => 0 : σ -> S₂) = f.comp constantCoeff :=
  eval₂Hom_zero f

/--
theorem `eval₂Hom_zero_apply` / 定理 `eval₂Hom_zero_apply`

English:
theorem eval₂Hom_zero_apply
  given: (f : R ->+* S₂) (p : MvPolynomial σ R)
  proof: RingHom.congr_fun (eval₂Hom_zero f) p

中文:
定理 eval₂Hom_zero_apply
  条件: (f : R ->+* S₂) (p : MvPolynomial σ R)
  证明: RingHom.congr_fun (eval₂Hom_zero f) p

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun
-/
theorem eval₂Hom_zero_apply (f : R ->+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (0 : σ -> S₂) p = f (constantCoeff p) :=
  RingHom.congr_fun (eval₂Hom_zero f) p

/--
theorem `eval₂Hom_zero'_apply` / 定理 `eval₂Hom_zero'_apply`

English:
theorem eval₂Hom_zero'_apply
  given: (f : R ->+* S₂) (p : MvPolynomial σ R)
  proof: eval₂Hom_zero_apply f p

@[simp]

中文:
定理 eval₂Hom_zero'_apply
  条件: (f : R ->+* S₂) (p : MvPolynomial σ R)
  证明: eval₂Hom_zero_apply f p

@[simp]
-/
theorem eval₂Hom_zero'_apply (f : R ->+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (fun _ => 0 : σ -> S₂) p = f (constantCoeff p) :=
  eval₂Hom_zero_apply f p

@[simp]
/--
theorem `eval₂_zero_apply` / 定理 `eval₂_zero_apply`

English:
theorem eval₂_zero_apply
  given: (f : R ->+* S₂) (p : MvPolynomial σ R)
  proof: eval₂Hom_zero_apply _ _

@[simp]

中文:
定理 eval₂_zero_apply
  条件: (f : R ->+* S₂) (p : MvPolynomial σ R)
  证明: eval₂Hom_zero_apply _ _

@[simp]
-/
theorem eval₂_zero_apply (f : R ->+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (0 : σ -> S₂) p = f (constantCoeff p) :=
  eval₂Hom_zero_apply _ _

@[simp]
/--
theorem `eval₂_zero'_apply` / 定理 `eval₂_zero'_apply`

English:
theorem eval₂_zero'_apply
  given: (f : R ->+* S₂) (p : MvPolynomial σ R)
  proof: eval₂_zero_apply f p

@[simp]

中文:
定理 eval₂_zero'_apply
  条件: (f : R ->+* S₂) (p : MvPolynomial σ R)
  证明: eval₂_zero_apply f p

@[simp]
-/
theorem eval₂_zero'_apply (f : R ->+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (fun _ => 0 : σ -> S₂) p = f (constantCoeff p) :=
  eval₂_zero_apply f p

@[simp]
/--
theorem `aeval_zero` / 定理 `aeval_zero`

English:
theorem aeval_zero
  given: (p : MvPolynomial σ R)
  proof: eval₂Hom_zero_apply (algebraMap R S₁) p

@[simp]

中文:
定理 aeval_zero
  条件: (p : MvPolynomial σ R)
  证明: eval₂Hom_zero_apply (algebraMap R S₁) p

@[simp]

Depends on / 依赖: algebraMap
-/
theorem aeval_zero (p : MvPolynomial σ R) :
    aeval (0 : σ -> S₁) p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_zero_apply (algebraMap R S₁) p

@[simp]
/--
theorem `aeval_zero'` / 定理 `aeval_zero'`

English:
theorem aeval_zero'
  given: (p : MvPolynomial σ R)
  proof: aeval_zero p

@[simp]

中文:
定理 aeval_zero'
  条件: (p : MvPolynomial σ R)
  证明: aeval_zero p

@[simp]

Depends on / 依赖: aeval_zero
-/
theorem aeval_zero' (p : MvPolynomial σ R) :
    aeval (fun _ => 0 : σ -> S₁) p = algebraMap _ _ (constantCoeff p) :=
  aeval_zero p

@[simp]
/--
theorem `eval_zero` / 定理 `eval_zero`

English:
theorem eval_zero
  statement: eval (0 : σ -> R) = constantCoeff
  proof: eval₂Hom_zero _

@[simp]

中文:
定理 eval_zero
  结论: eval (0 : σ -> R) = constantCoeff
  证明: eval₂Hom_zero _

@[simp]
-/
theorem eval_zero : eval (0 : σ -> R) = constantCoeff :=
  eval₂Hom_zero _

@[simp]
/--
theorem `eval_zero'` / 定理 `eval_zero'`

English:
theorem eval_zero'
  statement: eval (fun _ => 0 : σ -> R) = constantCoeff
  proof: eval₂Hom_zero _

中文:
定理 eval_zero'
  结论: eval (fun _ => 0 : σ -> R) = constantCoeff
  证明: eval₂Hom_zero _
-/
theorem eval_zero' : eval (fun _ => 0 : σ -> R) = constantCoeff :=
  eval₂Hom_zero _

/--
theorem `aeval_monomial` / 定理 `aeval_monomial`

English:
theorem aeval_monomial
  given: (g : σ -> S₁) (d : σ ->₀ Nat) (r : R)
  proof: eval₂Hom_monomial _ _ _ _

中文:
定理 aeval_monomial
  条件: (g : σ -> S₁) (d : σ ->₀ 自然数) (r : R)
  证明: eval₂Hom_monomial _ _ _ _
-/
theorem aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat) (r : R) :
    aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ k :=
  eval₂Hom_monomial _ _ _ _

/--
theorem `eval₂Hom_eq_zero` / 定理 `eval₂Hom_eq_zero`

English:
theorem eval₂Hom_eq_zero
  statement: (f : R ->+* S₂) (g : σ -> S₂) (φ : MvPolynomial σ R)
  proof: by
  rw [φ.as_sum]; rw [map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨i, hi, hgi⟩ : exists i in d.support, g i = 0 := h d (Finsupp.mem_support_iff.mp hd)
  rw [eval₂Hom_monomial]; rw [Finsupp.prod]; rw [Finset.prod_eq_zero hi]; rw [mul_zero]
  rw [hgi]; rw [zero_pow]
  rwa [← Finsupp

中文:
定理 eval₂Hom_eq_zero
  结论: (f : R ->+* S₂) (g : σ -> S₂) (φ : MvPolynomial σ R)
  证明: by
  rw [φ.as_sum]; rw [map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨i, hi, hgi⟩ : exists i in d.support, g i = 0 := h d (Finsupp.mem_support_iff.mp hd)
  rw [eval₂Hom_monomial]; rw [Finsupp.prod]; rw [Finset.prod_eq_zero hi]; rw [mul_zero]
  rw [hgi]; rw [zero_pow]
  rwa [← Finsupp

Depends on / 依赖: Finset, Finset.prod_eq_zero, Finset.sum_eq_zero, Finsupp, Finsupp.mem_support_iff, Finsupp.mem_support_iff.mp, Finsupp.prod, as_sum, d.support, map_sum, mem_support_iff, mul_zero, prod_eq_zero, sum_eq_zero, support, zero_pow
-/
theorem eval₂Hom_eq_zero (f : R ->+* S₂) (g : σ -> S₂) (φ : MvPolynomial σ R)
    (h : forall d, φ.coeff d != 0 -> exists i in d.support, g i = 0) : eval₂Hom f g φ = 0 := by
  rw [φ.as_sum]; rw [map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨i, hi, hgi⟩ : exists i in d.support, g i = 0 := h d (Finsupp.mem_support_iff.mp hd)
  rw [eval₂Hom_monomial]; rw [Finsupp.prod]; rw [Finset.prod_eq_zero hi]; rw [mul_zero]
  rw [hgi]; rw [zero_pow]
  rwa [← Finsupp.mem_support_iff]

/--
theorem `aeval_eq_zero` / 定理 `aeval_eq_zero`

English:
theorem aeval_eq_zero
  statement: [Algebra R S₂] (f : σ -> S₂) (φ : MvPolynomial σ R)
  proof: eval₂Hom_eq_zero _ _ _ h

中文:
定理 aeval_eq_zero
  结论: [Algebra R S₂] (f : σ -> S₂) (φ : MvPolynomial σ R)
  证明: eval₂Hom_eq_zero _ _ _ h
-/
theorem aeval_eq_zero [Algebra R S₂] (f : σ -> S₂) (φ : MvPolynomial σ R)
    (h : forall d, φ.coeff d != 0 -> exists i in d.support, f i = 0) : aeval f φ = 0 :=
  eval₂Hom_eq_zero _ _ _ h

/--
theorem `aeval_sum` / 定理 `aeval_sum`

English:
theorem aeval_sum
  given: {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R)
  proof: map_sum (MvPolynomial.aeval f) _ _

中文:
定理 aeval_sum
  条件: {ι : 类型} (s : Finset ι) (φ : ι -> MvPolynomial σ R)
  证明: map_sum (MvPolynomial.aeval f) _ _

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, map_sum
-/
theorem aeval_sum {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) :
    aeval f (∑ i in s, φ i) = ∑ i in s, aeval f (φ i) :=
  map_sum (MvPolynomial.aeval f) _ _

/--
theorem `aeval_prod` / 定理 `aeval_prod`

English:
theorem aeval_prod
  given: {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R)
  proof: map_prod (MvPolynomial.aeval f) _ _

中文:
定理 aeval_prod
  条件: {ι : 类型} (s : Finset ι) (φ : ι -> MvPolynomial σ R)
  证明: map_prod (MvPolynomial.aeval f) _ _

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, map_prod
-/
theorem aeval_prod {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) :
    aeval f (∏ i in s, φ i) = ∏ i in s, aeval f (φ i) :=
  map_prod (MvPolynomial.aeval f) _ _

variable (R)

/--
theorem `_root_.Algebra.adjoin_range_eq_range_aeval` / 定理 `_root_.Algebra.adjoin_range_eq_range_aeval`

English:
theorem _root_.Algebra.adjoin_range_eq_range_aeval
  proof: by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]

中文:
定理 _root_.Algebra.adjoin_range_eq_range_aeval
  证明: by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, Function, Function.comp_def, MvPolynomial, MvPolynomial.adjoin_range_X, MvPolynomial.aeval_X, Set.range_comp, adjoin_range_X, aeval_X, comp_def, map_adjoin, map_top, range_comp
-/
theorem _root_.Algebra.adjoin_range_eq_range_aeval :
    Algebra.adjoin R (Set.range f) = (MvPolynomial.aeval f).range := by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]

/--
theorem `_root_.Algebra.adjoin_eq_range` / 定理 `_root_.Algebra.adjoin_eq_range`

English:
theorem _root_.Algebra.adjoin_eq_range
  given: (s : Set S₁)
  proof: by
  rw [← Algebra.adjoin_range_eq_range_aeval]; rw [Subtype.range_coe]

中文:
定理 _root_.Algebra.adjoin_eq_range
  条件: (s : Set S₁)
  证明: by
  rw [← Algebra.adjoin_range_eq_range_aeval]; rw [Subtype.range_coe]

Depends on / 依赖: Algebra, Algebra.adjoin_range_eq_range_aeval, Subtype, Subtype.range_coe, adjoin_range_eq_range_aeval, range_coe
-/
theorem _root_.Algebra.adjoin_eq_range (s : Set S₁) :
    Algebra.adjoin R s = (MvPolynomial.aeval ((↑) : s -> S₁)).range := by
  rw [← Algebra.adjoin_range_eq_range_aeval]; rw [Subtype.range_coe]

end Aeval

section AevalTower

variable {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
variable [Algebra S R] [Algebra S A] [Algebra S B]

/--
Definition of `aevalTower` / `aevalTower` 的定义

English:
definition aevalTower
  signature: (f : R ->ₐ[S] A) (X : σ -> A)
  body: { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }

中文:
定义 aevalTower
  签名: (f : R ->ₐ[S] A) (X : σ -> A)
  定义体: { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, MvPolynomial, algebraMap_eq, commutes
-/
def aevalTower (f : R ->ₐ[S] A) (X : σ -> A) : MvPolynomial σ R ->ₐ[S] A :=
  { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }

variable (g : R ->ₐ[S] A) (y : σ -> A)

@[simp]
/--
theorem `aevalTower_X` / 定理 `aevalTower_X`

English:
theorem aevalTower_X
  given: (i : σ)
  statement: aevalTower g y (X i) = y i
  proof: eval₂_X _ _ _

@[simp]

中文:
定理 aevalTower_X
  条件: (i : σ)
  结论: aevalTower g y (X i) = y i
  证明: eval₂_X _ _ _

@[simp]
-/
theorem aevalTower_X (i : σ) : aevalTower g y (X i) = y i :=
  eval₂_X _ _ _

@[simp]
/--
theorem `aevalTower_C` / 定理 `aevalTower_C`

English:
theorem aevalTower_C
  given: (x : R)
  statement: aevalTower g y (C x) = g x
  proof: eval₂_C _ _ _

@[simp]

中文:
定理 aevalTower_C
  条件: (x : R)
  结论: aevalTower g y (C x) = g x
  证明: eval₂_C _ _ _

@[simp]

Depends on / 依赖: CauSeq, CauSeq.ring, mul_comm
-/
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _ _

@[simp]
/--
theorem `aevalTower_ofNat` / 定理 `aevalTower_ofNat`

English:
theorem aevalTower_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: _root_.map_ofNat _ _

@[simp]

中文:
定理 aevalTower_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: _root_.map_ofNat _ _

@[simp]

Depends on / 依赖: _root_, _root_.map_ofNat, map_ofNat
-/
theorem aevalTower_ofNat (n : Nat) [n.AtLeastTwo] :
    aevalTower g y (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
/--
theorem `aevalTower_comp_C` / 定理 `aevalTower_comp_C`

English:
theorem aevalTower_comp_C
  statement: (aevalTower g y : MvPolynomial σ R ->+* A).comp C = g
  proof: RingHom.ext aevalTower_C _ _

中文:
定理 aevalTower_comp_C
  结论: (aevalTower g y : MvPolynomial σ R ->+* A).comp C = g
  证明: RingHom.ext aevalTower_C _ _

Depends on / 依赖: RingHom, RingHom.ext, aevalTower_C
-/
theorem aevalTower_comp_C : (aevalTower g y : MvPolynomial σ R ->+* A).comp C = g :=
RingHom.ext aevalTower_C _ _

/--
theorem `aevalTower_algebraMap` / 定理 `aevalTower_algebraMap`

English:
theorem aevalTower_algebraMap
  given: (x : R)
  statement: aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x
  proof: eval₂_C _ _ _

中文:
定理 aevalTower_algebraMap
  条件: (x : R)
  结论: aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x
  证明: eval₂_C _ _ _
-/
theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x :=
  eval₂_C _ _ _

/--
theorem `aevalTower_comp_algebraMap` / 定理 `aevalTower_comp_algebraMap`

English:
theorem aevalTower_comp_algebraMap
  proof: aevalTower_comp_C _ _

中文:
定理 aevalTower_comp_algebraMap
  证明: aevalTower_comp_C _ _

Depends on / 依赖: aevalTower_comp_C
-/
theorem aevalTower_comp_algebraMap :
    (aevalTower g y : MvPolynomial σ R ->+* A).comp (algebraMap R (MvPolynomial σ R)) = g :=
  aevalTower_comp_C _ _

/--
theorem `aevalTower_toAlgHom` / 定理 `aevalTower_toAlgHom`

English:
theorem aevalTower_toAlgHom
  given: (x : R)
  proof: aevalTower_algebraMap _ _ _

@[simp]

中文:
定理 aevalTower_toAlgHom
  条件: (x : R)
  证明: aevalTower_algebraMap _ _ _

@[simp]

Depends on / 依赖: aevalTower_algebraMap
-/
theorem aevalTower_toAlgHom (x : R) :
    aevalTower g y (IsScalarTower.toAlgHom S R (MvPolynomial σ R) x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
/--
theorem `aevalTower_comp_toAlgHom` / 定理 `aevalTower_comp_toAlgHom`

English:
theorem aevalTower_comp_toAlgHom
  proof: AlgHom.coe_ringHom_injective aevalTower_comp_algebraMap _ _

@[simp]

中文:
定理 aevalTower_comp_toAlgHom
  证明: AlgHom.coe_ringHom_injective aevalTower_comp_algebraMap _ _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, aevalTower_comp_algebraMap, coe_ringHom_injective
-/
theorem aevalTower_comp_toAlgHom :
    (aevalTower g y).comp (IsScalarTower.toAlgHom S R (MvPolynomial σ R)) = g :=
AlgHom.coe_ringHom_injective aevalTower_comp_algebraMap _ _

@[simp]
/--
theorem `aevalTower_id` / 定理 `aevalTower_id`

English:
theorem aevalTower_id
  proof: by
  ext
  simp only [aevalTower_X, aeval_X]

@[simp]

中文:
定理 aevalTower_id
  证明: by
  ext
  simp only [aevalTower_X, aeval_X]

@[simp]

Depends on / 依赖: aevalTower_X, aeval_X
-/
theorem aevalTower_id :
    aevalTower (AlgHom.id S S) = (aeval : (σ -> S) -> MvPolynomial σ S ->ₐ[S] S) := by
  ext
  simp only [aevalTower_X, aeval_X]

@[simp]
/--
theorem `aevalTower_ofId` / 定理 `aevalTower_ofId`

English:
theorem aevalTower_ofId
  proof: by
  ext
  simp only [aeval_X, aevalTower_X]

中文:
定理 aevalTower_ofId
  证明: by
  ext
  simp only [aeval_X, aevalTower_X]

Depends on / 依赖: aevalTower_X, aeval_X
-/
theorem aevalTower_ofId :
    aevalTower (Algebra.ofId S A) = (aeval : (σ -> A) -> MvPolynomial σ S ->ₐ[S] A) := by
  ext
  simp only [aeval_X, aevalTower_X]

end AevalTower

section EvalMem

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

/--
theorem `eval₂_mem` / 定理 `eval₂_mem`

English:
theorem eval₂_mem
  statement: {f : R ->+* S} {p : MvPolynomial σ R} {s : subS}
  proof: by
  classical
  replace hs : forall i, f (p.coeff i) in s := by
    intro i
    by_cases hi : i in p.support
    · exact hs i hi
    · rw [MvPolynomial.notMem_support_iff.1 hi, f.map_zero]
      exact zero_mem s
  induction p using MvPolynomial.monomial_add_induction_on with
  | C a =>
    simpa us

中文:
定理 eval₂_mem
  结论: {f : R ->+* S} {p : MvPolynomial σ R} {s : subS}
  证明: by
  classical
  replace hs : forall i, f (p.coeff i) in s := by
    intro i
    by_cases hi : i in p.support
    · exact hs i hi
    · rw [MvPolynomial.notMem_support_iff.1 hi, f.map_zero]
      exact zero_mem s
  induction p using MvPolynomial.monomial_add_induction_on with
  | C a =>
    simpa us

Depends on / 依赖: MvPolynomial, MvPolynomial.monomial_add_induction_on, MvPolynomial.notMem_support_iff, add_mem, classical, f.map_zero, map_zero, monomial_add, monomial_add_induction_on, mul_mem, notMem_support_iff, p.coeff, p.support, pow_mem, prod_mem, replace, support, zero_mem
-/
theorem eval₂_mem {f : R ->+* S} {p : MvPolynomial σ R} {s : subS}
    (hs : forall i in p.support, f (p.coeff i) in s) {v : σ -> S} (hv : forall i, v i in s) :
    MvPolynomial.eval₂ f v p in s := by
  classical
  replace hs : forall i, f (p.coeff i) in s := by
    intro i
    by_cases hi : i in p.support
    · exact hs i hi
    · rw [MvPolynomial.notMem_support_iff.1 hi, f.map_zero]
      exact zero_mem s
  induction p using MvPolynomial.monomial_add_induction_on with
  | C a =>
    simpa using hs 0
  | monomial_add a b f ha _ ih =>
    rw [eval₂_add]; rw [eval₂_monomial]
    refine add_mem (mul_mem ?_ <| prod_mem fun i _ => pow_mem (hv _) _) (ih fun i => ?_)
    · simpa [MvPolynomial.notMem_support_iff.1 ha] using hs a
    have := hs i
    rw [coeff_add]; rw [coeff_monomial] at this
    split_ifs at this with h
    · subst h
      rw [MvPolynomial.notMem_support_iff.1 ha]; rw [map_zero]
      exact zero_mem _
    · rwa [zero_add] at this

/--
theorem `eval_mem` / 定理 `eval_mem`

English:
theorem eval_mem
  statement: {p : MvPolynomial σ S} {s : subS} (hs : forall i in p.support, p.coeff i in s) {v : σ -> S}
  proof: eval₂_mem hs hv

中文:
定理 eval_mem
  结论: {p : MvPolynomial σ S} {s : subS} (hs : 对任意 i in p.support, p.coeff i in s) {v : σ -> S}
  证明: eval₂_mem hs hv
-/
theorem eval_mem {p : MvPolynomial σ S} {s : subS} (hs : forall i in p.support, p.coeff i in s) {v : σ -> S}
    (hv : forall i, v i in s) : MvPolynomial.eval v p in s :=
  eval₂_mem hs hv

end EvalMem

variable {S T : Type*} [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

/--
lemma `aeval_sumElim` / 引理 `aeval_sumElim`

English:
lemma aeval_sumElim
  given: {σ τ : Type*} (p : MvPolynomial (σ oplus τ) R) (f : τ -> S) (g : σ -> T)
  proof: by
  induction p using MvPolynomial.induction_on with
  | C r => simp [← IsScalarTower.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i h => cases i <;> simp [h]

中文:
引理 aeval_sumElim
  条件: {σ τ : 类型} (p : MvPolynomial (σ oplus τ) R) (f : τ -> S) (g : σ -> T)
  证明: by
  induction p using MvPolynomial.induction_on with
  | C r => simp [← IsScalarTower.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i h => cases i <;> simp [h]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, MvPolynomial, MvPolynomial.induction_on, algebraMap_apply, induction_on, mul_X
-/
lemma aeval_sumElim {σ τ : Type*} (p : MvPolynomial (σ oplus τ) R) (f : τ -> S) (g : σ -> T) :
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
/--
Definition of `algebraMvPolynomial` / `algebraMvPolynomial` 的定义

English:
definition algebraMvPolynomial
  signature: : Algebra (MvPolynomial σ R) (MvPolynomial σ S)
  body: inferInstanceAs Algebra (AddMonoidAlgebra _ _) (AddMonoidAlgebra _ _)

中文:
定义 algebraMvPolynomial
  签名: : Algebra (MvPolynomial σ R) (MvPolynomial σ S)
  定义体: inferInstanceAs Algebra (AddMonoidAlgebra _ _) (AddMonoidAlgebra _ _)

Depends on / 依赖: AddMonoidAlgebra, Algebra
-/
noncomputable def algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPolynomial σ S) :=
inferInstanceAs Algebra (AddMonoidAlgebra _ _) (AddMonoidAlgebra _ _)

attribute [local instance] algebraMvPolynomial

-- We want this to have higher priority than `AddMonoidAlgebra.algebraMap_def`.
-- TODO: Unify `MvPolynomial.map` and `AddMonoidAlgebra.mapRingHom` so that this becomes useless.
@[simp high]
/--
lemma `algebraMap_def` / 引理 `algebraMap_def`

English:
lemma algebraMap_def
  proof: rfl

中文:
引理 algebraMap_def
  证明: rfl
-/
lemma algebraMap_def :
    algebraMap (MvPolynomial σ R) (MvPolynomial σ S) = MvPolynomial.map (algebraMap R S) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ S)
  body: IsScalarTower.of_algebraMap_eq' (by ext; simp [C, monomial, map])

中文:
实例 :
  签名: IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ S)
  定义体: IsScalarTower.of_algebraMap_eq' (by ext; simp [C, monomial, map])

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, monomial, of_algebraMap_eq
-/
instance : IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ S) :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp [C, monomial, map])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FaithfulSMul
  signature: R S] : FaithfulSMul (MvPolynomial σ R) (MvPolynomial σ S)
  body: (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

中文:
实例 [FaithfulSMul
  签名: R S] : FaithfulSMul (MvPolynomial σ R) (MvPolynomial σ S)
  定义体: (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, faithfulSMul_iff_algebraMap_injective, map_injective
-/
instance [FaithfulSMul R S] : FaithfulSMul (MvPolynomial σ R) (MvPolynomial σ S) :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

end Algebra

end MvPolynomial
