/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.NatPowAssoc
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Scalar-multiple polynomial evaluation

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power.  This
is a generalization of `Algebra.Polynomial.Eval`.

## Main definitions

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `Semiring`
  `R` at an element `x` of an `AddCommMonoid` `S` that has natural number powers and an `R`-action.
* `smeval.linearMap`: the `smeval` function as an `R`-linear map, when `S` is an `R`-module.
* `smeval.algebraMap`: the `smeval` function as an `R`-algebra map, when `S` is an `R`-algebra.

## Main results

* `smeval_monomial`: monomials evaluate as we expect.
* `smeval_add`, `smeval_smul`: linearity of evaluation, given an `R`-module.
* `smeval_mul`, `smeval_comp`: multiplicativity of evaluation, given power-associativity.
* `eval₂_smulOneHom_eq_smeval`, `leval_eq_smeval.linearMap`,
  `aeval_eq_smeval`, etc.: comparisons

## TODO

* `smeval_neg` and `smeval_intCast` for `R` a ring and `S` an `AddCommGroup`.
* Nonunital evaluation for polynomials with vanishing constant term for `Pow S ℕ+` (different file?)

-/

@[expose] public section

namespace Polynomial

section MulActionWithZero

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

/-- Scalar multiplication together with taking a natural number power. -/
/-
**Polynomial.smul_pow** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：smul_pow : Nat -> R -> S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication together with taking a natural number power.
-/
def smul_pow : ℕ → R → S := fun n r => r • x ^ n

/-- Evaluate a polynomial `p` in the scalar semiring `R` at an element `x` in the target `S` using
scalar multiple `R`-action. -/
irreducible_def smeval : S := p.sum (smul_pow x)

/-
**Polynomial.smeval_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_eq_sum : p.smeval x = p.sum (smul_pow x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_def`：∀ {R : Type u_3} [inst : Semiring R] (p : Polynom
ial R) {S : Type u_4} [inst_1 : AddCommMonoid S] [inst_2 : Pow S ℕ]   [inst_3 : 
MulActionWi…
-/
theorem smeval_eq_sum : p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

@[simp]
/-
**Polynomial.smeval_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_C : (C r).smeval x = r • x ^ 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `Polynomial.sum_C_index`：sum_C_index {a} {β} [AddCommMonoid β] {f : Nat -
> R -> β} (h : f 0 0 = 0) : (C a).sum f = f 0 a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smeval_C : (C r).smeval x = r • x ^ 0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]
/-
**Polynomial.smeval_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_monomial (n : Nat) : (monomial n r).smeval x = r • x ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `Polynomial.sum_monomial_index`：sum_monomial_index {S : Type*} [AddCommMo
noid S] {n : Nat} (a : R) (f : Nat -> R -> S) (hf : f n 0 = 0) : (monomial n a :
 R[X]).sum f = f n …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smeval_monomial (n : ℕ) :
    (monomial n r).smeval x = r • x ^ n := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]
/-
**Polynomial.eval_eq_smeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_eq_smeval : p.eval r = p.smeval r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_eq_sum`：eval_eq_sum : p.eval x = p.sum fun e a => a * x 
^ e
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
-/
theorem eval_eq_smeval : p.eval r = p.smeval r := by
  rw [eval_eq_sum, smeval_eq_sum]
  rfl
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_smulOneHom_eq_smeval (R : Type*) [Semiring R] {S : Type*} [Semiring S] [Module R S]
    [IsScalarTower R S S] (p : R[X]) (x : S) :
    p.eval₂ RingHom.smulOneHom x = p.smeval x := by
  rw [smeval_eq_sum, eval₂_eq_sum]
  congr 1 with e a
  simp only [RingHom.smulOneHom_apply, smul_one_mul, smul_pow]

variable (R)

@[simp]
/-
**Polynomial.smeval_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_zero : (0 : R[X]).smeval x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `Polynomial.sum_zero_index`：sum_zero_index {S : Type*} [AddCommMonoid S] 
(f : Nat -> R -> S) : (0 : R[X]).sum f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smeval_zero : (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, sum_zero_index]

@[simp]
/-
**Polynomial.smeval_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0 := by
  rw [← C_1, smeval_C]
  simp only [one_smul]

@[simp]
/-
**Polynomial.smeval_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_X : (X : R[X]).smeval x = x ^ 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `Polynomial.sum_X_index`：sum_X_index {S : Type*} [AddCommMonoid S] {f : N
at -> R -> S} (hf : f 1 0 = 0) : (X : R[X]).sum f = f 1 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smeval_X :
    (X : R[X]).smeval x = x ^ 1 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

@[simp]
/-
**Polynomial.smeval_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_X_pow {n : Nat} : (X ^ n : R[X]).smeval x = x ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `Polynomial.sum_monomial_index`：sum_monomial_index {S : Type*} [AddCommMo
noid S] {n : Nat} (a : R) (f : Nat -> R -> S) (hf : f n 0 = 0) : (monomial n a :
 R[X]).sum f = f n …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smeval_X_pow {n : ℕ} :
    (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

end MulActionWithZero

section Module

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

@[simp]
/-
**Polynomial.smeval_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_add : (p + q).smeval x = p.smeval x + q.smeval x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `Polynomial.sum_add_index`：sum_add_index {S : Type*} [AddCommMonoid S] (p
 q : R[X]) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) (h_add : forall a b₁ b
₂, f a (b₁ + b…
· 使用定理 `Polynomial.smul_pow.eq_1`：∀ {R : Type u_1} [inst : Semiring R] {S : Type
 u_2} [inst_1 : AddCommMonoid S] [inst_2 : Pow S ℕ]   [inst_3 : MulActionWithZer
o R S] (x : S)…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
theorem smeval_add : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [smeval_eq_sum]
  refine sum_add_index p q (smul_pow x) (fun _ ↦ ?_) (fun _ _ _ ↦ ?_)
  · rw [smul_pow, zero_smul]
  · rw [smul_pow, smul_pow, smul_pow, add_smul]
/-
**Polynomial.smeval_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_natCast (n : Nat) : (n : R[X]).smeval x = n • x ^ 0
参数：n : Nat。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Polynomial.smeval_zero`：smeval_zero : (0 : R[X]).smeval x = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
-/
theorem smeval_natCast (n : ℕ) : (n : R[X]).smeval x = n • x ^ 0 := by
  induction n with
  | zero => simp only [smeval_zero, Nat.cast_zero, zero_smul]
  | succ n ih => rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[simp]
/-
**Polynomial.smeval_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_smul (r : R) : (r • p).smeval x = r • p.smeval x
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smul_monomial`：smul_monomial {S} [SMulZeroClass S R] (a : S) 
(n : Nat) (b : R) : a • monomial n b = monomial n (a • b)
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem smeval_smul (r : R) : (r • p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => rw [smul_add, smeval_add, ph, qh, ← smul_add, smeval_add]
  | monomial n a => rw [smul_monomial, smeval_monomial, smeval_monomial, smul_assoc]

/-- `Polynomial.smeval` as a linear map. -/
/-
**Polynomial.smeval.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.smeval`。
形式化陈述：(R : Type u_1) →   [inst : Semiring R] →     {S : Type u_2} → [inst_1 : Ad
dCommMonoid S] → [Pow S ℕ] → [inst_3 : _root_.Module R S] → S → Polynomial R →ₗ[
R] S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.smeval` as a linear map.
-/
def smeval.linearMap : R[X] →ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := by simp only [smeval_add]
  map_smul' c f := by simp only [smeval_smul, RingHom.id_apply]

@[simp]
/-
**Polynomial.smeval.linearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.smeval
`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] (p : Polynomial R) {S : Type u_2} [in
st_1 : AddCommMonoid S] [inst_2 : Pow S ℕ]   [inst_3 : _root_.Module R S] (x : S
), (Polynomial.smeval.linearMap R x) p = p.smeval x
参数：R : Type u_1；p : Polynomial R；x : S；Polynomial.smeval.linearMap R x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval.linearMap_apply : smeval.linearMap R x p = p.smeval x := rfl
/-
**Polynomial.leval_coe_eq_smeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leval_coe_eq_smeval {R : Type*} [Semiring R] (r : R) : ⇑(leval r) = fun p 
=> p.smeval r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leval_apply`：∀ {R : Type u_1} [inst : Semiring R] (r : R) (f 
: Polynomial R), (Polynomial.leval r) f = Polynomial.eval r f
· 使用定理 `Polynomial.eval_eq_smeval`：eval_eq_smeval : p.eval r = p.smeval r
-/
theorem leval_coe_eq_smeval {R : Type*} [Semiring R] (r : R) :
    ⇑(leval r) = fun p => p.smeval r := by
  ext
  simpa using eval_eq_smeval _ _
/-
**Polynomial.leval_eq_smeval.linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.lev
al_eq_smeval`。
形式化陈述：∀ {R : Type u_3} [inst : Semiring R] (r : R), Polynomial.leval r = Polynom
ial.smeval.linearMap R r
参数：r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leval_apply`：∀ {R : Type u_1} [inst : Semiring R] (r : R) (f 
: Polynomial R), (Polynomial.leval r) f = Polynomial.eval r f
· 使用定理 `Polynomial.smeval.linearMap_apply`：∀ (R : Type u_1) [inst : Semiring R] 
(p : Polynomial R) {S : Type u_2} [inst_1 : AddCommMonoid S] [inst_2 : Pow S ℕ] 
  [inst_3 : _root_.Modu…
· 使用定理 `Polynomial.eval_eq_smeval`：eval_eq_smeval : p.eval r = p.smeval r
-/
theorem leval_eq_smeval.linearMap {R : Type*} [Semiring R] (r : R) :
    leval r = smeval.linearMap R r := by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply, smeval.linearMap_apply, eval_eq_smeval]

end Module

section Neg

variable (R : Type*) [Ring R] {S : Type*} [AddCommGroup S] [Pow S ℕ] [Module R S] (p q : R[X])
  (x : S)

@[simp]
/-
**Polynomial.smeval_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_neg : (-p).smeval x = -p.smeval x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Polynomial.smeval_zero`：smeval_zero : (0 : R[X]).smeval x = 0
-/
theorem smeval_neg : (-p).smeval x = -p.smeval x := by
  rw [← add_eq_zero_iff_eq_neg, ← smeval_add, neg_add_cancel, smeval_zero]

@[simp]
/-
**Polynomial.smeval_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_sub : (p - q).smeval x = p.smeval x - q.smeval x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_neg`：smeval_neg : (-p).smeval x = -p.smeval x
-/
theorem smeval_sub : (p - q).smeval x = p.smeval x - q.smeval x := by
  rw [sub_eq_add_neg, smeval_add, smeval_neg, sub_eq_add_neg]
/-
**Polynomial.smeval_neg_nat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_neg_nat (S : Type*) [NonAssocRing S] [Pow S Nat] [NatPowAssoc S] (q
 : Nat[X]) (n : Nat) : q.smeval (-(n : S)) = q.smeval (-n : Int)
参数：S : Type*；q : Nat[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_eq_sum`：smeval_eq_sum : p.smeval x = p.sum (smul_pow x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_npow`：∀ (R : Type u_2) [inst : NonAssocRing R] [inst_1 : Pow R 
ℕ] [NatPowAssoc R] (n : ℤ) (m : ℕ), ↑(n ^ m) = ↑n ^ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smeval_neg_nat (S : Type*) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] (q : ℕ[X])
    (n : ℕ) : q.smeval (-(n : S)) = q.smeval (-n : ℤ) := by
  rw [smeval_eq_sum, smeval_eq_sum]
  simp only [Polynomial.smul_pow, sum_def]
  simp

end Neg

section NatPowAssoc

/-!
In the module docstring for algebras at `Mathlib/Algebra/Algebra/Basic.lean`, we see that
`[CommSemiring R] [Semiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]` is an
equivalent way to express `[CommSemiring R] [Semiring S] [Algebra R S]` that allows one to relax
the defining structures independently.  For non-associative power-associative algebras (e.g.,
octonions), we replace the `[Semiring S]` with `[NonAssocSemiring S] [Pow S ℕ] [NatPowAssoc S]`.
-/

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

/-
**Polynomial.smeval_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_C_mul : (C r * p).smeval x = r • p.smeval x
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.C_mul_monomial`：C_mul_monomial : C a * monomial n b = monomia
l n (a * b)
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem smeval_C_mul : (C r * p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, smeval_add, ph, qh, smul_add]
  | monomial n b => simp only [C_mul_monomial, smeval_monomial, mul_smul]

variable [NatPowAssoc S]
/-
**Polynomial.smeval_at_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_at_natCast (q : Nat[X]) : forall (n : Nat), q.smeval (n : S) = q.sm
eval n
参数：q : Nat[X]。
该定理/引理给出了一组等式。
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
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_npow`：Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R Nat
] [NatPowAssoc R] (n m : Nat) : (↑(n ^ m) : R) = (↑n : R) ^ m
-/
theorem smeval_at_natCast (q : ℕ[X]) : ∀ (n : ℕ), q.smeval (n : S) = q.smeval n := by
  induction q using Polynomial.induction_on' with
  | add p q ph qh =>
    intro n
    simp only [smeval_add, ph, qh, Nat.cast_add]
  | monomial n a =>
    intro n
    rw [smeval_monomial, smeval_monomial, nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Nat.cast_npow]
/-
**Polynomial.smeval_at_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_at_zero : p.smeval (0 : S) = (p.coeff 0) • (1 : S)
该定理/引理给出了一组等式。
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
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_monomial_succ`：coeff_monomial_succ : coeff (monomial (n
 + 1) a) 0 = 0
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smeval_at_zero : p.smeval (0 : S) = (p.coeff 0) • (1 : S) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp_all only [smeval_add, coeff_add, add_smul]
  | monomial n a =>
    cases n with
    | zero => simp only [monomial_zero_left, smeval_C, npow_zero, coeff_C_zero]
    | succ n => rw [coeff_monomial_succ, smeval_monomial, npow_add, npow_one, mul_zero, zero_smul,
        smul_zero]

section
variable [SMulCommClass R S S]

/-
**Polynomial.smeval_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_X_mul : (X * p).smeval x = x * p.smeval x
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monomial_one_one_eq_X`：monomial_one_one_eq_X : monomial 1 (1 
: R) = X
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, one_mul, npow_add,
      npow_one, ← mul_smul_comm, smeval_monomial]
/-
**Polynomial.smeval_X_pow_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_X_pow_assoc (m n : Nat) : x ^ m * x ^ n * p.smeval x = x ^ m * (x ^
 n * p.smeval x)
参数：m n : Nat。
该定理/引理给出了一组等式。
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
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `npow_mul_assoc`：npow_mul_assoc (k m n : Nat) (x : M) : (x ^ k * x ^ m) *
 x ^ n = x ^ k * (x ^ m * x ^ n)
-/
theorem smeval_X_pow_assoc (m n : ℕ) :
    x ^ m * x ^ n * p.smeval x = x ^ m * (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a => simp only [smeval_monomial, mul_smul_comm, npow_mul_assoc]
/-
**Polynomial.smeval_X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] (p : Polynomial R) {S : Type u_2} [in
st_1 : NonAssocSemiring S]   [inst_2 : _root_.Module R S] [inst_3 : Pow S ℕ] (x 
: S) [NatPowAssoc S] [SMulCommClass R S S] (n : ℕ),   (Polynomial.X ^ n * p).sme
val x = x ^ n * p.smeval x
参数：R : Type u_1；p : Polynomial R；x : S；n : ℕ；Polynomial.X ^ n * p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_X_pow_mul : ∀ (n : ℕ), (X ^ n * p).smeval x = x ^ n * p.smeval x
  | 0 => by
    simp [npow_zero, one_mul]
  | n + 1 => by
    rw [add_comm, npow_add, mul_assoc, npow_one, smeval_X_mul, smeval_X_pow_mul n, npow_add,
      smeval_X_pow_assoc, npow_one]
/-
**Polynomial.smeval_monomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_monomial_mul (n : Nat) : (monomial n r * p).smeval x = r • (x ^ n *
 p.smeval x)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.smeval_C_mul`：smeval_C_mul : (C r * p).smeval x = r • p.smeva
l x
· 使用定理 `Polynomial.smeval_X_pow_mul`：∀ (R : Type u_1) [inst : Semiring R] (p : P
olynomial R) {S : Type u_2} [inst_1 : NonAssocSemiring S]   [inst_2 : _root_.Mod
ule R S] [inst_3 …
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
theorem smeval_monomial_mul (n : ℕ) :
    (monomial n r * p).smeval x = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs =>
    simp only [smeval_add]
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, smeval_C_mul, smeval_X_pow_mul, smeval_add]
  | monomial n a =>
    rw [smeval_monomial, monomial_mul_monomial, smeval_monomial, npow_add, mul_smul, mul_smul_comm]

end

variable [IsScalarTower R S S]

/-
**Polynomial.smeval_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_mul_X : (p * X).smeval x = p.smeval x * x
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.monomial_mul_monomial`：monomial_mul_monomial (n m : Nat) (r s
 : R) : monomial n r * monomial m s = monomial (n + m) (r * s)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用定理 `npow_add`：npow_add (k n : Nat) (x : M) : x ^ (k + n) = x ^ k * x ^ n
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [add_mul, smeval_add, ph, qh]
  | monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one,
      npow_add, smul_mul_assoc, npow_one]
/-
**Polynomial.smeval_assoc_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_assoc_X_pow (m n : Nat) : p.smeval x * x ^ m * x ^ n = p.smeval x *
 (x ^ m * x ^ n)
参数：m n : Nat。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `npow_mul_assoc`：npow_mul_assoc (k m n : Nat) (x : M) : (x ^ k * x ^ m) *
 x ^ n = x ^ k * (x ^ m * x ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smeval_assoc_X_pow (m n : ℕ) :
    p.smeval x * x ^ m * x ^ n = p.smeval x * (x ^ m * x ^ n) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, add_mul]
  | monomial n a =>
    rw [smeval_monomial, smul_mul_assoc, smul_mul_assoc, npow_mul_assoc, ← smul_mul_assoc]
/-
**Polynomial.smeval_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] (p : Polynomial R) {S : Type u_2} [in
st_1 : NonAssocSemiring S]   [inst_2 : _root_.Module R S] [inst_3 : Pow S ℕ] (x 
: S) [NatPowAssoc S] [IsScalarTower R S S] (n : ℕ),   (p * Polynomial.X ^ n).sme
val x = p.smeval x * x ^ n
参数：R : Type u_1；p : Polynomial R；x : S；n : ℕ；p * Polynomial.X ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_mul_X_pow : ∀ (n : ℕ), (p * X ^ n).smeval x = p.smeval x * x ^ n
  | 0 => by
    simp only [npow_zero, mul_one]
  | n + 1 => by
    rw [npow_add, ← mul_assoc, npow_one, smeval_mul_X, smeval_mul_X_pow n, npow_add,
      ← smeval_assoc_X_pow, npow_one]

variable [SMulCommClass R S S]
/-
**Polynomial.smeval_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_mul : (p * q).smeval x = p.smeval x * q.smeval x
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.smeval_monomial_mul`：smeval_monomial_mul (n : Nat) : (monomia
l n r * p).smeval x = r • (x ^ n * p.smeval x)
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
theorem smeval_mul : (p * q).smeval x = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [hr, hs, smeval_add, add_mul]
  | monomial n a =>
    simp only [smeval_monomial, smeval_monomial_mul, smul_mul_assoc]
/-
**Polynomial.smeval_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] (p : Polynomial R) {S : Type u_2} [in
st_1 : NonAssocSemiring S]   [inst_2 : _root_.Module R S] [inst_3 : Pow S ℕ] (x 
: S) [NatPowAssoc S] [IsScalarTower R S S] [SMulCommClass R S S]   (n : ℕ), (p ^
 n).smeval x = p.smeval x ^ n
参数：R : Type u_1；p : Polynomial R；x : S；n : ℕ；p ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_pow : ∀ (n : ℕ), (p ^ n).smeval x = (p.smeval x) ^ n
  | 0 => by
    simp only [npow_zero, smeval_one, one_smul]
  | n + 1 => by
    rw [npow_add, smeval_mul, smeval_pow n, pow_one, npow_add, npow_one]
/-
**Polynomial.smeval_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_comp : (p.comp q).smeval x = p.smeval (q.smeval x)
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.monomial_comp`：monomial_comp (n : Nat) : (monomial n a).comp 
p = C a * p ^ n
· 使用定理 `Polynomial.smeval_C_mul`：smeval_C_mul : (C r * p).smeval x = r • p.smeva
l x
· 使用定理 `Polynomial.smeval_pow`：∀ (R : Type u_1) [inst : Semiring R] (p : Polynom
ial R) {S : Type u_2} [inst_1 : NonAssocSemiring S]   [inst_2 : _root_.Module R 
S] [inst_3 …
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
-/
theorem smeval_comp : (p.comp q).smeval x = p.smeval (q.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs, smeval_add]
  | monomial n a => simp [smeval_monomial, smeval_C_mul, smeval_pow]

end NatPowAssoc

section Commute

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [Semiring S]
  [Module R S] [IsScalarTower R S S] [SMulCommClass R S S] {x y : S}

/-
**Polynomial.smeval_commute_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_commute_left (hc : Commute x y) : Commute (p.smeval x) y
参数：hc : Commute x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Commute.add_left`：add_left [Distrib R] {a b c : R} : Commute a c -> Comm
ute b c -> Commute (a + b) c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
-/
theorem smeval_commute_left (hc : Commute x y) : Commute (p.smeval x) y := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a => simpa [smeval_monomial] using Commute.smul_left (Commute.pow_left hc _) _
/-
**Polynomial.smeval_commute** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smeval_commute (hc : Commute x y) : Commute (p.smeval x) (q.smeval y)
参数：hc : Commute x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Commute.add_left`：add_left [Distrib R] {a b c : R} : Commute a c -> Comm
ute b c -> Commute (a + b) c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_monomial`：smeval_monomial (n : Nat) : (monomial n r).s
meval x = r • x ^ n
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Polynomial.smeval_commute_left`：smeval_commute_left (hc : Commute x y) :
 Commute (p.smeval x) y
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem smeval_commute (hc : Commute x y) : Commute (p.smeval x) (q.smeval y) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a =>
    simp only [smeval_monomial]
    refine Commute.smul_left ?_ a
    induction n with
    | zero => simp only [npow_zero, Commute.one_left]
    | succ n ih =>
      refine (commute_iff_eq (x ^ (n + 1)) (q.smeval y)).mpr ?_
      rw [commute_iff_eq (x ^ n) (q.smeval y)] at ih
      have hxq : x * q.smeval y = q.smeval y * x := by
        refine (commute_iff_eq x (q.smeval y)).mp ?_
        exact Commute.symm (smeval_commute_left R q (Commute.symm hc))
      rw [pow_succ, ← mul_assoc, ← ih, mul_assoc, hxq, mul_assoc]

end Commute

section Algebra

/-
**Polynomial.aeval_eq_smeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Alg
ebra R S] (x : S) (p : R[X]) : aeval x p = p.smeval x
参数：x : S；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_def`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R
] [inst_1 : Semiring S] (f : R →+* S) (x : S) (p : Polynomial R),   Polynomial.e
val₂ f x p…
· 使用定理 `Algebra.algebraMap_eq_smul_one'`：algebraMap_eq_smul_one' : ⇑(algebraMap 
R A) = fun r => r • (1 : A)
· 使用定理 `Polynomial.smeval_def`：∀ {R : Type u_3} [inst : Semiring R] (p : Polynom
ial R) {S : Type u_4} [inst_1 : AddCommMonoid S] [inst_2 : Pow S ℕ]   [inst_3 : 
MulActionWi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) (p : R[X]) : aeval x p = p.smeval x := by
  rw [aeval_def, eval₂_def, Algebra.algebraMap_eq_smul_one', smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl
/-
**Polynomial.aeval_coe_eq_smeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_coe_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] 
[Algebra R S] (x : S) : ⇑(aeval x) = fun (p : R[X]) => p.smeval x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_eq_smeval`：aeval_eq_smeval {R : Type*} [CommSemiring R]
 {S : Type*} [Semiring S] [Algebra R S] (x : S) (p : R[X]) : aeval x p = p.smeva
l x
-/
theorem aeval_coe_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : ⇑(aeval x) = fun (p : R[X]) => p.smeval x := funext fun p => aeval_eq_smeval x p

end Algebra

end Polynomial

