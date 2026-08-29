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

This file defines polynomial evaluation via scalar multiplication. Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power. This
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

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S Nat]
  [MulActionWithZero R S] (x : S)

/--
Definition of `smul_pow` / `smul_pow` 的定义

English:
definition smul_pow
  signature: : Nat -> R -> S
  body: fun n r => r • x ^ n

中文:
定义 smul_pow
  签名: : 自然数 -> R -> S
  定义体: fun n r => r • x ^ n
-/
def smul_pow : Nat -> R -> S := fun n r => r • x ^ n

/-- Evaluate a polynomial `p` in the scalar semiring `R` at an element `x` in the target `S` using
scalar multiple `R`-action. -/
irreducible_def smeval : S := p.sum (smul_pow x)

/--
theorem `smeval_eq_sum` / 定理 `smeval_eq_sum`

English:
theorem smeval_eq_sum
  statement: p.smeval x = p.sum (smul_pow x)
  proof: by rw [smeval_def]

@[simp]

中文:
定理 smeval_eq_sum
  结论: p.smeval x = p.求和 (smul_pow x)
  证明: by rw [smeval_def]

@[simp]

Depends on / 依赖: smeval_def
-/
theorem smeval_eq_sum : p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

@[simp]
/--
theorem `smeval_C` / 定理 `smeval_C`

English:
theorem smeval_C
  statement: (C r).smeval x = r • x ^ 0
  proof: by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]

中文:
定理 smeval_C
  结论: (C r).smeval x = r • x ^ 0
  证明: by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]

Depends on / 依赖: smeval_eq_sum, smul_pow, sum_C_index, zero_smul
-/
theorem smeval_C : (C r).smeval x = r • x ^ 0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]
/--
theorem `smeval_monomial` / 定理 `smeval_monomial`

English:
theorem smeval_monomial
  given: (n : Nat)
  proof: by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

中文:
定理 smeval_monomial
  条件: (n : 自然数)
  证明: by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

Depends on / 依赖: smeval_eq_sum, smul_pow, sum_monomial_index, zero_smul
-/
theorem smeval_monomial (n : Nat) :
    (monomial n r).smeval x = r • x ^ n := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

/--
theorem `eval_eq_smeval` / 定理 `eval_eq_smeval`

English:
theorem eval_eq_smeval
  statement: p.eval r = p.smeval r
  proof: by
  rw [eval_eq_sum]; rw [smeval_eq_sum]
  rfl

中文:
定理 eval_eq_smeval
  结论: p.eval r = p.smeval r
  证明: by
  rw [eval_eq_sum]; rw [smeval_eq_sum]
  rfl

Depends on / 依赖: eval_eq_sum, smeval_eq_sum
-/
theorem eval_eq_smeval : p.eval r = p.smeval r := by
  rw [eval_eq_sum]; rw [smeval_eq_sum]
  rfl

/--
theorem `eval₂_smulOneHom_eq_smeval` / 定理 `eval₂_smulOneHom_eq_smeval`

English:
theorem eval₂_smulOneHom_eq_smeval
  statement: (R : Type*) [Semiring R] {S : Type*} [Semiring S] [Module R S]
  proof: by
  rw [smeval_eq_sum]; rw [eval₂_eq_sum]
  congr 1 with e a
  simp only [RingHom.smulOneHom_apply, smul_one_mul, smul_pow]

中文:
定理 eval₂_smulOneHom_eq_smeval
  结论: (R : 类型) [半环 R] {S : 类型} [半环 S] [模 R S]
  证明: by
  rw [smeval_eq_sum]; rw [eval₂_eq_sum]
  congr 1 with e a
  simp only [RingHom.smulOneHom_apply, smul_one_mul, smul_pow]

Depends on / 依赖: RingHom, RingHom.smulOneHom_apply, smeval_eq_sum, smulOneHom_apply, smul_one_mul, smul_pow
-/
theorem eval₂_smulOneHom_eq_smeval (R : Type*) [Semiring R] {S : Type*} [Semiring S] [Module R S]
    [IsScalarTower R S S] (p : R[X]) (x : S) :
    p.eval₂ RingHom.smulOneHom x = p.smeval x := by
  rw [smeval_eq_sum]; rw [eval₂_eq_sum]
  congr 1 with e a
  simp only [RingHom.smulOneHom_apply, smul_one_mul, smul_pow]

variable (R)

@[simp]
/--
theorem `smeval_zero` / 定理 `smeval_zero`

English:
theorem smeval_zero
  statement: (0 : R[X]).smeval x = 0
  proof: by
  simp only [smeval_eq_sum, sum_zero_index]

@[simp]

中文:
定理 smeval_zero
  结论: (0 : R[X]).smeval x = 0
  证明: by
  simp only [smeval_eq_sum, sum_zero_index]

@[simp]

Depends on / 依赖: smeval_eq_sum, sum_zero_index
-/
theorem smeval_zero : (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, sum_zero_index]

@[simp]
/--
theorem `smeval_one` / 定理 `smeval_one`

English:
theorem smeval_one
  statement: (1 : R[X]).smeval x = 1 • x ^ 0
  proof: by
  rw [← C_1]; rw [smeval_C]
  simp only [one_smul]

@[simp]

中文:
定理 smeval_one
  结论: (1 : R[X]).smeval x = 1 • x ^ 0
  证明: by
  rw [← C_1]; rw [smeval_C]
  simp only [one_smul]

@[simp]

Depends on / 依赖: one_smul, smeval_C
-/
theorem smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0 := by
  rw [← C_1]; rw [smeval_C]
  simp only [one_smul]

@[simp]
/--
theorem `smeval_X` / 定理 `smeval_X`

English:
theorem smeval_X
  proof: by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

@[simp]

中文:
定理 smeval_X
  证明: by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

@[simp]

Depends on / 依赖: one_smul, smeval_eq_sum, smul_pow, sum_X_index, zero_smul
-/
theorem smeval_X :
    (X : R[X]).smeval x = x ^ 1 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

@[simp]
/--
theorem `smeval_X_pow` / 定理 `smeval_X_pow`

English:
theorem smeval_X_pow
  given: {n : Nat}
  proof: by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

中文:
定理 smeval_X_pow
  条件: {n : 自然数}
  证明: by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

Depends on / 依赖: X_pow_eq_monomial, one_smul, smeval_eq_sum, smul_pow, sum_monomial_index, zero_smul
-/
theorem smeval_X_pow {n : Nat} :
    (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

end MulActionWithZero

section Module

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S Nat] [Module R S]
  (x : S)

@[simp]
/--
theorem `smeval_add` / 定理 `smeval_add`

English:
theorem smeval_add
  statement: (p + q).smeval x = p.smeval x + q.smeval x
  proof: by
  simp only [smeval_eq_sum]
  refine sum_add_index p q (smul_pow x) (fun _ => ?_) (fun _ _ _ => ?_)
  · rw [smul_pow, zero_smul]
  · rw [smul_pow, smul_pow, smul_pow, add_smul]

中文:
定理 smeval_add
  结论: (p + q).smeval x = p.smeval x + q.smeval x
  证明: by
  simp only [smeval_eq_sum]
  refine sum_add_index p q (smul_pow x) (fun _ => ?_) (fun _ _ _ => ?_)
  · rw [smul_pow, zero_smul]
  · rw [smul_pow, smul_pow, smul_pow, add_smul]

Depends on / 依赖: add_smul, smeval_eq_sum, smul_pow, sum_add_index, zero_smul
-/
theorem smeval_add : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [smeval_eq_sum]
  refine sum_add_index p q (smul_pow x) (fun _ => ?_) (fun _ _ _ => ?_)
  · rw [smul_pow, zero_smul]
  · rw [smul_pow, smul_pow, smul_pow, add_smul]

/--
theorem `smeval_natCast` / 定理 `smeval_natCast`

English:
theorem smeval_natCast
  given: (n : Nat)
  statement: (n : R[X]).smeval x = n • x ^ 0
  proof: by
  induction n with
  | zero => simp only [smeval_zero, Nat.cast_zero, zero_smul]
  | succ n ih => rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[simp]

中文:
定理 smeval_natCast
  条件: (n : 自然数)
  结论: (n : R[X]).smeval x = n • x ^ 0
  证明: by
  induction n with
  | zero => simp only [smeval_zero, Nat.cast_zero, zero_smul]
  | succ n ih => rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[simp]

Depends on / 依赖: Nat.cast_zero, add_nsmul, cast_succ, cast_zero, n.cast_succ, smeval_add, smeval_one, smeval_zero, zero_smul
-/
theorem smeval_natCast (n : Nat) : (n : R[X]).smeval x = n • x ^ 0 := by
  induction n with
  | zero => simp only [smeval_zero, Nat.cast_zero, zero_smul]
  | succ n ih => rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[simp]
/--
theorem `smeval_smul` / 定理 `smeval_smul`

English:
theorem smeval_smul
  given: (r : R)
  statement: (r • p).smeval x = r • p.smeval x
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => rw [smul_add, smeval_add, ph, qh, ← smul_add, smeval_add]
  | monomial n a => rw [smul_monomial, smeval_monomial, smeval_monomial, smul_assoc]

中文:
定理 smeval_smul
  条件: (r : R)
  结论: (r • p).smeval x = r • p.smeval x
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => rw [smul_add, smeval_add, ph, qh, ← smul_add, smeval_add]
  | monomial n a => rw [smul_monomial, smeval_monomial, smeval_monomial, smul_assoc]

Depends on / 依赖: Polynomial, Polynomial.induction_on, induction_on, monomial, smeval_add, smeval_monomial, smul_add, smul_assoc, smul_monomial
-/
theorem smeval_smul (r : R) : (r • p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => rw [smul_add, smeval_add, ph, qh, ← smul_add, smeval_add]
  | monomial n a => rw [smul_monomial, smeval_monomial, smeval_monomial, smul_assoc]

/--
Definition of `smeval.linearMap` / `smeval.linearMap` 的定义

English:
definition smeval.linearMap
  signature: : R[X] ->ₗ[R] S where
  body: f.smeval x
  map_add' f g := by simp only [smeval_add]
  map_smul' c f := by simp only [smeval_smul, RingHom.id_apply]

@[simp]

中文:
定义 smeval.linearMap
  签名: : R[X] ->ₗ[R] S where
  定义体: f.smeval x
  map_add' f g := by simp only [smeval_add]
  map_smul' c f := by simp only [smeval_smul, RingHom.id_apply]

@[simp]

Depends on / 依赖: f.smeval, smeval
-/
def smeval.linearMap : R[X] ->ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := by simp only [smeval_add]
  map_smul' c f := by simp only [smeval_smul, RingHom.id_apply]

@[simp]
/--
theorem `smeval.linearMap_apply` / 定理 `smeval.linearMap_apply`

English:
theorem smeval.linearMap_apply
  statement: smeval.linearMap R x p = p.smeval x
  proof: rfl

中文:
定理 smeval.linearMap_apply
  结论: smeval.linearMap R x p = p.smeval x
  证明: rfl
-/
theorem smeval.linearMap_apply : smeval.linearMap R x p = p.smeval x := rfl

/--
theorem `leval_coe_eq_smeval` / 定理 `leval_coe_eq_smeval`

English:
theorem leval_coe_eq_smeval
  given: {R : Type*} [Semiring R] (r : R)
  proof: by
  ext
  simpa using eval_eq_smeval _ _

中文:
定理 leval_coe_eq_smeval
  条件: {R : 类型} [半环 R] (r : R)
  证明: by
  ext
  simpa using eval_eq_smeval _ _

Depends on / 依赖: eval_eq_smeval
-/
theorem leval_coe_eq_smeval {R : Type*} [Semiring R] (r : R) :
    ⇑(leval r) = fun p => p.smeval r := by
  ext
  simpa using eval_eq_smeval _ _

/--
theorem `leval_eq_smeval.linearMap` / 定理 `leval_eq_smeval.linearMap`

English:
theorem leval_eq_smeval.linearMap
  given: {R : Type*} [Semiring R] (r : R)
  proof: by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply]; rw [smeval.linearMap_apply]; rw [eval_eq_smeval]

中文:
定理 leval_eq_smeval.linearMap
  条件: {R : 类型} [半环 R] (r : R)
  证明: by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply]; rw [smeval.linearMap_apply]; rw [eval_eq_smeval]

Depends on / 依赖: LinearMap, LinearMap.ext, eval_eq_smeval, leval_apply, linearMap_apply, smeval, smeval.linearMap_apply
-/
theorem leval_eq_smeval.linearMap {R : Type*} [Semiring R] (r : R) :
    leval r = smeval.linearMap R r := by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply]; rw [smeval.linearMap_apply]; rw [eval_eq_smeval]

end Module

section Neg

variable (R : Type*) [Ring R] {S : Type*} [AddCommGroup S] [Pow S Nat] [Module R S] (p q : R[X])
  (x : S)

@[simp]
/--
theorem `smeval_neg` / 定理 `smeval_neg`

English:
theorem smeval_neg
  statement: (-p).smeval x = -p.smeval x
  proof: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← smeval_add]; rw [neg_add_cancel]; rw [smeval_zero]

@[simp]

中文:
定理 smeval_neg
  结论: (-p).smeval x = -p.smeval x
  证明: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← smeval_add]; rw [neg_add_cancel]; rw [smeval_zero]

@[simp]

Depends on / 依赖: add_eq_zero_iff_eq_neg, neg_add_cancel, smeval_add, smeval_zero
-/
theorem smeval_neg : (-p).smeval x = -p.smeval x := by
  rw [← add_eq_zero_iff_eq_neg]; rw [← smeval_add]; rw [neg_add_cancel]; rw [smeval_zero]

@[simp]
/--
theorem `smeval_sub` / 定理 `smeval_sub`

English:
theorem smeval_sub
  statement: (p - q).smeval x = p.smeval x - q.smeval x
  proof: by
  rw [sub_eq_add_neg]; rw [smeval_add]; rw [smeval_neg]; rw [sub_eq_add_neg]

中文:
定理 smeval_sub
  结论: (p - q).smeval x = p.smeval x - q.smeval x
  证明: by
  rw [sub_eq_add_neg]; rw [smeval_add]; rw [smeval_neg]; rw [sub_eq_add_neg]

Depends on / 依赖: smeval_add, smeval_neg, sub_eq_add_neg
-/
theorem smeval_sub : (p - q).smeval x = p.smeval x - q.smeval x := by
  rw [sub_eq_add_neg]; rw [smeval_add]; rw [smeval_neg]; rw [sub_eq_add_neg]

/--
theorem `smeval_neg_nat` / 定理 `smeval_neg_nat`

English:
theorem smeval_neg_nat
  statement: (S : Type*) [NonAssocRing S] [Pow S Nat] [NatPowAssoc S] (q : Nat[X])
  proof: by
  rw [smeval_eq_sum]; rw [smeval_eq_sum]
  simp only [Polynomial.smul_pow, sum_def]
  simp

中文:
定理 smeval_neg_nat
  结论: (S : 类型) [非结合环 S] [幂 S 自然数] [自然数PowAssoc S] (q : 自然数[X])
  证明: by
  rw [smeval_eq_sum]; rw [smeval_eq_sum]
  simp only [Polynomial.smul_pow, sum_def]
  simp

Depends on / 依赖: Polynomial, Polynomial.smul_pow, smeval_eq_sum, smul_pow, sum_def
-/
theorem smeval_neg_nat (S : Type*) [NonAssocRing S] [Pow S Nat] [NatPowAssoc S] (q : Nat[X])
    (n : Nat) : q.smeval (-(n : S)) = q.smeval (-n : Int) := by
  rw [smeval_eq_sum]; rw [smeval_eq_sum]
  simp only [Polynomial.smul_pow, sum_def]
  simp

end Neg

section NatPowAssoc

/-!
In the module docstring for algebras at `Mathlib/Algebra/Algebra/Basic.lean`, we see that
`[CommSemiring R] [Semiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]` is an
equivalent way to express `[CommSemiring R] [Semiring S] [Algebra R S]` that allows one to relax
the defining structures independently. For non-associative power-associative algebras (e.g.,
octonions), we replace the `[Semiring S]` with `[NonAssocSemiring S] [Pow S ℕ] [NatPowAssoc S]`.
-/

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S Nat] (x : S)

/--
theorem `smeval_C_mul` / 定理 `smeval_C_mul`

English:
theorem smeval_C_mul
  statement: (C r * p).smeval x = r • p.smeval x
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, smeval_add, ph, qh, smul_add]
  | monomial n b => simp only [C_mul_monomial, smeval_monomial, mul_smul]

中文:
定理 smeval_C_mul
  结论: (C r * p).smeval x = r • p.smeval x
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, smeval_add, ph, qh, smul_add]
  | monomial n b => simp only [C_mul_monomial, smeval_monomial, mul_smul]

Depends on / 依赖: C_mul_monomial, Polynomial, Polynomial.induction_on, induction_on, monomial, mul_add, mul_smul, smeval_add, smeval_monomial, smul_add
-/
theorem smeval_C_mul : (C r * p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, smeval_add, ph, qh, smul_add]
  | monomial n b => simp only [C_mul_monomial, smeval_monomial, mul_smul]

variable [NatPowAssoc S]

/--
theorem `smeval_at_natCast` / 定理 `smeval_at_natCast`

English:
theorem smeval_at_natCast
  given: (q : Nat[X])
  statement: forall (n : Nat), q.smeval (n : S) = q.smeval n
  proof: by
  induction q using Polynomial.induction_on' with
  | add p q ph qh =>
    intro n
    simp only [smeval_add, ph, qh, Nat.cast_add]
  | monomial n a =>
    intro n
    rw [smeval_monomial]; rw [smeval_monomial]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [Nat.cast_mul]; rw [Nat.cast_npow]

中文:
定理 smeval_at_natCast
  条件: (q : 自然数[X])
  结论: 对任意 (n : 自然数), q.smeval (n : S) = q.smeval n
  证明: by
  induction q using Polynomial.induction_on' with
  | add p q ph qh =>
    intro n
    simp only [smeval_add, ph, qh, Nat.cast_add]
  | monomial n a =>
    intro n
    rw [smeval_monomial]; rw [smeval_monomial]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [Nat.cast_mul]; rw [Nat.cast_npow]

Depends on / 依赖: Nat.cast_add, Nat.cast_mul, Nat.cast_npow, Polynomial, Polynomial.induction_on, cast_add, cast_mul, cast_npow, induction_on, monomial, nsmul_eq_mul, smeval_add, smeval_monomial, smul_eq_mul
-/
theorem smeval_at_natCast (q : Nat[X]) : forall (n : Nat), q.smeval (n : S) = q.smeval n := by
  induction q using Polynomial.induction_on' with
  | add p q ph qh =>
    intro n
    simp only [smeval_add, ph, qh, Nat.cast_add]
  | monomial n a =>
    intro n
    rw [smeval_monomial]; rw [smeval_monomial]; rw [nsmul_eq_mul]; rw [smul_eq_mul]; rw [Nat.cast_mul]; rw [Nat.cast_npow]

/--
theorem `smeval_at_zero` / 定理 `smeval_at_zero`

English:
theorem smeval_at_zero
  statement: p.smeval (0 : S) = (p.coeff 0) • (1 : S)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp_all only [smeval_add, coeff_add, add_smul]
  | monomial n a =>
    cases n with
    | zero => simp only [monomial_zero_left, smeval_C, npow_zero, coeff_C_zero]
    | succ n => rw [coeff_monomial_succ, smeval_monomial, npo

中文:
定理 smeval_at_zero
  结论: p.smeval (0 : S) = (p.coeff 0) • (1 : S)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp_all only [smeval_add, coeff_add, add_smul]
  | monomial n a =>
    cases n with
    | zero => simp only [monomial_zero_left, smeval_C, npow_zero, coeff_C_zero]
    | succ n => rw [coeff_monomial_succ, smeval_monomial, npo

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_smul, coeff_C_zero, coeff_add, coeff_monomial_succ, induction_on, monomial, monomial_zero_left, mul_zero, npow_add, npow_one, npow_zero, smeval_C, smeval_add, smeval_monomial, smul_zero, zero_smul
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

/--
theorem `smeval_X_mul` / 定理 `smeval_X_mul`

English:
theorem smeval_X_mul
  statement: (X * p).smeval x = x * p.smeval x
  proof: by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a =>
    rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]; rw [smeval_monomial]; rw [one_mul]; rw [npow_add]; rw [npow_one]; rw [← mul_smul_comm]; rw [smeval_mon

中文:
定理 smeval_X_mul
  结论: (X * p).smeval x = x * p.smeval x
  证明: by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a =>
    rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]; rw [smeval_monomial]; rw [one_mul]; rw [npow_add]; rw [npow_one]; rw [← mul_smul_comm]; rw [smeval_mon

Depends on / 依赖: Polynomial, Polynomial.induction_on, induction_on, monomial, monomial_mul_monomial, monomial_one_one_eq_X, mul_add, mul_smul_comm, npow_add, npow_one, one_mul, smeval_add, smeval_monomial
-/
theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a =>
    rw [← monomial_one_one_eq_X]; rw [monomial_mul_monomial]; rw [smeval_monomial]; rw [one_mul]; rw [npow_add]; rw [npow_one]; rw [← mul_smul_comm]; rw [smeval_monomial]

/--
theorem `smeval_X_pow_assoc` / 定理 `smeval_X_pow_assoc`

English:
theorem smeval_X_pow_assoc
  given: (m n : Nat)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a => simp only [smeval_monomial, mul_smul_comm, npow_mul_assoc]

中文:
定理 smeval_X_pow_assoc
  条件: (m n : 自然数)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a => simp only [smeval_monomial, mul_smul_comm, npow_mul_assoc]

Depends on / 依赖: Polynomial, Polynomial.induction_on, induction_on, monomial, mul_add, mul_smul_comm, npow_mul_assoc, smeval_add, smeval_monomial
-/
theorem smeval_X_pow_assoc (m n : Nat) :
    x ^ m * x ^ n * p.smeval x = x ^ m * (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, mul_add]
  | monomial n a => simp only [smeval_monomial, mul_smul_comm, npow_mul_assoc]

/--
theorem `smeval_X_pow_mul` / 定理 `smeval_X_pow_mul`

English:
theorem smeval_X_pow_mul
  statement: forall (n : Nat), (X ^ n * p).smeval x = x ^ n * p.smeval x

中文:
定理 smeval_X_pow_mul
  结论: 对任意 (n : 自然数), (X ^ n * p).smeval x = x ^ n * p.smeval x
-/
theorem smeval_X_pow_mul : forall (n : Nat), (X ^ n * p).smeval x = x ^ n * p.smeval x
  | 0 => by
    simp [npow_zero, one_mul]
  | n + 1 => by
    rw [add_comm]; rw [npow_add]; rw [mul_assoc]; rw [npow_one]; rw [smeval_X_mul]; rw [smeval_X_pow_mul n]; rw [npow_add]; rw [smeval_X_pow_assoc]; rw [npow_one]

/--
theorem `smeval_monomial_mul` / 定理 `smeval_monomial_mul`

English:
theorem smeval_monomial_mul
  given: (n : Nat)
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs =>
    simp only [smeval_add]
    rw [← C_mul_X_pow_eq_monomial]; rw [mul_assoc]; rw [smeval_C_mul]; rw [smeval_X_pow_mul]; rw [smeval_add]
  | monomial n a =>
    rw [smeval_monomial]; rw [monomial_mul_monomial]; rw [smeval_mono

中文:
定理 smeval_monomial_mul
  条件: (n : 自然数)
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs =>
    simp only [smeval_add]
    rw [← C_mul_X_pow_eq_monomial]; rw [mul_assoc]; rw [smeval_C_mul]; rw [smeval_X_pow_mul]; rw [smeval_add]
  | monomial n a =>
    rw [smeval_monomial]; rw [monomial_mul_monomial]; rw [smeval_mono

Depends on / 依赖: C_mul_X_pow_eq_monomial, Polynomial, Polynomial.induction_on, induction_on, monomial, monomial_mul_monomial, mul_assoc, mul_smul, mul_smul_comm, npow_add, smeval_C_mul, smeval_X_pow_mul, smeval_add, smeval_monomial
-/
theorem smeval_monomial_mul (n : Nat) :
    (monomial n r * p).smeval x = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs =>
    simp only [smeval_add]
    rw [← C_mul_X_pow_eq_monomial]; rw [mul_assoc]; rw [smeval_C_mul]; rw [smeval_X_pow_mul]; rw [smeval_add]
  | monomial n a =>
    rw [smeval_monomial]; rw [monomial_mul_monomial]; rw [smeval_monomial]; rw [npow_add]; rw [mul_smul]; rw [mul_smul_comm]

end

variable [IsScalarTower R S S]

/--
theorem `smeval_mul_X` / 定理 `smeval_mul_X`

English:
theorem smeval_mul_X
  statement: (p * X).smeval x = p.smeval x * x
  proof: by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [add_mul, smeval_add, ph, qh]
  | monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one,
      npow_add, smul_mul_assoc, npow_one]

中文:
定理 smeval_mul_X
  结论: (p * X).smeval x = p.smeval x * x
  证明: by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [add_mul, smeval_add, ph, qh]
  | monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one,
      npow_add, smul_mul_assoc, npow_one]

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_mul, induction_on, monomial, monomial_mul_monomial, monomial_one_one_eq_X, mul_one, npow_add, npow_one, smeval_add, smeval_monomial, smul_mul_assoc
-/
theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [add_mul, smeval_add, ph, qh]
  | monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one,
      npow_add, smul_mul_assoc, npow_one]

/--
theorem `smeval_assoc_X_pow` / 定理 `smeval_assoc_X_pow`

English:
theorem smeval_assoc_X_pow
  given: (m n : Nat)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, add_mul]
  | monomial n a =>
    rw [smeval_monomial]; rw [smul_mul_assoc]; rw [smul_mul_assoc]; rw [npow_mul_assoc]; rw [← smul_mul_assoc]

中文:
定理 smeval_assoc_X_pow
  条件: (m n : 自然数)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, add_mul]
  | monomial n a =>
    rw [smeval_monomial]; rw [smul_mul_assoc]; rw [smul_mul_assoc]; rw [npow_mul_assoc]; rw [← smul_mul_assoc]

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_mul, induction_on, monomial, npow_mul_assoc, smeval_add, smeval_monomial, smul_mul_assoc
-/
theorem smeval_assoc_X_pow (m n : Nat) :
    p.smeval x * x ^ m * x ^ n = p.smeval x * (x ^ m * x ^ n) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [smeval_add, ph, qh, add_mul]
  | monomial n a =>
    rw [smeval_monomial]; rw [smul_mul_assoc]; rw [smul_mul_assoc]; rw [npow_mul_assoc]; rw [← smul_mul_assoc]

/--
theorem `smeval_mul_X_pow` / 定理 `smeval_mul_X_pow`

English:
theorem smeval_mul_X_pow
  statement: forall (n : Nat), (p * X ^ n).smeval x = p.smeval x * x ^ n

中文:
定理 smeval_mul_X_pow
  结论: 对任意 (n : 自然数), (p * X ^ n).smeval x = p.smeval x * x ^ n
-/
theorem smeval_mul_X_pow : forall (n : Nat), (p * X ^ n).smeval x = p.smeval x * x ^ n
  | 0 => by
    simp only [npow_zero, mul_one]
  | n + 1 => by
    rw [npow_add]; rw [← mul_assoc]; rw [npow_one]; rw [smeval_mul_X]; rw [smeval_mul_X_pow n]; rw [npow_add]; rw [← smeval_assoc_X_pow]; rw [npow_one]

variable [SMulCommClass R S S]

/--
theorem `smeval_mul` / 定理 `smeval_mul`

English:
theorem smeval_mul
  statement: (p * q).smeval x = p.smeval x * q.smeval x
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [hr, hs, smeval_add, add_mul]
  | monomial n a =>
    simp only [smeval_monomial, smeval_monomial_mul, smul_mul_assoc]

中文:
定理 smeval_mul
  结论: (p * q).smeval x = p.smeval x * q.smeval x
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [hr, hs, smeval_add, add_mul]
  | monomial n a =>
    simp only [smeval_monomial, smeval_monomial_mul, smul_mul_assoc]

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_mul, induction_on, monomial, smeval_add, smeval_monomial, smeval_monomial_mul, smul_mul_assoc
-/
theorem smeval_mul : (p * q).smeval x = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [hr, hs, smeval_add, add_mul]
  | monomial n a =>
    simp only [smeval_monomial, smeval_monomial_mul, smul_mul_assoc]

/--
theorem `smeval_pow` / 定理 `smeval_pow`

English:
theorem smeval_pow
  statement: forall (n : Nat), (p ^ n).smeval x = (p.smeval x) ^ n

中文:
定理 smeval_pow
  结论: 对任意 (n : 自然数), (p ^ n).smeval x = (p.smeval x) ^ n
-/
theorem smeval_pow : forall (n : Nat), (p ^ n).smeval x = (p.smeval x) ^ n
  | 0 => by
    simp only [npow_zero, smeval_one, one_smul]
  | n + 1 => by
    rw [npow_add]; rw [smeval_mul]; rw [smeval_pow n]; rw [pow_one]; rw [npow_add]; rw [npow_one]

/--
theorem `smeval_comp` / 定理 `smeval_comp`

English:
theorem smeval_comp
  statement: (p.comp q).smeval x = p.smeval (q.smeval x)
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs, smeval_add]
  | monomial n a => simp [smeval_monomial, smeval_C_mul, smeval_pow]

中文:
定理 smeval_comp
  结论: (p.comp q).smeval x = p.smeval (q.smeval x)
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs, smeval_add]
  | monomial n a => simp [smeval_monomial, smeval_C_mul, smeval_pow]

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_comp, induction_on, monomial, smeval_C_mul, smeval_add, smeval_monomial, smeval_pow
-/
theorem smeval_comp : (p.comp q).smeval x = p.smeval (q.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs, smeval_add]
  | monomial n a => simp [smeval_monomial, smeval_C_mul, smeval_pow]

end NatPowAssoc

section Commute

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [Semiring S]
  [Module R S] [IsScalarTower R S S] [SMulCommClass R S S] {x y : S}

/--
theorem `smeval_commute_left` / 定理 `smeval_commute_left`

English:
theorem smeval_commute_left
  given: (hc : Commute x y)
  statement: Commute (p.smeval x) y
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a => simpa [smeval_monomial] using Commute.smul_left (Commute.pow_left hc _) _

中文:
定理 smeval_commute_left
  条件: (hc : Commute x y)
  结论: Commute (p.smeval x) y
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a => simpa [smeval_monomial] using Commute.smul_left (Commute.pow_left hc _) _

Depends on / 依赖: Commute, Commute.add_left, Commute.pow_left, Commute.smul_left, Polynomial, Polynomial.induction_on, add_left, induction_on, monomial, pow_left, smeval_add, smeval_monomial, smul_left
-/
theorem smeval_commute_left (hc : Commute x y) : Commute (p.smeval x) y := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a => simpa [smeval_monomial] using Commute.smul_left (Commute.pow_left hc _) _

/--
theorem `smeval_commute` / 定理 `smeval_commute`

English:
theorem smeval_commute
  given: (hc : Commute x y)
  statement: Commute (p.smeval x) (q.smeval y)
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a =>
    simp only [smeval_monomial]
    refine Commute.smul_left ?_ a
    induction n with
    | zero => simp only [npow_zero, Commute.one_left]
    | succ n 

中文:
定理 smeval_commute
  条件: (hc : Commute x y)
  结论: Commute (p.smeval x) (q.smeval y)
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a =>
    simp only [smeval_monomial]
    refine Commute.smul_left ?_ a
    induction n with
    | zero => simp only [npow_zero, Commute.one_left]
    | succ n 

Depends on / 依赖: Commute, Commute.add_left, Commute.one_left, Commute.smul_left, Commute.symm, Polynomial, Polynomial.induction_on, add_left, commute_iff_eq, induction_on, monomial, npow_zero, one_left, q.smeval, smeval, smeval_add, smeval_monomial, smul_left
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
      rw [pow_succ]; rw [← mul_assoc]; rw [← ih]; rw [mul_assoc]; rw [hxq]; rw [mul_assoc]

end Commute

section Algebra

/--
theorem `aeval_eq_smeval` / 定理 `aeval_eq_smeval`

English:
theorem aeval_eq_smeval
  statement: {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
  proof: by
  rw [aeval_def]; rw [eval₂_def]; rw [Algebra.algebraMap_eq_smul_one']; rw [smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl

中文:
定理 aeval_eq_smeval
  结论: {R : 类型} [交换半环 R] {S : 类型} [半环 S] [代数 R S]
  证明: by
  rw [aeval_def]; rw [eval₂_def]; rw [Algebra.algebraMap_eq_smul_one']; rw [smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, aeval_def, algebraMap_eq_smul_one, one_mul, smeval_def, smul_mul_assoc
-/
theorem aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) (p : R[X]) : aeval x p = p.smeval x := by
  rw [aeval_def]; rw [eval₂_def]; rw [Algebra.algebraMap_eq_smul_one']; rw [smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl

/--
theorem `aeval_coe_eq_smeval` / 定理 `aeval_coe_eq_smeval`

English:
theorem aeval_coe_eq_smeval
  statement: {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
  proof: funext fun p => aeval_eq_smeval x p

中文:
定理 aeval_coe_eq_smeval
  结论: {R : 类型} [交换半环 R] {S : 类型} [半环 S] [代数 R S]
  证明: funext fun p => aeval_eq_smeval x p

Depends on / 依赖: aeval_eq_smeval
-/
theorem aeval_coe_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : ⇑(aeval x) = fun (p : R[X]) => p.smeval x := funext fun p => aeval_eq_smeval x p

end Algebra

end Polynomial
