/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Notation.Support

/-!
# Support of a function

In this file we prove basic properties of `Function.support f = {x | f x ≠ 0}`, and similarly for
`Function.mulSupport f = {x | f x ≠ 1}`.
-/

public section

assert_not_exists CompleteLattice MonoidWithZero

open Set

variable {α M G : Type*}

namespace Function

@[to_additive]
/--
theorem `mulSupport_mul` / 定理 `mulSupport_mul`

English:
theorem mulSupport_mul
  given: [MulOneClass M] (f g : α -> M)
  proof: mulSupport_binop_subset (· * ·) (one_mul _) f g

@[to_additive]

中文:
定理 mulSupport_mul
  条件: [MulOneClass M] (f g : α -> M)
  证明: mulSupport_binop_subset (· * ·) (one_mul _) f g

@[to_additive]

Depends on / 依赖: mulSupport_binop_subset, one_mul
-/
theorem mulSupport_mul [MulOneClass M] (f g : α -> M) :
    (mulSupport fun x => f x * g x) subseteq mulSupport f union mulSupport g :=
  mulSupport_binop_subset (· * ·) (one_mul _) f g

@[to_additive]
/--
theorem `mulSupport_pow` / 定理 `mulSupport_pow`

English:
theorem mulSupport_pow
  given: [Monoid M] (f : α -> M) (n : Nat)
  proof: by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

中文:
定理 mulSupport_pow
  条件: [Monoid M] (f : α -> M) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

Depends on / 依赖: Subset, Subset.rfl, mulSupport_mul, pow_succ, pow_zero, union_subset
-/
theorem mulSupport_pow [Monoid M] (f : α -> M) (n : Nat) :
    (mulSupport fun x => f x ^ n) subseteq mulSupport f := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

section DivisionMonoid

variable [DivisionMonoid G] (f g : α -> G)

@[to_additive (attr := simp)]
/--
theorem `mulSupport_fun_inv` / 定理 `mulSupport_fun_inv`

English:
theorem mulSupport_fun_inv
  statement: (mulSupport fun x => (f x)⁻¹) = mulSupport f
  proof: ext fun _ => inv_ne_one

@[to_additive (attr := simp)]

中文:
定理 mulSupport_fun_inv
  结论: (mulSupport fun x => (f x)⁻¹) = mulSupport f
  证明: ext fun _ => inv_ne_one

@[to_additive (attr := simp)]

Depends on / 依赖: inv_ne_one
-/
theorem mulSupport_fun_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f :=
  ext fun _ => inv_ne_one

@[to_additive (attr := simp)]
/--
theorem `mulSupport_inv` / 定理 `mulSupport_inv`

English:
theorem mulSupport_inv
  statement: mulSupport f⁻¹ = mulSupport f
  proof: mulSupport_fun_inv f

@[to_additive]

中文:
定理 mulSupport_inv
  结论: mulSupport f⁻¹ = mulSupport f
  证明: mulSupport_fun_inv f

@[to_additive]

Depends on / 依赖: mulSupport_fun_inv
-/
theorem mulSupport_inv : mulSupport f⁻¹ = mulSupport f :=
  mulSupport_fun_inv f

@[to_additive]
/--
theorem `mulSupport_mul_inv` / 定理 `mulSupport_mul_inv`

English:
theorem mulSupport_mul_inv
  statement: (mulSupport fun x => f x * (g x)⁻¹) subseteq mulSupport f union mulSupport g
  proof: mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

@[to_additive]

中文:
定理 mulSupport_mul_inv
  结论: (mulSupport fun x => f x * (g x)⁻¹) subseteq mulSupport f union mulSupport g
  证明: mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

@[to_additive]

Depends on / 依赖: mulSupport_binop_subset
-/
theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) subseteq mulSupport f union mulSupport g :=
  mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

@[to_additive]
/--
theorem `mulSupport_div` / 定理 `mulSupport_div`

English:
theorem mulSupport_div
  statement: (mulSupport fun x => f x / g x) subseteq mulSupport f union mulSupport g
  proof: mulSupport_binop_subset (· / ·) one_div_one f g

中文:
定理 mulSupport_div
  结论: (mulSupport fun x => f x / g x) subseteq mulSupport f union mulSupport g
  证明: mulSupport_binop_subset (· / ·) one_div_one f g

Depends on / 依赖: mulSupport_binop_subset, one_div_one
-/
theorem mulSupport_div : (mulSupport fun x => f x / g x) subseteq mulSupport f union mulSupport g :=
  mulSupport_binop_subset (· / ·) one_div_one f g

end DivisionMonoid

end Function
