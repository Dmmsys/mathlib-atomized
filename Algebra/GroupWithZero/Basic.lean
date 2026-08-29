/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Conv
public import Batteries.Tactic.SeqFocus

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `GroupWithZero` and `CommGroupWithZero`.
To reduce import dependencies, the type-classes themselves are in
`Algebra.GroupWithZero.Defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open Function

variable {M₀ G₀ : Type*}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/--
theorem `left_ne_zero_of_mul` / 定理 `left_ne_zero_of_mul`

English:
theorem left_ne_zero_of_mul
  statement: a * b != 0 -> a != 0
  proof: mt fun h => mul_eq_zero_of_left h b

中文:
定理 left_ne_zero_of_mul
  结论: a * b != 0 -> a != 0
  证明: mt fun h => mul_eq_zero_of_left h b

Depends on / 依赖: mul_eq_zero_of_left
-/
theorem left_ne_zero_of_mul : a * b != 0 -> a != 0 :=
  mt fun h => mul_eq_zero_of_left h b

/--
theorem `right_ne_zero_of_mul` / 定理 `right_ne_zero_of_mul`

English:
theorem right_ne_zero_of_mul
  statement: a * b != 0 -> b != 0
  proof: mt (mul_eq_zero_of_right a)

中文:
定理 right_ne_zero_of_mul
  结论: a * b != 0 -> b != 0
  证明: mt (mul_eq_zero_of_right a)

Depends on / 依赖: mul_eq_zero_of_right
-/
theorem right_ne_zero_of_mul : a * b != 0 -> b != 0 :=
  mt (mul_eq_zero_of_right a)

/--
theorem `ne_zero_and_ne_zero_of_mul` / 定理 `ne_zero_and_ne_zero_of_mul`

English:
theorem ne_zero_and_ne_zero_of_mul
  given: (h : a * b != 0)
  statement: a != 0 ∧ b != 0
  proof: ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

中文:
定理 ne_zero_and_ne_zero_of_mul
  条件: (h : a * b != 0)
  结论: a != 0 ∧ b != 0
  证明: ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

Depends on / 依赖: left_ne_zero_of_mul, right_ne_zero_of_mul
-/
theorem ne_zero_and_ne_zero_of_mul (h : a * b != 0) : a != 0 ∧ b != 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

/--
theorem `mul_eq_zero_of_ne_zero_imp_eq_zero` / 定理 `mul_eq_zero_of_ne_zero_imp_eq_zero`

English:
theorem mul_eq_zero_of_ne_zero_imp_eq_zero
  given: {a b : M₀} (h : a != 0 -> b = 0)
  statement: a * b = 0
  proof: by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

中文:
定理 mul_eq_zero_of_ne_zero_imp_eq_zero
  条件: {a b : M₀} (h : a != 0 -> b = 0)
  结论: a * b = 0
  证明: by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

Depends on / 依赖: Classical, Classical.propDecidable, Decidable, mul_zero, propDecidable, zero_mul
-/
theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a != 0 -> b = 0) : a * b = 0 := by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

/--
theorem `zero_mul_eq_const` / 定理 `zero_mul_eq_const`

English:
theorem zero_mul_eq_const
  statement: ((0 : M₀) * ·) = Function.const _ 0
  proof: funext zero_mul

中文:
定理 zero_mul_eq_const
  结论: ((0 : M₀) * ·) = Function.const _ 0
  证明: funext zero_mul

Depends on / 依赖: zero_mul
-/
theorem zero_mul_eq_const : ((0 : M₀) * ·) = Function.const _ 0 :=
  funext zero_mul

/--
theorem `mul_zero_eq_const` / 定理 `mul_zero_eq_const`

English:
theorem mul_zero_eq_const
  statement: (· * (0 : M₀)) = Function.const _ 0
  proof: funext mul_zero

中文:
定理 mul_zero_eq_const
  结论: (· * (0 : M₀)) = Function.const _ 0
  证明: funext mul_zero

Depends on / 依赖: mul_zero
-/
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  funext mul_zero

end MulZeroClass

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

/--
theorem `eq_zero_of_mul_self_eq_zero` / 定理 `eq_zero_of_mul_self_eq_zero`

English:
theorem eq_zero_of_mul_self_eq_zero
  given: (h : a * a = 0)
  statement: a = 0
  proof: (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

中文:
定理 eq_zero_of_mul_self_eq_zero
  条件: (h : a * a = 0)
  结论: a = 0
  证明: (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

Depends on / 依赖: eq_zero_or_eq_zero_of_mul_eq_zero
-/
theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

/--
theorem `mul_ne_zero` / 定理 `mul_ne_zero`

English:
theorem mul_ne_zero
  given: (ha : a != 0) (hb : b != 0)
  statement: a * b != 0
  proof: mt eq_zero_or_eq_zero_of_mul_eq_zero not_or.mpr ⟨ha, hb⟩

中文:
定理 mul_ne_zero
  条件: (ha : a != 0) (hb : b != 0)
  结论: a * b != 0
  证明: mt eq_zero_or_eq_zero_of_mul_eq_zero not_or.mpr ⟨ha, hb⟩

Depends on / 依赖: eq_zero_or_eq_zero_of_mul_eq_zero, not_or, not_or.mpr
-/
theorem mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0 :=
mt eq_zero_or_eq_zero_of_mul_eq_zero not_or.mpr ⟨ha, hb⟩

end Mul

namespace NeZero

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y]
  body: ⟨mul_ne_zero out out⟩

中文:
实例 mul
  签名: [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y]
  定义体: ⟨mul_ne_zero out out⟩

Depends on / 依赖: mul_ne_zero
-/
instance mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y] :
    NeZero (x * y) :=
  ⟨mul_ne_zero out out⟩

end NeZero

end

section

variable [MulZeroOneClass M₀]

/--
theorem `eq_zero_of_zero_eq_one` / 定理 `eq_zero_of_zero_eq_one`

English:
theorem eq_zero_of_zero_eq_one
  given: (h : (0 : M₀) = 1) (a : M₀)
  statement: a = 0
  proof: by
  rw [← mul_one a]; rw [← h]; rw [mul_zero]

中文:
定理 eq_zero_of_zero_eq_one
  条件: (h : (0 : M₀) = 1) (a : M₀)
  结论: a = 0
  证明: by
  rw [← mul_one a]; rw [← h]; rw [mul_zero]

Depends on / 依赖: mul_one, mul_zero
-/
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_one a]; rw [← h]; rw [mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
@[instance_reducible]
/--
Definition of `uniqueOfZeroEqOne` / `uniqueOfZeroEqOne` 的定义

English:
definition uniqueOfZeroEqOne
  signature: (h : (0 : M₀) = 1)
  body: 0
  uniq := eq_zero_of_zero_eq_one h

中文:
定义 uniqueOfZeroEqOne
  签名: (h : (0 : M₀) = 1)
  定义体: 0
  uniq := eq_zero_of_zero_eq_one h
-/
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h

/--
theorem `subsingleton_iff_zero_eq_one` / 定理 `subsingleton_iff_zero_eq_one`

English:
theorem subsingleton_iff_zero_eq_one
  statement: (0 : M₀) = 1 ↔ Subsingleton M₀
  proof: ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one

中文:
定理 subsingleton_iff_zero_eq_one
  结论: (0 : M₀) = 1 ↔ Subsingleton M₀
  证明: ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one

Depends on / 依赖: Subsingleton, Subsingleton.elim, uniqueOfZeroEqOne
-/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => haveI := uniqueOfZeroEqOne h; inferInstance, fun h => @Subsingleton.elim _ h _ _⟩

alias ⟨subsingleton_of_zero_eq_one, _⟩ := subsingleton_iff_zero_eq_one

/--
theorem `eq_of_zero_eq_one` / 定理 `eq_of_zero_eq_one`

English:
theorem eq_of_zero_eq_one
  given: (h : (0 : M₀) = 1) (a b : M₀)
  statement: a = b
  proof: @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

中文:
定理 eq_of_zero_eq_one
  条件: (h : (0 : M₀) = 1) (a b : M₀)
  结论: a = b
  证明: @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

Depends on / 依赖: Subsingleton, Subsingleton.elim, subsingleton_of_zero_eq_one
-/
theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

/--
theorem `zero_ne_one_or_forall_eq_0` / 定理 `zero_ne_one_or_forall_eq_0`

English:
theorem zero_ne_one_or_forall_eq_0
  statement: (0 : M₀) != 1 ∨ forall a : M₀, a = 0
  proof: not_or_of_imp eq_zero_of_zero_eq_one

中文:
定理 zero_ne_one_or_forall_eq_0
  结论: (0 : M₀) != 1 ∨ 对任意 a : M₀, a = 0
  证明: not_or_of_imp eq_zero_of_zero_eq_one

Depends on / 依赖: eq_zero_of_zero_eq_one, not_or_of_imp
-/
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) != 1 ∨ forall a : M₀, a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one

end

section

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

/--
theorem `left_ne_zero_of_mul_eq_one` / 定理 `left_ne_zero_of_mul_eq_one`

English:
theorem left_ne_zero_of_mul_eq_one
  given: (h : a * b = 1)
  statement: a != 0
  proof: left_ne_zero_of_mul ne_zero_of_eq_one h

中文:
定理 left_ne_zero_of_mul_eq_one
  条件: (h : a * b = 1)
  结论: a != 0
  证明: left_ne_zero_of_mul ne_zero_of_eq_one h

Depends on / 依赖: left_ne_zero_of_mul, ne_zero_of_eq_one
-/
theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a != 0 :=
left_ne_zero_of_mul ne_zero_of_eq_one h

/--
theorem `right_ne_zero_of_mul_eq_one` / 定理 `right_ne_zero_of_mul_eq_one`

English:
theorem right_ne_zero_of_mul_eq_one
  given: (h : a * b = 1)
  statement: b != 0
  proof: right_ne_zero_of_mul ne_zero_of_eq_one h

中文:
定理 right_ne_zero_of_mul_eq_one
  条件: (h : a * b = 1)
  结论: b != 0
  证明: right_ne_zero_of_mul ne_zero_of_eq_one h

Depends on / 依赖: ne_zero_of_eq_one, right_ne_zero_of_mul
-/
theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b != 0 :=
right_ne_zero_of_mul ne_zero_of_eq_one h

end

section Nilpotent

variable {R S : Type*} {x y : R}

/--
Definition of `IsNilpotent` / `IsNilpotent` 的定义

English:
definition IsNilpotent
  signature: [Zero R] [Pow R Nat] (x : R)
  body: exists n : Nat, x ^ n = 0

中文:
定义 IsNilpotent
  签名: [Zero R] [Pow R 自然数] (x : R)
  定义体: exists n : Nat, x ^ n = 0
-/
def IsNilpotent [Zero R] [Pow R Nat] (x : R) : Prop :=
  exists n : Nat, x ^ n = 0

/--
theorem `IsNilpotent.mk` / 定理 `IsNilpotent.mk`

English:
theorem IsNilpotent.mk
  given: [Zero R] [Pow R Nat] (x : R) (n : Nat) (e : x ^ n = 0)
  statement: IsNilpotent x
  proof: ⟨n, e⟩

中文:
定理 IsNilpotent.mk
  条件: [Zero R] [Pow R 自然数] (x : R) (n : 自然数) (e : x ^ n = 0)
  结论: IsNilpotent x
  证明: ⟨n, e⟩
-/
theorem IsNilpotent.mk [Zero R] [Pow R Nat] (x : R) (n : Nat) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩

/--
lemma `isNilpotent_of_subsingleton` / 引理 `isNilpotent_of_subsingleton`

English:
lemma isNilpotent_of_subsingleton
  given: [Zero R] [Pow R Nat] [Subsingleton R]
  statement: IsNilpotent x
  proof: ⟨0, Subsingleton.elim _ _⟩

中文:
引理 isNilpotent_of_subsingleton
  条件: [Zero R] [Pow R 自然数] [Subsingleton R]
  结论: IsNilpotent x
  证明: ⟨0, Subsingleton.elim _ _⟩
-/
@[simp] lemma isNilpotent_of_subsingleton [Zero R] [Pow R Nat] [Subsingleton R] : IsNilpotent x :=
  ⟨0, Subsingleton.elim _ _⟩

/--
theorem `IsNilpotent.zero` / 定理 `IsNilpotent.zero`

English:
theorem IsNilpotent.zero
  given: [MonoidWithZero R]
  statement: IsNilpotent (0 : R)
  proof: ⟨1, pow_one 0⟩

中文:
定理 IsNilpotent.zero
  条件: [MonoidWithZero R]
  结论: IsNilpotent (0 : R)
  证明: ⟨1, pow_one 0⟩
-/
@[simp] theorem IsNilpotent.zero [MonoidWithZero R] : IsNilpotent (0 : R) :=
  ⟨1, pow_one 0⟩

/--
theorem `not_isNilpotent_one` / 定理 `not_isNilpotent_one`

English:
theorem not_isNilpotent_one
  given: [MonoidWithZero R] [Nontrivial R]
  proof: fun ⟨_, H⟩ => zero_ne_one (H.symm.trans (one_pow _))

中文:
定理 not_isNilpotent_one
  条件: [MonoidWithZero R] [Nontrivial R]
  证明: fun ⟨_, H⟩ => zero_ne_one (H.symm.trans (one_pow _))

Depends on / 依赖: H.symm.trans, one_pow, zero_ne_one
-/
theorem not_isNilpotent_one [MonoidWithZero R] [Nontrivial R] :
    ¬ IsNilpotent (1 : R) := fun ⟨_, H⟩ => zero_ne_one (H.symm.trans (one_pow _))

/--
lemma `IsNilpotent.pow_succ` / 引理 `IsNilpotent.pow_succ`

English:
lemma IsNilpotent.pow_succ
  statement: (n : Nat) {S : Type*} [MonoidWithZero S] {x : S}
  proof: have ⟨N, hN⟩ := hx
  ⟨N, by rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]⟩

中文:
引理 IsNilpotent.pow_succ
  结论: (n : 自然数) {S : 类型} [MonoidWithZero S] {x : S}
  证明: have ⟨N, hN⟩ := hx
  ⟨N, by rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]⟩

Depends on / 依赖: Nat.succ_mul, mul_zero, pow_add, pow_mul, succ_mul
-/
lemma IsNilpotent.pow_succ (n : Nat) {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ) :=
  have ⟨N, hN⟩ := hx
  ⟨N, by rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]⟩

/--
theorem `IsNilpotent.of_pow` / 定理 `IsNilpotent.of_pow`

English:
theorem IsNilpotent.of_pow
  statement: [MonoidWithZero R] {x : R} {m : Nat}
  proof: have ⟨n, h⟩ := h
  ⟨m * n, by rw [← h, pow_mul x m n]⟩

中文:
定理 IsNilpotent.of_pow
  结论: [MonoidWithZero R] {x : R} {m : 自然数}
  证明: have ⟨n, h⟩ := h
  ⟨m * n, by rw [← h, pow_mul x m n]⟩

Depends on / 依赖: e.hom, e.inv, hom_inv_id, inv_hom_id, pow_mul
-/
theorem IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : Nat}
    (h : IsNilpotent (x ^ m)) : IsNilpotent x :=
  have ⟨n, h⟩ := h
  ⟨m * n, by rw [← h, pow_mul x m n]⟩

/--
lemma `IsNilpotent.pow_of_pos` / 引理 `IsNilpotent.pow_of_pos`

English:
lemma IsNilpotent.pow_of_pos
  statement: {n} {S : Type*} [MonoidWithZero S] {x : S}
  proof: by
  cases n with
  | zero => contradiction
  | succ => exact IsNilpotent.pow_succ _ hx

@[simp]

中文:
引理 IsNilpotent.pow_of_pos
  结论: {n} {S : 类型} [MonoidWithZero S] {x : S}
  证明: by
  cases n with
  | zero => contradiction
  | succ => exact IsNilpotent.pow_succ _ hx

@[simp]

Depends on / 依赖: IsNilpotent, IsNilpotent.pow_succ, pow_succ
-/
lemma IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) (hn : n != 0) : IsNilpotent (x ^ n) := by
  cases n with
  | zero => contradiction
  | succ => exact IsNilpotent.pow_succ _ hx

@[simp]
/--
lemma `IsNilpotent.pow_iff_pos` / 引理 `IsNilpotent.pow_iff_pos`

English:
lemma IsNilpotent.pow_iff_pos
  given: {n} {S : Type*} [MonoidWithZero S] {x : S} (hn : n != 0)
  proof: ⟨of_pow, (pow_of_pos · hn)⟩

中文:
引理 IsNilpotent.pow_iff_pos
  条件: {n} {S : 类型} [MonoidWithZero S] {x : S} (hn : n != 0)
  证明: ⟨of_pow, (pow_of_pos · hn)⟩

Depends on / 依赖: of_pow, pow_of_pos
-/
lemma IsNilpotent.pow_iff_pos {n} {S : Type*} [MonoidWithZero S] {x : S} (hn : n != 0) :
    IsNilpotent (x ^ n) ↔ IsNilpotent x :=
  ⟨of_pow, (pow_of_pos · hn)⟩

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
/--
Definition of `IsReduced` / `IsReduced` 的定义

English:
class IsReduced
  parameters: (R : Type*) [Zero R] [Pow R Nat]
  axioms and operations (1):
    - eq_zero : forall x : R, IsNilpotent x -> x = 0

中文:
类 IsReduced
  参数: (R : 类型) [Zero R] [Pow R 自然数]
  公理与运算 (1 个):
    - eq_zero : 对任意 x : R, IsNilpotent x -> x = 0
-/
class IsReduced (R : Type*) [Zero R] [Pow R Nat] : Prop where
  /-- A reduced structure has no nonzero nilpotent elements. -/
  eq_zero : forall x : R, IsNilpotent x -> x = 0

/--
theorem `eq_zero_of_pow_eq_zero` / 定理 `eq_zero_of_pow_eq_zero`

English:
theorem eq_zero_of_pow_eq_zero
  given: [Zero R] [Pow R Nat] [IsReduced R] {n : Nat} (h : x ^ n = 0)
  proof: IsReduced.eq_zero x ⟨n, h⟩

中文:
定理 eq_zero_of_pow_eq_zero
  条件: [Zero R] [Pow R 自然数] [IsReduced R] {n : 自然数} (h : x ^ n = 0)
  证明: IsReduced.eq_zero x ⟨n, h⟩

Depends on / 依赖: IsReduced, IsReduced.eq_zero, eq_zero
-/
theorem eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsReduced R] {n : Nat} (h : x ^ n = 0) :
    x = 0 := IsReduced.eq_zero x ⟨n, h⟩

instance (priority := 900) isReduced_of_subsingleton [Zero R] [Pow R Nat] [Subsingleton R] :
    IsReduced R :=
  ⟨fun _ _ => Subsingleton.elim ..⟩

/--
theorem `IsNilpotent.eq_zero` / 定理 `IsNilpotent.eq_zero`

English:
theorem IsNilpotent.eq_zero
  given: [Zero R] [Pow R Nat] [IsReduced R] (h : IsNilpotent x)
  statement: x = 0
  proof: IsReduced.eq_zero x h

@[simp]

中文:
定理 IsNilpotent.eq_zero
  条件: [Zero R] [Pow R 自然数] [IsReduced R] (h : IsNilpotent x)
  结论: x = 0
  证明: IsReduced.eq_zero x h

@[simp]

Depends on / 依赖: IsReduced, IsReduced.eq_zero, eq_zero
-/
theorem IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h

@[simp]
/--
theorem `isNilpotent_iff_eq_zero` / 定理 `isNilpotent_iff_eq_zero`

English:
theorem isNilpotent_iff_eq_zero
  given: [MonoidWithZero R] [IsReduced R]
  statement: IsNilpotent x ↔ x = 0
  proof: ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩

中文:
定理 isNilpotent_iff_eq_zero
  条件: [MonoidWithZero R] [IsReduced R]
  结论: IsNilpotent x ↔ x = 0
  证明: ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩

Depends on / 依赖: IsNilpotent, IsNilpotent.zero, eq_zero, h.eq_zero, h.symm
-/
theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩

/--
lemma `exists_isNilpotent_of_not_isReduced` / 引理 `exists_isNilpotent_of_not_isReduced`

English:
lemma exists_isNilpotent_of_not_isReduced
  given: {R : Type*} [Zero R] [Pow R Nat] (h : ¬IsReduced R)
  proof: by
  simpa [isReduced_iff, not_forall, and_comm] using h

中文:
引理 exists_isNilpotent_of_not_isReduced
  条件: {R : 类型} [Zero R] [Pow R 自然数] (h : ¬IsReduced R)
  证明: by
  simpa [isReduced_iff, not_forall, and_comm] using h

Depends on / 依赖: and_comm, isReduced_iff, not_forall
-/
lemma exists_isNilpotent_of_not_isReduced {R : Type*} [Zero R] [Pow R Nat] (h : ¬IsReduced R) :
    exists x : R, x != 0 ∧ IsNilpotent x := by
  simpa [isReduced_iff, not_forall, and_comm] using h

end Nilpotent

section MonoidWithZero
variable [MonoidWithZero M₀] {a : M₀} {n : Nat}

/--
lemma `zero_pow` / 引理 `zero_pow`

English:
lemma zero_pow
  statement: forall {n : Nat}, n != 0 -> (0 : M₀) ^ n = 0

中文:
引理 zero_pow
  结论: 对任意 {n : 自然数}, n != 0 -> (0 : M₀) ^ n = 0
-/
@[simp] lemma zero_pow : forall {n : Nat}, n != 0 -> (0 : M₀) ^ n = 0
  | n + 1, _ => by rw [pow_succ, mul_zero]

/--
lemma `zero_pow_eq` / 引理 `zero_pow_eq`

English:
lemma zero_pow_eq
  given: (n : Nat)
  statement: (0 : M₀) ^ n = if n = 0 then 1 else 0
  proof: by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]

中文:
引理 zero_pow_eq
  条件: (n : 自然数)
  结论: (0 : M₀) ^ n = if n = 0 then 1 else 0
  证明: by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]

Depends on / 依赖: pow_zero, split_ifs, zero_pow
-/
lemma zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]

/--
lemma `zero_pow_eq_one₀` / 引理 `zero_pow_eq_one₀`

English:
lemma zero_pow_eq_one₀
  given: [Nontrivial M₀]
  statement: (0 : M₀) ^ n = 1 ↔ n = 0
  proof: by
  rw [zero_pow_eq]; rw [one_ne_zero.ite_eq_left_iff]

中文:
引理 zero_pow_eq_one₀
  条件: [Nontrivial M₀]
  结论: (0 : M₀) ^ n = 1 ↔ n = 0
  证明: by
  rw [zero_pow_eq]; rw [one_ne_zero.ite_eq_left_iff]

Depends on / 依赖: ite_eq_left_iff, one_ne_zero, one_ne_zero.ite_eq_left_iff, zero_pow_eq
-/
lemma zero_pow_eq_one₀ [Nontrivial M₀] : (0 : M₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_pow_eq]; rw [one_ne_zero.ite_eq_left_iff]

/--
lemma `pow_eq_zero_of_le` / 引理 `pow_eq_zero_of_le`

English:
lemma pow_eq_zero_of_le
  statement: forall {m n}, m <= n -> a ^ m = 0 -> a ^ n = 0

中文:
引理 pow_eq_zero_of_le
  结论: 对任意 {m n}, m <= n -> a ^ m = 0 -> a ^ n = 0
-/
lemma pow_eq_zero_of_le : forall {m n}, m <= n -> a ^ m = 0 -> a ^ n = 0
  | _, _, Nat.le.refl, ha => ha
  | _, _, Nat.le.step hmn, ha => by rw [pow_succ, pow_eq_zero_of_le hmn ha, zero_mul]

/--
lemma `ne_zero_pow` / 引理 `ne_zero_pow`

English:
lemma ne_zero_pow
  given: (hn : n != 0) (ha : a ^ n != 0)
  statement: a != 0
  proof: by rintro rfl; exact ha zero_pow hn

@[simp]

中文:
引理 ne_zero_pow
  条件: (hn : n != 0) (ha : a ^ n != 0)
  结论: a != 0
  证明: by rintro rfl; exact ha zero_pow hn

@[simp]

Depends on / 依赖: zero_pow
-/
lemma ne_zero_pow (hn : n != 0) (ha : a ^ n != 0) : a != 0 := by rintro rfl; exact ha zero_pow hn

@[simp]
/--
lemma `zero_pow_eq_zero` / 引理 `zero_pow_eq_zero`

English:
lemma zero_pow_eq_zero
  given: [Nontrivial M₀]
  statement: (0 : M₀) ^ n = 0 ↔ n != 0
  proof: ⟨by rintro h rfl; simp at h, zero_pow⟩

中文:
引理 zero_pow_eq_zero
  条件: [Nontrivial M₀]
  结论: (0 : M₀) ^ n = 0 ↔ n != 0
  证明: ⟨by rintro h rfl; simp at h, zero_pow⟩

Depends on / 依赖: zero_pow
-/
lemma zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n != 0 :=
  ⟨by rintro h rfl; simp at h, zero_pow⟩

/--
lemma `pow_mul_eq_zero_of_le` / 引理 `pow_mul_eq_zero_of_le`

English:
lemma pow_mul_eq_zero_of_le
  statement: {a b : M₀} {m n : Nat} (hmn : m <= n)
  proof: by
  rw [show n = n - m + m by lia]; rw [pow_add]; rw [mul_assoc]; rw [h]
  simp

中文:
引理 pow_mul_eq_zero_of_le
  结论: {a b : M₀} {m n : 自然数} (hmn : m <= n)
  证明: by
  rw [show n = n - m + m by lia]; rw [pow_add]; rw [mul_assoc]; rw [h]
  simp

Depends on / 依赖: mul_assoc, pow_add
-/
lemma pow_mul_eq_zero_of_le {a b : M₀} {m n : Nat} (hmn : m <= n)
    (h : a ^ m * b = 0) : a ^ n * b = 0 := by
  rw [show n = n - m + m by lia]; rw [pow_add]; rw [mul_assoc]; rw [h]
  simp

instance (priority := 900) isReduced_of_noZeroDivisors [NoZeroDivisors M₀] :
    IsReduced M₀ :=
  ⟨fun a ⟨n, ha⟩ => by
    induction n with
    | zero => simpa using congr_arg (a * ·) ha
    | succ n ih => rw [pow_succ, mul_eq_zero] at ha; exact ha.elim ih id⟩

variable [IsReduced M₀]

/--
lemma `pow_eq_zero_iff` / 引理 `pow_eq_zero_iff`

English:
lemma pow_eq_zero_iff
  given: (hn : n != 0)
  statement: a ^ n = 0 ↔ a = 0
  proof: ⟨eq_zero_of_pow_eq_zero, (·.symm ▸ zero_pow hn)⟩

中文:
引理 pow_eq_zero_iff
  条件: (hn : n != 0)
  结论: a ^ n = 0 ↔ a = 0
  证明: ⟨eq_zero_of_pow_eq_zero, (·.symm ▸ zero_pow hn)⟩
-/
@[simp] lemma pow_eq_zero_iff (hn : n != 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨eq_zero_of_pow_eq_zero, (·.symm ▸ zero_pow hn)⟩

/--
lemma `pow_ne_zero_iff` / 引理 `pow_ne_zero_iff`

English:
lemma pow_ne_zero_iff
  given: (hn : n != 0)
  statement: a ^ n != 0 ↔ a != 0
  proof: (pow_eq_zero_iff hn).not

中文:
引理 pow_ne_zero_iff
  条件: (hn : n != 0)
  结论: a ^ n != 0 ↔ a != 0
  证明: (pow_eq_zero_iff hn).not

Depends on / 依赖: pow_eq_zero_iff
-/
lemma pow_ne_zero_iff (hn : n != 0) : a ^ n != 0 ↔ a != 0 := (pow_eq_zero_iff hn).not

/--
lemma `pow_ne_zero` / 引理 `pow_ne_zero`

English:
lemma pow_ne_zero
  given: (n : Nat) (h : a != 0)
  statement: a ^ n != 0
  proof: mt eq_zero_of_pow_eq_zero h

中文:
引理 pow_ne_zero
  条件: (n : 自然数) (h : a != 0)
  结论: a ^ n != 0
  证明: mt eq_zero_of_pow_eq_zero h

Depends on / 依赖: eq_zero_of_pow_eq_zero
-/
lemma pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0 := mt eq_zero_of_pow_eq_zero h

/--
Instance `NeZero.pow` / 实例 `NeZero.pow`

English:
instance NeZero.pow
  signature: [NeZero a]
  body: ⟨pow_ne_zero n NeZero.out⟩

中文:
实例 NeZero.pow
  签名: [NeZero a]
  定义体: ⟨pow_ne_zero n NeZero.out⟩

Depends on / 依赖: NeZero, NeZero.out, pow_ne_zero
-/
instance NeZero.pow [NeZero a] : NeZero (a ^ n) := ⟨pow_ne_zero n NeZero.out⟩

/--
lemma `sq_eq_zero_iff` / 引理 `sq_eq_zero_iff`

English:
lemma sq_eq_zero_iff
  statement: a ^ 2 = 0 ↔ a = 0
  proof: pow_eq_zero_iff two_ne_zero

中文:
引理 sq_eq_zero_iff
  结论: a ^ 2 = 0 ↔ a = 0
  证明: pow_eq_zero_iff two_ne_zero

Depends on / 依赖: pow_eq_zero_iff, two_ne_zero
-/
lemma sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0 := pow_eq_zero_iff two_ne_zero

/--
lemma `pow_eq_zero_iff'` / 引理 `pow_eq_zero_iff'`

English:
lemma pow_eq_zero_iff'
  given: [Nontrivial M₀]
  statement: a ^ n = 0 ↔ a = 0 ∧ n != 0
  proof: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero := eq_zero_of_pow_eq_zero
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero_iff := pow_eq_zero_iff
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_ne_zero_if

中文:
引理 pow_eq_zero_iff'
  条件: [Nontrivial M₀]
  结论: a ^ n = 0 ↔ a = 0 ∧ n != 0
  证明: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero := eq_zero_of_pow_eq_zero
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero_iff := pow_eq_zero_iff
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_ne_zero_if
-/
@[simp] lemma pow_eq_zero_iff' [Nontrivial M₀] : a ^ n = 0 ↔ a = 0 ∧ n != 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero := eq_zero_of_pow_eq_zero
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero_iff := pow_eq_zero_iff
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_ne_zero_iff := pow_ne_zero_iff
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_ne_zero := pow_ne_zero
@[deprecated (since := "2026-01-08")] alias IsReduced.pow_eq_zero_iff' := pow_eq_zero_iff'

/--
theorem `exists_right_inv_of_exists_left_inv` / 定理 `exists_right_inv_of_exists_left_inv`

English:
theorem exists_right_inv_of_exists_left_inv
  statement: {α} [MonoidWithZero α]
  proof: by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact ⟨a, Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := h a ha
  obtain ⟨c, hc⟩ := h b (left_ne_zero_of_mul <| hb.trans_ne one_ne_zero)
  refine ⟨b, ?_⟩
  conv_lhs => rw [← one_mul (a * b), ← hc, mul_assoc, ← mul_assoc b, hb, one_mul, hc]

中文:
定理 exists_right_inv_of_exists_left_inv
  结论: {α} [MonoidWithZero α]
  证明: by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact ⟨a, Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := h a ha
  obtain ⟨c, hc⟩ := h b (left_ne_zero_of_mul <| hb.trans_ne one_ne_zero)
  refine ⟨b, ?_⟩
  conv_lhs => rw [← one_mul (a * b), ← hc, mul_assoc, ← mul_assoc b, hb, one_mul, hc]

Depends on / 依赖: Subsingleton, Subsingleton.elim, conv_lhs, hb.trans_ne, left_ne_zero_of_mul, mul_assoc, one_mul, one_ne_zero, subsingleton_or_nontrivial, trans_ne
-/
theorem exists_right_inv_of_exists_left_inv {α} [MonoidWithZero α]
    (h : forall a : α, a != 0 -> exists b : α, b * a = 1) {a : α} (ha : a != 0) : exists b : α, a * b = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial α
  · exact ⟨a, Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := h a ha
  obtain ⟨c, hc⟩ := h b (left_ne_zero_of_mul <| hb.trans_ne one_ne_zero)
  refine ⟨b, ?_⟩
  conv_lhs => rw [← one_mul (a * b), ← hc, mul_assoc, ← mul_assoc b, hb, one_mul, hc]

end MonoidWithZero

section CancelMonoidWithZero

variable {a b c : M₀}
variable [MulZeroOneClass M₀]

/--
theorem `mul_right_eq_self₀` / 定理 `mul_right_eq_self₀`

English:
theorem mul_right_eq_self₀
  given: [IsLeftCancelMulZero M₀]
  statement: a * b = a ↔ b = 1 ∨ a = 0
  proof: calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

中文:
定理 mul_right_eq_self₀
  条件: [IsLeftCancelMulZero M₀]
  结论: a * b = a ↔ b = 1 ∨ a = 0
  证明: calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

Depends on / 依赖: cokerToKer, mul_eq_mul_left_iff, mul_one
-/
theorem mul_right_eq_self₀ [IsLeftCancelMulZero M₀] : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

/--
theorem `mul_left_eq_self₀` / 定理 `mul_left_eq_self₀`

English:
theorem mul_left_eq_self₀
  given: [IsRightCancelMulZero M₀]
  statement: a * b = b ↔ a = 1 ∨ b = 0
  proof: calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff

@[simp]

中文:
定理 mul_left_eq_self₀
  条件: [IsRightCancelMulZero M₀]
  结论: a * b = b ↔ a = 1 ∨ b = 0
  证明: calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff

@[simp]

Depends on / 依赖: mul_eq_mul_right_iff, one_mul
-/
theorem mul_left_eq_self₀ [IsRightCancelMulZero M₀] : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff

@[simp]
/--
theorem `mul_eq_left₀` / 定理 `mul_eq_left₀`

English:
theorem mul_eq_left₀
  given: [IsLeftCancelMulZero M₀] (ha : a != 0)
  statement: a * b = a ↔ b = 1
  proof: by
  rw [Iff.comm]; rw [← mul_right_inj' ha]; rw [mul_one]

@[simp]

中文:
定理 mul_eq_left₀
  条件: [IsLeftCancelMulZero M₀] (ha : a != 0)
  结论: a * b = a ↔ b = 1
  证明: by
  rw [Iff.comm]; rw [← mul_right_inj' ha]; rw [mul_one]

@[simp]

Depends on / 依赖: Iff.comm, mul_one, mul_right_inj
-/
theorem mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a != 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm]; rw [← mul_right_inj' ha]; rw [mul_one]

@[simp]
/--
theorem `mul_eq_right₀` / 定理 `mul_eq_right₀`

English:
theorem mul_eq_right₀
  given: [IsRightCancelMulZero M₀] (hb : b != 0)
  statement: a * b = b ↔ a = 1
  proof: by
  rw [Iff.comm]; rw [← mul_left_inj' hb]; rw [one_mul]

@[simp]

中文:
定理 mul_eq_right₀
  条件: [IsRightCancelMulZero M₀] (hb : b != 0)
  结论: a * b = b ↔ a = 1
  证明: by
  rw [Iff.comm]; rw [← mul_left_inj' hb]; rw [one_mul]

@[simp]

Depends on / 依赖: Iff.comm, mul_left_inj, one_mul
-/
theorem mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b != 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm]; rw [← mul_left_inj' hb]; rw [one_mul]

@[simp]
/--
theorem `left_eq_mul₀` / 定理 `left_eq_mul₀`

English:
theorem left_eq_mul₀
  given: [IsLeftCancelMulZero M₀] (ha : a != 0)
  statement: a = a * b ↔ b = 1
  proof: by
  rw [eq_comm]; rw [mul_eq_left₀ ha]

@[simp]

中文:
定理 left_eq_mul₀
  条件: [IsLeftCancelMulZero M₀] (ha : a != 0)
  结论: a = a * b ↔ b = 1
  证明: by
  rw [eq_comm]; rw [mul_eq_left₀ ha]

@[simp]

Depends on / 依赖: eq_comm
-/
theorem left_eq_mul₀ [IsLeftCancelMulZero M₀] (ha : a != 0) : a = a * b ↔ b = 1 := by
  rw [eq_comm]; rw [mul_eq_left₀ ha]

@[simp]
/--
theorem `right_eq_mul₀` / 定理 `right_eq_mul₀`

English:
theorem right_eq_mul₀
  given: [IsRightCancelMulZero M₀] (hb : b != 0)
  statement: b = a * b ↔ a = 1
  proof: by
  rw [eq_comm]; rw [mul_eq_right₀ hb]

中文:
定理 right_eq_mul₀
  条件: [IsRightCancelMulZero M₀] (hb : b != 0)
  结论: b = a * b ↔ a = 1
  证明: by
  rw [eq_comm]; rw [mul_eq_right₀ hb]

Depends on / 依赖: eq_comm
-/
theorem right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b != 0) : b = a * b ↔ a = 1 := by
  rw [eq_comm]; rw [mul_eq_right₀ hb]

/--
theorem `eq_zero_of_mul_eq_self_right` / 定理 `eq_zero_of_mul_eq_self_right`

English:
theorem eq_zero_of_mul_eq_self_right
  given: [IsLeftCancelMulZero M₀] (h₁ : b != 1) (h₂ : a * b = a)
  proof: Classical.byContradiction fun ha => h₁ mul_left_cancel₀ ha h₂.symm ▸ (mul_one a).symm

中文:
定理 eq_zero_of_mul_eq_self_right
  条件: [IsLeftCancelMulZero M₀] (h₁ : b != 1) (h₂ : a * b = a)
  证明: Classical.byContradiction fun ha => h₁ mul_left_cancel₀ ha h₂.symm ▸ (mul_one a).symm

Depends on / 依赖: Classical, Classical.byContradiction, byContradiction, mul_one
-/
theorem eq_zero_of_mul_eq_self_right [IsLeftCancelMulZero M₀] (h₁ : b != 1) (h₂ : a * b = a) :
    a = 0 :=
Classical.byContradiction fun ha => h₁ mul_left_cancel₀ ha h₂.symm ▸ (mul_one a).symm

/--
theorem `eq_zero_of_mul_eq_self_left` / 定理 `eq_zero_of_mul_eq_self_left`

English:
theorem eq_zero_of_mul_eq_self_left
  given: [IsRightCancelMulZero M₀] (h₁ : b != 1) (h₂ : b * a = a)
  proof: Classical.byContradiction fun ha => h₁ mul_right_cancel₀ ha h₂.symm ▸ (one_mul a).symm

中文:
定理 eq_zero_of_mul_eq_self_left
  条件: [IsRightCancelMulZero M₀] (h₁ : b != 1) (h₂ : b * a = a)
  证明: Classical.byContradiction fun ha => h₁ mul_right_cancel₀ ha h₂.symm ▸ (one_mul a).symm

Depends on / 依赖: Classical, Classical.byContradiction, byContradiction, one_mul
-/
theorem eq_zero_of_mul_eq_self_left [IsRightCancelMulZero M₀] (h₁ : b != 1) (h₂ : b * a = a) :
    a = 0 :=
Classical.byContradiction fun ha => h₁ mul_right_cancel₀ ha h₂.symm ▸ (one_mul a).symm

variable {M₀ : Type*} [MonoidWithZero M₀]

instance (priority := 100) [IsLeftCancelMulZero M₀] : IsDedekindFiniteMonoid M₀ where
  mul_eq_one_symm h := by
    cases subsingleton_or_nontrivial M₀
    · exact Subsingleton.elim _ _
    exact (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (left_ne_zero_of_mul_eq_one h)).mul_eq_one_symm h

instance (priority := 100) [IsRightCancelMulZero M₀] : IsDedekindFiniteMonoid M₀ where
  mul_eq_one_symm h := by
    cases subsingleton_or_nontrivial M₀
    · exact Subsingleton.elim _ _
    exact (IsRightCancelMulZero.mul_right_cancel_of_ne_zero
      (right_ne_zero_of_mul_eq_one h)).mul_eq_one_symm h

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b x : G₀}

/--
theorem `GroupWithZero.mul_right_injective` / 定理 `GroupWithZero.mul_right_injective`

English:
theorem GroupWithZero.mul_right_injective
  given: (h : x != 0)
  proof: fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

中文:
定理 GroupWithZero.mul_right_injective
  条件: (h : x != 0)
  证明: fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

Depends on / 依赖: congr_arg, mul_assoc, one_mul
-/
theorem GroupWithZero.mul_right_injective (h : x != 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

/--
theorem `GroupWithZero.mul_left_injective` / 定理 `GroupWithZero.mul_left_injective`

English:
theorem GroupWithZero.mul_left_injective
  given: (h : x != 0)
  proof: fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel₀ h, mul_one] using congr_arg (fun y => y * x⁻¹) w

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`

中文:
定理 GroupWithZero.mul_left_injective
  条件: (h : x != 0)
  证明: fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel₀ h, mul_one] using congr_arg (fun y => y * x⁻¹) w

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`

Depends on / 依赖: congr_arg, mul_assoc, mul_one
-/
theorem GroupWithZero.mul_left_injective (h : x != 0) :
    Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel₀ h, mul_one] using congr_arg (fun y => y * x⁻¹) w

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`
/--
theorem `inv_mul_cancel_right₀` / 定理 `inv_mul_cancel_right₀`

English:
theorem inv_mul_cancel_right₀
  given: (h : b != 0) (a : G₀)
  statement: a * b⁻¹ * b = a
  proof: calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]


@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`

中文:
定理 inv_mul_cancel_right₀
  条件: (h : b != 0) (a : G₀)
  结论: a * b⁻¹ * b = a
  证明: calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]


@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`

Depends on / 依赖: cokerIsoKer, hS.cokerIsoKer, hom_inv_id, mul_assoc
-/
theorem inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]


@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`
/--
theorem `inv_mul_cancel_left₀` / 定理 `inv_mul_cancel_left₀`

English:
theorem inv_mul_cancel_left₀
  given: (h : a != 0) (b : G₀)
  statement: a⁻¹ * (a * b) = b
  proof: calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

中文:
定理 inv_mul_cancel_left₀
  条件: (h : a != 0) (b : G₀)
  结论: a⁻¹ * (a * b) = b
  证明: calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

Depends on / 依赖: cokerIsoKer, hS.cokerIsoKer, inv_hom_id, mul_assoc
-/
theorem inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]


/--
theorem `inv_eq_of_mul` / 定理 `inv_eq_of_mul`

English:
theorem inv_eq_of_mul
  given: (h : a * b = 1)
  statement: a⁻¹ = b
  proof: by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b]; rw [h]; rw [mul_one]

中文:
定理 inv_eq_of_mul
  条件: (h : a * b = 1)
  结论: a⁻¹ = b
  证明: by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b]; rw [h]; rw [mul_one]
-/
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b]; rw [h]; rw [mul_one]

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ where
  inv_inv a := by
    by_cases h : a = 0
    · simp [h]
    · exact left_inv_eq_right_inv (inv_mul_cancel₀ <| inv_ne_zero h) (inv_mul_cancel₀ h)
  mul_inv_rev a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    apply inv_eq_of_mul
    simp [mul_assoc, ha, hb]
  inv_eq_of_mul _ _ := by exact inv_eq_of_mul

-- see Note [lower instance priority]
instance (priority := 10) : IsCancelMulZero G₀ where
  mul_left_cancel_of_ne_zero {x} hx y z h := by
    dsimp only at h; rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z]
  mul_right_cancel_of_ne_zero {x} hx y z h := by
    dsimp only at h; rw [← mul_inv_cancel_right₀ hx y, h, mul_inv_cancel_right₀ hx z]

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a : G₀}

@[simp]
/--
theorem `zero_div` / 定理 `zero_div`

English:
theorem zero_div
  given: (a : G₀)
  statement: 0 / a = 0
  proof: by rw [div_eq_mul_inv, zero_mul]

@[simp]

中文:
定理 zero_div
  条件: (a : G₀)
  结论: 0 / a = 0
  证明: by rw [div_eq_mul_inv, zero_mul]

@[simp]

Depends on / 依赖: div_eq_mul_inv, zero_mul
-/
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: (a : G₀)
  statement: a / 0 = 0
  proof: by rw [div_eq_mul_inv, inv_zero, mul_zero]

中文:
定理 div_zero
  条件: (a : G₀)
  结论: a / 0 = 0
  证明: by rw [div_eq_mul_inv, inv_zero, mul_zero]

Depends on / 依赖: div_eq_mul_inv, inv_zero, mul_zero
-/
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
/--
theorem `mul_self_mul_inv` / 定理 `mul_self_mul_inv`

English:
theorem mul_self_mul_inv
  given: (a : G₀)
  statement: a * a * a⁻¹ = a
  proof: by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]

中文:
定理 mul_self_mul_inv
  条件: (a : G₀)
  结论: a * a * a⁻¹ = a
  证明: by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]

Depends on / 依赖: inv_zero, mul_assoc, mul_one, mul_zero
-/
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]


/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
/--
theorem `mul_inv_mul_cancel` / 定理 `mul_inv_mul_cancel`

English:
theorem mul_inv_mul_cancel
  given: (a : G₀)
  statement: a * a⁻¹ * a = a
  proof: by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel₀ h, one_mul]

中文:
定理 mul_inv_mul_cancel
  条件: (a : G₀)
  结论: a * a⁻¹ * a = a
  证明: by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel₀ h, one_mul]

Depends on / 依赖: inv_zero, mul_zero, one_mul
-/
theorem mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel₀ h, one_mul]


/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
/--
theorem `inv_mul_mul_self` / 定理 `inv_mul_mul_self`

English:
theorem inv_mul_mul_self
  given: (a : G₀)
  statement: a⁻¹ * a * a = a
  proof: by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel₀ h, one_mul]

中文:
定理 inv_mul_mul_self
  条件: (a : G₀)
  结论: a⁻¹ * a * a = a
  证明: by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel₀ h, one_mul]

Depends on / 依赖: inv_zero, mul_zero, one_mul
-/
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel₀ h, one_mul]


/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
/--
theorem `mul_self_div_self` / 定理 `mul_self_div_self`

English:
theorem mul_self_div_self
  given: (a : G₀)
  statement: a * a / a = a
  proof: by rw [div_eq_mul_inv, mul_self_mul_inv a]

中文:
定理 mul_self_div_self
  条件: (a : G₀)
  结论: a * a / a = a
  证明: by rw [div_eq_mul_inv, mul_self_mul_inv a]

Depends on / 依赖: div_eq_mul_inv, mul_self_mul_inv
-/
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
/--
theorem `div_self_mul_self` / 定理 `div_self_mul_self`

English:
theorem div_self_mul_self
  given: (a : G₀)
  statement: a / a * a = a
  proof: by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

中文:
定理 div_self_mul_self
  条件: (a : G₀)
  结论: a / a * a = a
  证明: by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

Depends on / 依赖: div_eq_mul_inv, mul_inv_mul_cancel
-/
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp]
/--
theorem `div_self_mul_self'` / 定理 `div_self_mul_self'`

English:
theorem div_self_mul_self'
  given: (a : G₀)
  statement: a / (a * a) = a⁻¹
  proof: calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _

中文:
定理 div_self_mul_self'
  条件: (a : G₀)
  结论: a / (a * a) = a⁻¹
  证明: calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _

Depends on / 依赖: inv_mul_mul_self, mul_inv_rev
-/
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _


/--
theorem `one_div_ne_zero` / 定理 `one_div_ne_zero`

English:
theorem one_div_ne_zero
  given: {a : G₀} (h : a != 0)
  statement: 1 / a != 0
  proof: by
  simpa only [one_div] using inv_ne_zero h

@[simp]

中文:
定理 one_div_ne_zero
  条件: {a : G₀} (h : a != 0)
  结论: 1 / a != 0
  证明: by
  simpa only [one_div] using inv_ne_zero h

@[simp]

Depends on / 依赖: inv_ne_zero, one_div
-/
theorem one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0 := by
  simpa only [one_div] using inv_ne_zero h

@[simp]
/--
theorem `inv_eq_zero` / 定理 `inv_eq_zero`

English:
theorem inv_eq_zero
  given: {a : G₀}
  statement: a⁻¹ = 0 ↔ a = 0
  proof: by rw [inv_eq_iff_eq_inv, inv_zero]

@[simp]

中文:
定理 inv_eq_zero
  条件: {a : G₀}
  结论: a⁻¹ = 0 ↔ a = 0
  证明: by rw [inv_eq_iff_eq_inv, inv_zero]

@[simp]

Depends on / 依赖: inv_eq_iff_eq_inv, inv_zero
-/
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_eq_inv, inv_zero]

@[simp]
/--
theorem `zero_eq_inv` / 定理 `zero_eq_inv`

English:
theorem zero_eq_inv
  given: {a : G₀}
  statement: 0 = a⁻¹ ↔ 0 = a
  proof: eq_comm.trans inv_eq_zero.trans eq_comm

中文:
定理 zero_eq_inv
  条件: {a : G₀}
  结论: 0 = a⁻¹ ↔ 0 = a
  证明: eq_comm.trans inv_eq_zero.trans eq_comm

Depends on / 依赖: eq_comm, eq_comm.trans, inv_eq_zero, inv_eq_zero.trans
-/
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
eq_comm.trans inv_eq_zero.trans eq_comm

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
/--
theorem `div_div_self` / 定理 `div_div_self`

English:
theorem div_div_self
  given: (a : G₀)
  statement: a / (a / a) = a
  proof: by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

中文:
定理 div_div_self
  条件: (a : G₀)
  结论: a / (a / a) = a
  证明: by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

Depends on / 依赖: div_div_eq_mul_div, mul_self_div_self
-/
theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

/--
theorem `ne_zero_of_one_div_ne_zero` / 定理 `ne_zero_of_one_div_ne_zero`

English:
theorem ne_zero_of_one_div_ne_zero
  given: {a : G₀} (h : 1 / a != 0)
  statement: a != 0
  proof: fun ha : a = 0 => by
  rw [ha]; rw [div_zero] at h
  contradiction

中文:
定理 ne_zero_of_one_div_ne_zero
  条件: {a : G₀} (h : 1 / a != 0)
  结论: a != 0
  证明: fun ha : a = 0 => by
  rw [ha]; rw [div_zero] at h
  contradiction

Depends on / 依赖: div_zero
-/
theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a != 0) : a != 0 := fun ha : a = 0 => by
  rw [ha]; rw [div_zero] at h
  contradiction

/--
theorem `eq_zero_of_one_div_eq_zero` / 定理 `eq_zero_of_one_div_eq_zero`

English:
theorem eq_zero_of_one_div_eq_zero
  given: {a : G₀} (h : 1 / a = 0)
  statement: a = 0
  proof: Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

中文:
定理 eq_zero_of_one_div_eq_zero
  条件: {a : G₀} (h : 1 / a = 0)
  结论: a = 0
  证明: Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

Depends on / 依赖: Classical, Classical.byCases, byCases, one_div_ne_zero
-/
theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

/--
theorem `mul_left_surjective₀` / 定理 `mul_left_surjective₀`

English:
theorem mul_left_surjective₀
  given: {a : G₀} (h : a != 0)
  statement: Surjective fun g => a * g
  proof: fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel₀ h]⟩

中文:
定理 mul_left_surjective₀
  条件: {a : G₀} (h : a != 0)
  结论: Surjective fun g => a * g
  证明: fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel₀ h]⟩
-/
theorem mul_left_surjective₀ {a : G₀} (h : a != 0) : Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel₀ h]⟩

/--
theorem `mul_right_surjective₀` / 定理 `mul_right_surjective₀`

English:
theorem mul_right_surjective₀
  given: {a : G₀} (h : a != 0)
  statement: Surjective fun g => g * a
  proof: fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel₀ h]⟩

中文:
定理 mul_right_surjective₀
  条件: {a : G₀} (h : a != 0)
  结论: Surjective fun g => g * a
  证明: fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel₀ h]⟩
-/
theorem mul_right_surjective₀ {a : G₀} (h : a != 0) : Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel₀ h]⟩

/--
lemma `zero_zpow` / 引理 `zero_zpow`

English:
lemma zero_zpow
  statement: forall n : Int, n != 0 -> (0 : G₀) ^ n = 0

中文:
引理 zero_zpow
  结论: 对任意 n : 整数, n != 0 -> (0 : G₀) ^ n = 0
-/
lemma zero_zpow : forall n : Int, n != 0 -> (0 : G₀) ^ n = 0
  | (n : Nat), h => by rw [zpow_natCast, zero_pow]; simpa [Int.natCast_eq_zero] using h
  | .negSucc n, _ => by simp

/--
lemma `zero_zpow_eq` / 引理 `zero_zpow_eq`

English:
lemma zero_zpow_eq
  given: (n : Int)
  statement: (0 : G₀) ^ n = if n = 0 then 1 else 0
  proof: by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

中文:
引理 zero_zpow_eq
  条件: (n : 整数)
  结论: (0 : G₀) ^ n = if n = 0 then 1 else 0
  证明: by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

Depends on / 依赖: split_ifs, zero_zpow, zpow_zero
-/
lemma zero_zpow_eq (n : Int) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

/--
lemma `zero_zpow_eq_one₀` / 引理 `zero_zpow_eq_one₀`

English:
lemma zero_zpow_eq_one₀
  given: {n : Int}
  statement: (0 : G₀) ^ n = 1 ↔ n = 0
  proof: by
  rw [zero_zpow_eq]; rw [one_ne_zero.ite_eq_left_iff]

中文:
引理 zero_zpow_eq_one₀
  条件: {n : 整数}
  结论: (0 : G₀) ^ n = 1 ↔ n = 0
  证明: by
  rw [zero_zpow_eq]; rw [one_ne_zero.ite_eq_left_iff]

Depends on / 依赖: ite_eq_left_iff, one_ne_zero, one_ne_zero.ite_eq_left_iff, zero_zpow_eq
-/
lemma zero_zpow_eq_one₀ {n : Int} : (0 : G₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_zpow_eq]; rw [one_ne_zero.ite_eq_left_iff]

/--
lemma `zpow_add_one₀` / 引理 `zpow_add_one₀`

English:
lemma zpow_add_one₀
  given: (ha : a != 0)
  statement: forall n : Int, a ^ (n + 1) = a ^ n * a

中文:
引理 zpow_add_one₀
  条件: (ha : a != 0)
  结论: 对任意 n : 整数, a ^ (n + 1) = a ^ n * a
-/
lemma zpow_add_one₀ (ha : a != 0) : forall n : Int, a ^ (n + 1) = a ^ n * a
  | (n : Nat) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [ha]
  | .negSucc (n + 1) => by
    rw [Int.negSucc_eq]; rw [zpow_neg]; rw [Int.neg_add]; rw [Int.neg_add_cancel_right]; rw [zpow_neg]; rw [← Int.natCast_succ]; rw [zpow_natCast]; rw [zpow_natCast]; rw [pow_succ' _ (n + 1)]; rw [mul_inv_rev]; rw [mul_assoc]; rw [inv_mul_cancel₀ ha]; rw [mul_one]

/--
lemma `zpow_sub_one₀` / 引理 `zpow_sub_one₀`

English:
lemma zpow_sub_one₀
  given: (ha : a != 0) (n : Int)
  statement: a ^ (n - 1) = a ^ n * a⁻¹
  proof: calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]

中文:
引理 zpow_sub_one₀
  条件: (ha : a != 0) (n : 整数)
  结论: a ^ (n - 1) = a ^ n * a⁻¹
  证明: calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]

Depends on / 依赖: Int.sub_add_cancel, mul_assoc, mul_one, sub_add_cancel
-/
lemma zpow_sub_one₀ (ha : a != 0) (n : Int) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]

/--
lemma `zpow_add₀` / 引理 `zpow_add₀`

English:
lemma zpow_add₀
  given: (ha : a != 0) (m n : Int)
  statement: a ^ (m + n) = a ^ m * a ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, Int.add_sub_assoc]

中文:
引理 zpow_add₀
  条件: (ha : a != 0) (m n : 整数)
  结论: a ^ (m + n) = a ^ m * a ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, Int.add_sub_assoc]

Depends on / 依赖: Int.add_assoc, Int.add_sub_assoc, add_assoc, add_sub_assoc, mul_assoc
-/
lemma zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, Int.add_sub_assoc]

/--
lemma `zpow_add'` / 引理 `zpow_add'`

English:
lemma zpow_add'
  given: {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 0)
  proof: by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or, not_true, Ne, hm, hn, false_and, or_false] at h
    rw [zero_zpow _ h]; rw [zero_zpow _ hm]; rw [zero_mul]
  · exact zpow_add₀ ha m n

中文:
引理 zpow_add'
  条件: {m n : 整数} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 0)
  证明: by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or, not_true, Ne, hm, hn, false_and, or_false] at h
    rw [zero_zpow _ h]; rw [zero_zpow _ hm]; rw [zero_mul]
  · exact zpow_add₀ ha m n

Depends on / 依赖: false_and, false_or, not_true, or_false, zero_mul, zero_zpow
-/
lemma zpow_add' {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or, not_true, Ne, hm, hn, false_and, or_false] at h
    rw [zero_zpow _ h]; rw [zero_zpow _ hm]; rw [zero_mul]
  · exact zpow_add₀ ha m n

/--
lemma `zpow_one_add₀` / 引理 `zpow_one_add₀`

English:
lemma zpow_one_add₀
  given: (h : a != 0) (i : Int)
  statement: a ^ (1 + i) = a * a ^ i
  proof: by rw [zpow_add₀ h, zpow_one]

中文:
引理 zpow_one_add₀
  条件: (h : a != 0) (i : 整数)
  结论: a ^ (1 + i) = a * a ^ i
  证明: by rw [zpow_add₀ h, zpow_one]

Depends on / 依赖: zpow_one
-/
lemma zpow_one_add₀ (h : a != 0) (i : Int) : a ^ (1 + i) = a * a ^ i := by rw [zpow_add₀ h, zpow_one]

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀]

/--
theorem `div_mul_eq_mul_div₀` / 定理 `div_mul_eq_mul_div₀`

English:
theorem div_mul_eq_mul_div₀
  given: (a b c : G₀)
  statement: a / c * b = a * b / c
  proof: by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]

中文:
定理 div_mul_eq_mul_div₀
  条件: (a b c : G₀)
  结论: a / c * b = a * b / c
  证明: by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]

Depends on / 依赖: div_eq_mul_inv, mul_assoc, mul_comm, simp_rw
-/
theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]

/--
lemma `div_sq_cancel` / 引理 `div_sq_cancel`

English:
lemma div_sq_cancel
  given: (a b : G₀)
  statement: a ^ 2 * b / a = a * b
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]

中文:
引理 div_sq_cancel
  条件: (a b : G₀)
  结论: a ^ 2 * b / a = a * b
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]

Depends on / 依赖: eq_or_ne, mul_assoc
-/
lemma div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]

end CommGroupWithZero
