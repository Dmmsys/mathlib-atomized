/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Minimal Axioms for a Ring

This file defines constructors to define a `Ring` or `CommRing` structure on a Type, while proving
a minimum number of equalities.

## Main Definitions

* `Ring.ofMinimalAxioms`: Define a `Ring` structure on a Type by proving a minimized set of axioms
* `CommRing.ofMinimalAxioms`: Define a `CommRing` structure on a Type by proving a minimized set of
  axioms

-/

public section

universe u

/--
Definition of `Ring.ofMinimalAxioms` / `Ring.ofMinimalAxioms` 的定义

English:
abbreviation Ring.ofMinimalAxioms
  signature: {R : Type u}
  body: letI := AddGroup.ofLeftAxioms add_assoc zero_add neg_add_cancel
  haveI add_comm : forall a b, a + b = b + a := by
    intro a b
    have h₁ : (1 + 1 : R) * (a + b) = a + (a + b) + b := by
      rw [left_distrib]
      simp only [right_distrib, one_mul, add_assoc]
    have h₂ : (1 + 1 : R) * (a + b) = a + (b + a) + b := by
      rw [right_distrib]
      simp only [left_distrib, one_mul, add_assoc]
    have := h₁.symm.trans h₂
    rwa [add_left_inj, add_right_inj] at this
  haveI zero_mul : forall a, (0 : R) * a = 0 := fun a => by
    have : 0 * a = 0 * a + 0 * a :=
      calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [right_distrib]
    rwa [left_eq_add] at this
  haveI mul_zero : forall a, a * (0 : R) = 0 := fun a => by
    have : a * 0 = a * 0 + a * 0 :=
      calc a * 0 = a * (0 + 0) := by rw [zero_add]
      _ = a * 0 + a * 0 := by rw [left_distrib]
    rwa [left_eq_add] at this
  { add_comm := add_comm
    left_distrib := left_distrib
    right_distrib := right_distrib
    zero_mul := zero_mul
    mul_zero := mul_zero
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
    neg_add_cancel := neg_add_cancel }

中文:
缩写 环.ofMinimalAxioms
  签名: {R : 类型u}
  定义体: letI := AddGroup.ofLeftAxioms add_assoc zero_add neg_add_cancel
  haveI add_comm : forall a b, a + b = b + a := by
    intro a b
    have h₁ : (1 + 1 : R) * (a + b) = a + (a + b) + b := by
      rw [left_distrib]
      simp only [right_distrib, one_mul, add_assoc]
    have h₂ : (1 + 1 : R) * (a + b) = a + (b + a) + b := by
      rw [right_distrib]
      simp only [left_distrib, one_mul, add_assoc]
    have := h₁.symm.trans h₂
    rwa [add_left_inj, add_right_inj] at this
  haveI zero_mul : forall a, (0 : R) * a = 0 := fun a => by
    have : 0 * a = 0 * a + 0 * a :=
      calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [right_distrib]
    rwa [left_eq_add] at this
  haveI mul_zero : forall a, a * (0 : R) = 0 := fun a => by
    have : a * 0 = a * 0 + a * 0 :=
      calc a * 0 = a * (0 + 0) := by rw [zero_add]
      _ = a * 0 + a * 0 := by rw [left_distrib]
    rwa [left_eq_add] at this
  { add_comm := add_comm
    left_distrib := left_distrib
    right_distrib := right_distrib
    zero_mul := zero_mul
    mul_zero := mul_zero
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
    neg_add_cancel := neg_add_cancel }

Depends on / 依赖: AddGroup, AddGroup.ofLeftAxioms, add_assoc, add_comm, add_left_inj, add_right_inj, left_distrib, neg_add_cancel, ofLeftAxioms, one_mul, right_distrib, symm.trans, zero_add, zero_mul
-/
abbrev Ring.ofMinimalAxioms {R : Type u}
    [Add R] [Mul R] [Neg R] [Zero R] [One R]
    (add_assoc : forall a b c : R, a + b + c = a + (b + c))
    (zero_add : forall a : R, 0 + a = a)
    (neg_add_cancel : forall a : R, -a + a = 0)
    (mul_assoc : forall a b c : R, a * b * c = a * (b * c))
    (one_mul : forall a : R, 1 * a = a)
    (mul_one : forall a : R, a * 1 = a)
    (left_distrib : forall a b c : R, a * (b + c) = a * b + a * c)
    (right_distrib : forall a b c : R, (a + b) * c = a * c + b * c) : Ring R :=
  letI := AddGroup.ofLeftAxioms add_assoc zero_add neg_add_cancel
  haveI add_comm : forall a b, a + b = b + a := by
    intro a b
    have h₁ : (1 + 1 : R) * (a + b) = a + (a + b) + b := by
      rw [left_distrib]
      simp only [right_distrib, one_mul, add_assoc]
    have h₂ : (1 + 1 : R) * (a + b) = a + (b + a) + b := by
      rw [right_distrib]
      simp only [left_distrib, one_mul, add_assoc]
    have := h₁.symm.trans h₂
    rwa [add_left_inj, add_right_inj] at this
  haveI zero_mul : forall a, (0 : R) * a = 0 := fun a => by
    have : 0 * a = 0 * a + 0 * a :=
      calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [right_distrib]
    rwa [left_eq_add] at this
  haveI mul_zero : forall a, a * (0 : R) = 0 := fun a => by
    have : a * 0 = a * 0 + a * 0 :=
      calc a * 0 = a * (0 + 0) := by rw [zero_add]
      _ = a * 0 + a * 0 := by rw [left_distrib]
    rwa [left_eq_add] at this
  { add_comm := add_comm
    left_distrib := left_distrib
    right_distrib := right_distrib
    zero_mul := zero_mul
    mul_zero := mul_zero
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
    neg_add_cancel := neg_add_cancel }

/--
Definition of `CommRing.ofMinimalAxioms` / `CommRing.ofMinimalAxioms` 的定义

English:
abbreviation CommRing.ofMinimalAxioms
  signature: {R : Type u}
  body: haveI mul_one : forall a : R, a * 1 = a := fun a => by
    rw [mul_comm]; rw [one_mul]
  haveI right_distrib : forall a b c : R, (a + b) * c = a * c + b * c := fun a b c => by
    rw [mul_comm]; rw [left_distrib]; rw [mul_comm]; rw [mul_comm b c]
  letI := Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel mul_assoc
    one_mul mul_one left_distrib right_distrib
  { mul_comm := mul_comm }

中文:
缩写 交换环.ofMinimalAxioms
  签名: {R : 类型u}
  定义体: haveI mul_one : forall a : R, a * 1 = a := fun a => by
    rw [mul_comm]; rw [one_mul]
  haveI right_distrib : forall a b c : R, (a + b) * c = a * c + b * c := fun a b c => by
    rw [mul_comm]; rw [left_distrib]; rw [mul_comm]; rw [mul_comm b c]
  letI := Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel mul_assoc
    one_mul mul_one left_distrib right_distrib
  { mul_comm := mul_comm }

Depends on / 依赖: Ring.ofMinimalAxioms, add_assoc, left_distrib, mul_assoc, mul_comm, mul_one, neg_add_cancel, ofMinimalAxioms, one_mul, right_distrib, zero_add
-/
abbrev CommRing.ofMinimalAxioms {R : Type u}
    [Add R] [Mul R] [Neg R] [Zero R] [One R]
    (add_assoc : forall a b c : R, a + b + c = a + (b + c))
    (zero_add : forall a : R, 0 + a = a)
    (neg_add_cancel : forall a : R, -a + a = 0)
    (mul_assoc : forall a b c : R, a * b * c = a * (b * c))
    (mul_comm : forall a b : R, a * b = b * a)
    (one_mul : forall a : R, 1 * a = a)
    (left_distrib : forall a b c : R, a * (b + c) = a * b + a * c) : CommRing R :=
  haveI mul_one : forall a : R, a * 1 = a := fun a => by
    rw [mul_comm]; rw [one_mul]
  haveI right_distrib : forall a b c : R, (a + b) * c = a * c + b * c := fun a b c => by
    rw [mul_comm]; rw [left_distrib]; rw [mul_comm]; rw [mul_comm b c]
  letI := Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel mul_assoc
    one_mul mul_one left_distrib right_distrib
  { mul_comm := mul_comm }
