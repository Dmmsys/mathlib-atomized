/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Pulling back ordered rings along injective maps
-/

public section

variable {R S : Type*}

namespace Function.Injective
variable [Semiring R] [PartialOrder R]

/--
lemma `isOrderedRing` / 引理 `isOrderedRing`

English:
lemma isOrderedRing
  statement: [IsOrderedRing R] [Semiring S] [PartialOrder S]
  proof: Function.Injective.isOrderedAddMonoid f add le
  zero_le_one := by simp only [← le, zero, one, zero_le_one]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; refine mul_le_mul_of_nonneg_left (le.2 hbc) ?_; rwa [← zero, le]
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; refine mul_le_mul_of_nonneg_right (le.2 hbc) ?_; rwa [← zero, le]

中文:
引理 isOrderedRing
  结论: [是Ordered环 R] [半环 S] [偏序 S]
  证明: Function.Injective.isOrderedAddMonoid f add le
  zero_le_one := by simp only [← le, zero, one, zero_le_one]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; refine mul_le_mul_of_nonneg_left (le.2 hbc) ?_; rwa [← zero, le]
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; refine mul_le_mul_of_nonneg_right (le.2 hbc) ?_; rwa [← zero, le]
-/
protected lemma isOrderedRing [IsOrderedRing R] [Semiring S] [PartialOrder S]
    (f : S -> R) (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (le : forall {x y}, f x <= f y ↔ x <= y) :
    IsOrderedRing S where
  __ := Function.Injective.isOrderedAddMonoid f add le
  zero_le_one := by simp only [← le, zero, one, zero_le_one]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; refine mul_le_mul_of_nonneg_left (le.2 hbc) ?_; rwa [← zero, le]
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le]; rw [mul]; rw [mul]; refine mul_le_mul_of_nonneg_right (le.2 hbc) ?_; rwa [← zero, le]

/--
lemma `isStrictOrderedRing` / 引理 `isStrictOrderedRing`

English:
lemma isStrictOrderedRing
  statement: [IsStrictOrderedRing R] [Semiring S] [PartialOrder S]
  proof: Function.Injective.isOrderedCancelAddMonoid f add le
  __ := domain_nontrivial f zero one
  __ := Function.Injective.isOrderedRing f zero one add mul le
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; refine mul_lt_mul_of_pos_left (lt.2 hbc) ?_; rwa [← zero, lt]
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; refine mul_lt_mul_of_pos_right (lt.2 hbc) ?_; rwa [← zero, lt]

中文:
引理 isStrictOrderedRing
  结论: [是StrictOrdered环 R] [半环 S] [偏序 S]
  证明: Function.Injective.isOrderedCancelAddMonoid f add le
  __ := domain_nontrivial f zero one
  __ := Function.Injective.isOrderedRing f zero one add mul le
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; refine mul_lt_mul_of_pos_left (lt.2 hbc) ?_; rwa [← zero, lt]
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; refine mul_lt_mul_of_pos_right (lt.2 hbc) ?_; rwa [← zero, lt]
-/
protected lemma isStrictOrderedRing [IsStrictOrderedRing R] [Semiring S] [PartialOrder S]
    (f : S -> R) (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y) :
    IsStrictOrderedRing S where
  __ := Function.Injective.isOrderedCancelAddMonoid f add le
  __ := domain_nontrivial f zero one
  __ := Function.Injective.isOrderedRing f zero one add mul le
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; refine mul_lt_mul_of_pos_left (lt.2 hbc) ?_; rwa [← zero, lt]
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt]; rw [mul]; rw [mul]; refine mul_lt_mul_of_pos_right (lt.2 hbc) ?_; rwa [← zero, lt]

end Function.Injective
