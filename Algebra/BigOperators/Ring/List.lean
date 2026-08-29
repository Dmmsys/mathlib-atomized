/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Big operators on a list in rings

This file contains the results concerning the interaction of list big operators with rings.
-/

public section

open MulOpposite List

variable {ι κ M M₀ R : Type*}

namespace Commute
variable [NonUnitalNonAssocSemiring R]

/--
lemma `list_sum_right` / 引理 `list_sum_right`

English:
lemma list_sum_right
  given: (a : R) (l : List R) (h : forall b in l, Commute a b)
  statement: Commute a l.sum
  proof: by
  induction l with
  | nil => exact Commute.zero_right _
  | cons x xs ih =>
    rw [List.sum_cons]
    exact (h _ mem_cons_self).add_right (ih fun j hj => h _ <| mem_cons_of_mem _ hj)

中文:
引理 list_sum_right
  条件: (a : R) (l : 列表 R) (h : 对任意 b in l, Commute a b)
  结论: Commute a l.求和
  证明: by
  induction l with
  | nil => exact Commute.zero_right _
  | cons x xs ih =>
    rw [List.sum_cons]
    exact (h _ mem_cons_self).add_right (ih fun j hj => h _ <| mem_cons_of_mem _ hj)

Depends on / 依赖: Commute, Commute.zero_right, List.sum_cons, add_right, mem_cons_of_mem, mem_cons_self, sum_cons, zero_right
-/
lemma list_sum_right (a : R) (l : List R) (h : forall b in l, Commute a b) : Commute a l.sum := by
  induction l with
  | nil => exact Commute.zero_right _
  | cons x xs ih =>
    rw [List.sum_cons]
    exact (h _ mem_cons_self).add_right (ih fun j hj => h _ <| mem_cons_of_mem _ hj)

/--
lemma `list_sum_left` / 引理 `list_sum_left`

English:
lemma list_sum_left
  given: (b : R) (l : List R) (h : forall a in l, Commute a b)
  statement: Commute l.sum b
  proof: ((Commute.list_sum_right _ _) fun _x hx => (h _ hx).symm).symm

中文:
引理 list_sum_left
  条件: (b : R) (l : 列表 R) (h : 对任意 a in l, Commute a b)
  结论: Commute l.求和 b
  证明: ((Commute.list_sum_right _ _) fun _x hx => (h _ hx).symm).symm

Depends on / 依赖: Commute, Commute.list_sum_right, list_sum_right
-/
lemma list_sum_left (b : R) (l : List R) (h : forall a in l, Commute a b) : Commute l.sum b :=
  ((Commute.list_sum_right _ _) fun _x hx => (h _ hx).symm).symm

end Commute

namespace List
section HasDistribNeg
variable [Monoid M] [HasDistribNeg M]

@[simp]
/--
lemma `prod_map_neg` / 引理 `prod_map_neg`

English:
lemma prod_map_neg
  given: (l : List M)
  proof: by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]

中文:
引理 prod_map_neg
  条件: (l : 列表 M)
  证明: by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]

Depends on / 依赖: Commute, Commute.neg_one_left, left_comm, neg_one_left, pow_left, pow_succ
-/
lemma prod_map_neg (l : List M) :
    (l.map Neg.neg).prod = (-1) ^ l.length * l.prod := by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]

end HasDistribNeg

section MonoidWithZero
variable [MonoidWithZero M₀] {l : List M₀}

/--
lemma `prod_eq_zero` / 引理 `prod_eq_zero`

English:
lemma prod_eq_zero
  statement: forall {l : List M₀}, (0 : M₀) in l -> l.prod = 0

中文:
引理 prod_eq_zero
  结论: 对任意 {l : 列表 M₀}, (0 : M₀) in l -> l.乘积 = 0
-/
lemma prod_eq_zero : forall {l : List M₀}, (0 : M₀) in l -> l.prod = 0
  -- | absurd h (not_mem_nil _)
  | a :: l, h => by
    rw [prod_cons]
    rcases mem_cons.1 h with ha | hl
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (prod_eq_zero hl)]

variable [Nontrivial M₀] [NoZeroDivisors M₀]

/--
lemma `prod_eq_zero_iff` / 引理 `prod_eq_zero_iff`

English:
lemma prod_eq_zero_iff
  statement: forall {l : List M₀}, l.prod = 0 ↔ (0 : M₀) in l

中文:
引理 prod_eq_zero_iff
  结论: 对任意 {l : 列表 M₀}, l.乘积 = 0 ↔ (0 : M₀) in l
-/
@[simp] lemma prod_eq_zero_iff : forall {l : List M₀}, l.prod = 0 ↔ (0 : M₀) in l
  | [] => by simp
  | a :: l => by rw [prod_cons, mul_eq_zero, prod_eq_zero_iff, mem_cons, eq_comm]

/--
lemma `prod_ne_zero` / 引理 `prod_ne_zero`

English:
lemma prod_ne_zero
  given: (hL : (0 : M₀) ∉ l)
  statement: l.prod != 0
  proof: mt prod_eq_zero_iff.1 hL

中文:
引理 prod_ne_zero
  条件: (hL : (0 : M₀) ∉ l)
  结论: l.乘积 != 0
  证明: mt prod_eq_zero_iff.1 hL

Depends on / 依赖: prod_eq_zero_iff
-/
lemma prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod != 0 := mt prod_eq_zero_iff.1 hL

end MonoidWithZero

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] (l : List ι) (f : ι -> R) (r : R)

/--
lemma `sum_map_mul_left` / 引理 `sum_map_mul_left`

English:
lemma sum_map_mul_left
  statement: (l.map fun b => r * f b).sum = r * (l.map f).sum
  proof: sum_map_hom l f AddMonoidHom.mulLeft r

中文:
引理 sum_map_mul_left
  结论: (l.map fun b => r * f b).求和 = r * (l.map f).求和
  证明: sum_map_hom l f AddMonoidHom.mulLeft r

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, mulLeft, sum_map_hom
-/
lemma sum_map_mul_left : (l.map fun b => r * f b).sum = r * (l.map f).sum :=
sum_map_hom l f AddMonoidHom.mulLeft r

/--
lemma `sum_map_mul_right` / 引理 `sum_map_mul_right`

English:
lemma sum_map_mul_right
  statement: (l.map fun b => f b * r).sum = (l.map f).sum * r
  proof: sum_map_hom l f AddMonoidHom.mulRight r

中文:
引理 sum_map_mul_right
  结论: (l.map fun b => f b * r).求和 = (l.map f).求和 * r
  证明: sum_map_hom l f AddMonoidHom.mulRight r

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, mulRight, sum_map_hom
-/
lemma sum_map_mul_right : (l.map fun b => f b * r).sum = (l.map f).sum * r :=
sum_map_hom l f AddMonoidHom.mulRight r

end NonUnitalNonAssocSemiring

/--
lemma `dvd_sum` / 引理 `dvd_sum`

English:
lemma dvd_sum
  given: [NonUnitalSemiring R] {a} {l : List R} (h : forall x in l, a ∣ x)
  statement: a ∣ l.sum
  proof: by
  induction l with
  | nil => exact dvd_zero _
  | cons x l ih =>
    rw [List.sum_cons]
    exact dvd_add (h _ mem_cons_self) (ih fun x hx => h x (mem_cons_of_mem _ hx))

中文:
引理 dvd_sum
  条件: [非幺半环 R] {a} {l : 列表 R} (h : 对任意 x in l, a ∣ x)
  结论: a ∣ l.求和
  证明: by
  induction l with
  | nil => exact dvd_zero _
  | cons x l ih =>
    rw [List.sum_cons]
    exact dvd_add (h _ mem_cons_self) (ih fun x hx => h x (mem_cons_of_mem _ hx))

Depends on / 依赖: List.sum_cons, dvd_add, dvd_zero, mem_cons_of_mem, mem_cons_self, sum_cons
-/
lemma dvd_sum [NonUnitalSemiring R] {a} {l : List R} (h : forall x in l, a ∣ x) : a ∣ l.sum := by
  induction l with
  | nil => exact dvd_zero _
  | cons x l ih =>
    rw [List.sum_cons]
    exact dvd_add (h _ mem_cons_self) (ih fun x hx => h x (mem_cons_of_mem _ hx))

/--
lemma `sum_zipWith_distrib_left` / 引理 `sum_zipWith_distrib_left`

English:
lemma sum_zipWith_distrib_left
  given: [NonUnitalNonAssocSemiring R] (f : ι -> κ -> R) (a : R)

中文:
引理 sum_zipWith_distrib_left
  条件: [非幺非结合半环 R] (f : ι -> κ -> R) (a : R)
-/
@[simp] lemma sum_zipWith_distrib_left [NonUnitalNonAssocSemiring R] (f : ι -> κ -> R) (a : R) :
    forall (l₁ : List ι) (l₂ : List κ),
      (zipWith (fun i j => a * f i j) l₁ l₂).sum = a * (zipWith f l₁ l₂).sum
  | [], _ => by simp
  | _, [] => by simp
  | i :: l₁, j :: l₂ => by simp [sum_zipWith_distrib_left, mul_add]

end List
