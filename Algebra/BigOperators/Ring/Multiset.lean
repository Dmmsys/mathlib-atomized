/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.Data.Multiset.Sections

/-! # Lemmas about `Multiset.sum` and `Multiset.prod` requiring extra algebra imports -/

public section


variable {ι M M₀ R : Type*}

namespace Multiset
section CommMonoid
variable [CommMonoid M] [HasDistribNeg M]

/--
lemma `prod_map_neg` / 引理 `prod_map_neg`

English:
lemma prod_map_neg
  given: (s : Multiset M)
  statement: (s.map Neg.neg).prod = (-1) ^ card s * s.prod
  proof: Quotient.inductionOn s (by simp)

中文:
引理 prod_map_neg
  条件: (s : Multiset M)
  结论: (s.map 取负.neg).乘积 = (-1) ^ card s * s.乘积
  证明: Quotient.inductionOn s (by simp)
-/
@[simp] lemma prod_map_neg (s : Multiset M) : (s.map Neg.neg).prod = (-1) ^ card s * s.prod :=
  Quotient.inductionOn s (by simp)

end CommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {s : Multiset M₀}

/--
lemma `prod_eq_zero` / 引理 `prod_eq_zero`

English:
lemma prod_eq_zero
  given: (h : (0 : M₀) in s)
  statement: s.prod = 0
  proof: by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

中文:
引理 prod_eq_zero
  条件: (h : (0 : M₀) in s)
  结论: s.乘积 = 0
  证明: by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

Depends on / 依赖: Multiset, Multiset.exists_cons_of_mem, Multiset.prod_cons, exists_cons_of_mem, prod_cons
-/
lemma prod_eq_zero (h : (0 : M₀) in s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]

variable [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀}

/--
lemma `prod_eq_zero_iff` / 引理 `prod_eq_zero_iff`

English:
lemma prod_eq_zero_iff
  statement: s.prod = 0 ↔ (0 : M₀) in s
  proof: Quotient.inductionOn s fun l => by rw [quot_mk_to_coe, prod_coe]; exact List.prod_eq_zero_iff

中文:
引理 prod_eq_zero_iff
  结论: s.乘积 = 0 ↔ (0 : M₀) in s
  证明: Quotient.inductionOn s fun l => by rw [quot_mk_to_coe, prod_coe]; exact List.prod_eq_zero_iff
-/
@[simp] lemma prod_eq_zero_iff : s.prod = 0 ↔ (0 : M₀) in s :=
  Quotient.inductionOn s fun l => by rw [quot_mk_to_coe, prod_coe]; exact List.prod_eq_zero_iff

/--
lemma `prod_ne_zero` / 引理 `prod_ne_zero`

English:
lemma prod_ne_zero
  given: (h : (0 : M₀) ∉ s)
  statement: s.prod != 0
  proof: mt prod_eq_zero_iff.1 h

中文:
引理 prod_ne_zero
  条件: (h : (0 : M₀) ∉ s)
  结论: s.乘积 != 0
  证明: mt prod_eq_zero_iff.1 h

Depends on / 依赖: prod_eq_zero_iff
-/
lemma prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod != 0 := mt prod_eq_zero_iff.1 h

end CommMonoidWithZero

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] {a : R} {s : Multiset ι} {f : ι -> R}

/--
lemma `sum_map_mul_left` / 引理 `sum_map_mul_left`

English:
lemma sum_map_mul_left
  statement: sum (s.map fun i => a * f i) = a * sum (s.map f)
  proof: Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]

中文:
引理 sum_map_mul_left
  结论: 求和 (s.map fun i => a * f i) = a * 求和 (s.map f)
  证明: Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on, mul_add
-/
lemma sum_map_mul_left : sum (s.map fun i => a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]

/--
lemma `sum_map_mul_right` / 引理 `sum_map_mul_right`

English:
lemma sum_map_mul_right
  statement: sum (s.map fun i => f i * a) = sum (s.map f) * a
  proof: Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]

中文:
引理 sum_map_mul_right
  结论: 求和 (s.map fun i => f i * a) = 求和 (s.map f) * a
  证明: Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]

Depends on / 依赖: Multiset, Multiset.induction_on, add_mul, induction_on
-/
lemma sum_map_mul_right : sum (s.map fun i => f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R] {s : Multiset R} {a : R}

/--
lemma `dvd_sum` / 引理 `dvd_sum`

English:
lemma dvd_sum
  statement: (forall x in s, a ∣ x) -> a ∣ s.sum
  proof: Multiset.induction_on s (fun _ => dvd_zero _) fun x s ih h => by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy => h _ <| mem_cons.2 <| Or.inr hy)

中文:
引理 dvd_sum
  结论: (对任意 x in s, a ∣ x) -> a ∣ s.求和
  证明: Multiset.induction_on s (fun _ => dvd_zero _) fun x s ih h => by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy => h _ <| mem_cons.2 <| Or.inr hy)

Depends on / 依赖: Multiset, Multiset.induction_on, Or.inr, dvd_add, dvd_zero, induction_on, mem_cons, mem_cons_self, sum_cons
-/
lemma dvd_sum : (forall x in s, a ∣ x) -> a ∣ s.sum :=
  Multiset.induction_on s (fun _ => dvd_zero _) fun x s ih h => by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy => h _ <| mem_cons.2 <| Or.inr hy)

end NonUnitalSemiring

section CommSemiring
variable [CommSemiring R]

/--
lemma `prod_map_sum` / 引理 `prod_map_sum`

English:
lemma prod_map_sum
  given: {s : Multiset (Multiset R)}
  proof: Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]

中文:
引理 prod_map_sum
  条件: {s : Multiset (Multiset R)}
  证明: Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on, map_bind, sum_map_mul_left, sum_map_mul_right
-/
lemma prod_map_sum {s : Multiset (Multiset R)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]

/--
lemma `prod_map_add` / 引理 `prod_map_add`

English:
lemma prod_map_add
  given: {s : Multiset ι} {f g : ι -> R}
  proof: by
  refine s.induction_on ?_ fun a s ih => ?_
  · simp only [map_zero, prod_zero, antidiagonal_zero, map_singleton, mul_one, sum_singleton]
  · simp only [map_cons, prod_cons, ih, sum_map_mul_left.symm, add_mul, mul_left_comm (f a),
      mul_left_comm (g a), sum_map_add, antidiagonal_cons, Prod.ma

中文:
引理 prod_map_add
  条件: {s : Multiset ι} {f g : ι -> R}
  证明: by
  refine s.induction_on ?_ fun a s ih => ?_
  · simp only [map_zero, prod_zero, antidiagonal_zero, map_singleton, mul_one, sum_singleton]
  · simp only [map_cons, prod_cons, ih, sum_map_mul_left.symm, add_mul, mul_left_comm (f a),
      mul_left_comm (g a), sum_map_add, antidiagonal_cons, Prod.ma

Depends on / 依赖: Function, Function.comp_apply, Prod.map_fst, Prod.map_snd, add_comm, add_mul, antidiagonal_cons, antidiagonal_zero, comp_apply, id_eq, induction_on, map_add, map_cons, map_fst, map_map, map_singleton, map_snd, map_zero, mul_assoc, mul_left_comm
-/
lemma prod_map_add {s : Multiset ι} {f g : ι -> R} :
    prod (s.map fun i => f i + g i) =
      sum ((antidiagonal s).map fun p => (p.1.map f).prod * (p.2.map g).prod) := by
  refine s.induction_on ?_ fun a s ih => ?_
  · simp only [map_zero, prod_zero, antidiagonal_zero, map_singleton, mul_one, sum_singleton]
  · simp only [map_cons, prod_cons, ih, sum_map_mul_left.symm, add_mul, mul_left_comm (f a),
      mul_left_comm (g a), sum_map_add, antidiagonal_cons, Prod.map_fst, Prod.map_snd,
      id_eq, map_add, map_map, Function.comp_apply, mul_assoc, sum_add]
    exact add_comm _ _

end CommSemiring
end Multiset

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

/--
theorem `multiset_sum_right` / 定理 `multiset_sum_right`

English:
theorem multiset_sum_right
  given: (a : R) (h : forall b in s, Commute a b)
  statement: Commute a s.sum
  proof: by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe]; rw [sum_coe]
  exact Commute.list_sum_right _ _ h

中文:
定理 multiset_sum_right
  条件: (a : R) (h : 对任意 b in s, Commute a b)
  结论: Commute a s.求和
  证明: by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe]; rw [sum_coe]
  exact Commute.list_sum_right _ _ h

Depends on / 依赖: Commute, Commute.list_sum_right, Quotient, Quotient.inductionOn, inductionOn, list_sum_right, quot_mk_to_coe, sum_coe
-/
theorem multiset_sum_right (a : R) (h : forall b in s, Commute a b) : Commute a s.sum := by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe]; rw [sum_coe]
  exact Commute.list_sum_right _ _ h

/--
theorem `multiset_sum_left` / 定理 `multiset_sum_left`

English:
theorem multiset_sum_left
  given: (b : R) (h : forall a in s, Commute a b)
  statement: Commute s.sum b
  proof: ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

中文:
定理 multiset_sum_left
  条件: (b : R) (h : 对任意 a in s, Commute a b)
  结论: Commute s.求和 b
  证明: ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

Depends on / 依赖: Commute, Commute.multiset_sum_right, multiset_sum_right
-/
theorem multiset_sum_left (b : R) (h : forall a in s, Commute a b) : Commute s.sum b :=
  ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm

end Commute
