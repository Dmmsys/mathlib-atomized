/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the Cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {F ι M N : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι -> M}

/-- Product of a multiset given a commutative monoid structure on `M`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      /-- Sum of a multiset given a commutative additive monoid structure on `M`.
      `sum {a, b, c} = a + b + c` -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : Multiset M -> M
  body: foldr (· * ·) 1

@[to_additive]

中文:
定义 乘积
  签名: : Multiset M -> M
  定义体: foldr (· * ·) 1

@[to_additive]
-/
def prod : Multiset M -> M :=
  foldr (· * ·) 1

@[to_additive]
/--
theorem `prod_eq_foldr` / 定理 `prod_eq_foldr`

English:
theorem prod_eq_foldr
  given: (s : Multiset M)
  proof: rfl

@[to_additive]

中文:
定理 prod_eq_foldr
  条件: (s : Multiset M)
  证明: rfl

@[to_additive]
-/
theorem prod_eq_foldr (s : Multiset M) :
    prod s = foldr (· * ·) 1 s :=
  rfl

@[to_additive]
/--
theorem `prod_eq_foldl` / 定理 `prod_eq_foldl`

English:
theorem prod_eq_foldl
  given: (s : Multiset M)
  proof: (foldr_swap _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]

中文:
定理 prod_eq_foldl
  条件: (s : Multiset M)
  证明: (foldr_swap _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: foldr_swap, mul_comm
-/
theorem prod_eq_foldl (s : Multiset M) :
    prod s = foldl (· * ·) 1 s :=
  (foldr_swap _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]
/--
theorem `prod_coe` / 定理 `prod_coe`

English:
theorem prod_coe
  given: (l : List M)
  statement: prod ↑l = l.prod
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 prod_coe
  条件: (l : 列表 M)
  结论: 乘积 ↑l = l.乘积
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem prod_coe (l : List M) : prod ↑l = l.prod := rfl

@[to_additive (attr := simp)]
/--
theorem `prod_toList` / 定理 `prod_toList`

English:
theorem prod_toList
  given: (s : Multiset M)
  statement: s.toList.prod = s.prod
  proof: by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]

@[to_additive (attr := simp, grind =)]

中文:
定理 prod_toList
  条件: (s : Multiset M)
  结论: s.toList.乘积 = s.乘积
  证明: by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]

@[to_additive (attr := simp, grind =)]

Depends on / 依赖: coe_toList, conv_rhs, prod_coe
-/
theorem prod_toList (s : Multiset M) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]

@[to_additive (attr := simp, grind =)]
/--
theorem `prod_map_toList` / 定理 `prod_map_toList`

English:
theorem prod_map_toList
  given: (s : Multiset ι) (f : ι -> M)
  statement: (s.toList.map f).prod = (s.map f).prod
  proof: by
  rw [← Multiset.prod_coe]; rw [← Multiset.map_coe]; rw [coe_toList]

@[to_additive (attr := simp, grind =)]

中文:
定理 prod_map_toList
  条件: (s : Multiset ι) (f : ι -> M)
  结论: (s.toList.map f).乘积 = (s.map f).乘积
  证明: by
  rw [← Multiset.prod_coe]; rw [← Multiset.map_coe]; rw [coe_toList]

@[to_additive (attr := simp, grind =)]

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, coe_toList, map_coe, prod_coe
-/
theorem prod_map_toList (s : Multiset ι) (f : ι -> M) : (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_coe]; rw [← Multiset.map_coe]; rw [coe_toList]

@[to_additive (attr := simp, grind =)]
/--
theorem `prod_zero` / 定理 `prod_zero`

English:
theorem prod_zero
  statement: @prod M _ 0 = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 prod_zero
  结论: @乘积 M _ 0 = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem prod_zero : @prod M _ 0 = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `prod_cons` / 定理 `prod_cons`

English:
theorem prod_cons
  given: (a : M) (s)
  statement: prod (a ::ₘ s) = a * prod s
  proof: foldr_cons _ _ _ _

@[to_additive (attr := simp)]

中文:
定理 prod_cons
  条件: (a : M) (s)
  结论: 乘积 (a ::ₘ s) = a * 乘积 s
  证明: foldr_cons _ _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: foldr_cons
-/
theorem prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _

@[to_additive (attr := simp)]
/--
theorem `prod_singleton` / 定理 `prod_singleton`

English:
theorem prod_singleton
  given: (a : M)
  statement: prod {a} = a
  proof: by
  simp only [mul_one, prod_cons, ← cons_zero, prod_zero]

@[to_additive]

中文:
定理 prod_singleton
  条件: (a : M)
  结论: 乘积 {a} = a
  证明: by
  simp only [mul_one, prod_cons, ← cons_zero, prod_zero]

@[to_additive]

Depends on / 依赖: cons_zero, mul_one, prod_cons, prod_zero
-/
theorem prod_singleton (a : M) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, prod_zero]

@[to_additive]
/--
theorem `prod_pair` / 定理 `prod_pair`

English:
theorem prod_pair
  given: (a b : M)
  statement: ({a, b} : Multiset M).prod = a * b
  proof: by
  rw [insert_eq_cons]; rw [prod_cons]; rw [prod_singleton]

@[to_additive (attr := simp)]

中文:
定理 prod_pair
  条件: (a b : M)
  结论: ({a, b} : Multiset M).乘积 = a * b
  证明: by
  rw [insert_eq_cons]; rw [prod_cons]; rw [prod_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: insert_eq_cons, prod_cons, prod_singleton
-/
theorem prod_pair (a b : M) : ({a, b} : Multiset M).prod = a * b := by
  rw [insert_eq_cons]; rw [prod_cons]; rw [prod_singleton]

@[to_additive (attr := simp)]
/--
theorem `prod_replicate` / 定理 `prod_replicate`

English:
theorem prod_replicate
  given: (n : Nat) (a : M)
  statement: (replicate n a).prod = a ^ n
  proof: by
  simp [replicate, List.prod_replicate]

@[to_additive]

中文:
定理 prod_replicate
  条件: (n : 自然数) (a : M)
  结论: (replicate n a).乘积 = a ^ n
  证明: by
  simp [replicate, List.prod_replicate]

@[to_additive]

Depends on / 依赖: List.prod_replicate, prod_replicate, replicate
-/
theorem prod_replicate (n : Nat) (a : M) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]

@[to_additive]
/--
theorem `pow_count` / 定理 `pow_count`

English:
theorem pow_count
  given: [DecidableEq M] (a : M)
  statement: a ^ s.count a = (s.filter (Eq a)).prod
  proof: by
  rw [filter_eq]; rw [prod_replicate]

@[to_additive]

中文:
定理 pow_count
  条件: [DecidableEq M] (a : M)
  结论: a ^ s.count a = (s.filter (相等 a)).乘积
  证明: by
  rw [filter_eq]; rw [prod_replicate]

@[to_additive]

Depends on / 依赖: filter_eq, prod_replicate
-/
theorem pow_count [DecidableEq M] (a : M) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq]; rw [prod_replicate]

@[to_additive]
/--
theorem `prod_hom_rel` / 定理 `prod_hom_rel`

English:
theorem prod_hom_rel
  statement: (s : Multiset ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N}
  proof: Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]

中文:
定理 prod_hom_rel
  结论: (s : Multiset ι) {r : M -> N -> 命题} {f : ι -> M} {g : ι -> N}
  证明: Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, l.prod_hom_rel, map_coe, prod_coe, prod_hom_rel, quot_mk_to_coe
-/
theorem prod_hom_rel (s : Multiset ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N}
    (h₁ : r 1 1) (h₂ : forall ⦃a b c⦄, r b c -> r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
/--
theorem `prod_map_one` / 定理 `prod_map_one`

English:
theorem prod_map_one
  statement: prod (m.map fun _ => (1 : M)) = 1
  proof: by
  rw [map_const']; rw [prod_replicate]; rw [one_pow]

@[to_additive]

中文:
定理 prod_map_one
  结论: 乘积 (m.map fun _ => (1 : M)) = 1
  证明: by
  rw [map_const']; rw [prod_replicate]; rw [one_pow]

@[to_additive]

Depends on / 依赖: map_const, one_pow, prod_replicate
-/
theorem prod_map_one : prod (m.map fun _ => (1 : M)) = 1 := by
  rw [map_const']; rw [prod_replicate]; rw [one_pow]

@[to_additive]
/--
theorem `prod_induction` / 定理 `prod_induction`

English:
theorem prod_induction
  statement: (p : M -> Prop) (s : Multiset M) (p_mul : forall a b, p a -> p b -> p (a * b))
  proof: by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

@[to_additive]

中文:
定理 prod_induction
  结论: (p : M -> 命题) (s : Multiset M) (p_mul : 对任意 a b, p a -> p b -> p (a * b))
  证明: by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

@[to_additive]

Depends on / 依赖: foldr_induction, p_mul, p_one, prod_eq_foldr
-/
theorem prod_induction (p : M -> Prop) (s : Multiset M) (p_mul : forall a b, p a -> p b -> p (a * b))
    (p_one : p 1) (p_s : forall a in s, p a) : p s.prod := by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

@[to_additive]
/--
theorem `prod_induction_nonempty` / 定理 `prod_induction_nonempty`

English:
theorem prod_induction_nonempty
  statement: (p : M -> Prop) (p_mul : forall a b, p a -> p b -> p (a * b)) (hs : s != ∅)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : forall x, x in s -> p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_sel

中文:
定理 prod_induction_nonempty
  结论: (p : M -> 命题) (p_mul : 对任意 a b, p a -> p b -> p (a * b)) (hs : s != ∅)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : forall x, x in s -> p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_sel

Depends on / 依赖: Multiset, Multiset.induction_on, hs_empty, induction_on, mem_cons_of_mem, mem_cons_self, p_mul, prod_cons, s.prod
-/
theorem prod_induction_nonempty (p : M -> Prop) (p_mul : forall a b, p a -> p b -> p (a * b)) (hs : s != ∅)
    (p_s : forall a in s, p a) : p s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : forall x, x in s -> p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

end CommMonoid

end Multiset
