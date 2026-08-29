/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Big operators on a multiset in ordered groups with zeros

This file contains the results concerning the interaction of multiset big operators with ordered
groups with zeros.
-/

public section

namespace Multiset

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

/--
lemma `prod_nonneg` / 引理 `prod_nonneg`

English:
lemma prod_nonneg
  given: {s : Multiset R} (h : forall a in s, 0 <= a)
  statement: 0 <= s.prod
  proof: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_nonneg h

中文:
引理 prod_nonneg
  条件: {s : Multiset R} (h : 对任意 a in s, 0 <= a)
  结论: 0 <= s.prod
  证明: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_nonneg h

Depends on / 依赖: List.prod_nonneg, Quotient, Quotient.ind, mem_coe, prod_coe, prod_nonneg, quot_mk_to_coe
-/
lemma prod_nonneg {s : Multiset R} (h : forall a in s, 0 <= a) : 0 <= s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_nonneg h

/--
lemma `one_le_prod` / 引理 `one_le_prod`

English:
lemma one_le_prod
  given: {s : Multiset R} (h : forall a in s, 1 <= a)
  statement: 1 <= s.prod
  proof: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.one_le_prod h

中文:
引理 one_le_prod
  条件: {s : Multiset R} (h : 对任意 a in s, 1 <= a)
  结论: 1 <= s.prod
  证明: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.one_le_prod h

Depends on / 依赖: List.one_le_prod, Quotient, Quotient.ind, mem_coe, one_le_prod, prod_coe, quot_mk_to_coe
-/
lemma one_le_prod {s : Multiset R} (h : forall a in s, 1 <= a) : 1 <= s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.one_le_prod h

/--
theorem `prod_map_le_prod_map₀` / 定理 `prod_map_le_prod_map₀`

English:
theorem prod_map_le_prod_map₀
  statement: {ι : Type*} {s : Multiset ι} (f : ι -> R) (g : ι -> R)
  proof: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe] at *
  apply List.prod_map_le_prod_map₀ f g h0 h

中文:
定理 prod_map_le_prod_map₀
  结论: {ι : 类型} {s : Multiset ι} (f : ι -> R) (g : ι -> R)
  证明: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe] at *
  apply List.prod_map_le_prod_map₀ f g h0 h

Depends on / 依赖: List.prod_map_le_prod_map, Quotient, Quotient.ind, map_coe, mem_coe, prod_coe, quot_mk_to_coe
-/
theorem prod_map_le_prod_map₀ {ι : Type*} {s : Multiset ι} (f : ι -> R) (g : ι -> R)
    (h0 : forall i in s, 0 <= f i) (h : forall i in s, f i <= g i) :
    (map f s).prod <= (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe] at *
  apply List.prod_map_le_prod_map₀ f g h0 h

/--
theorem `prod_map_le_pow_card` / 定理 `prod_map_le_pow_card`

English:
theorem prod_map_le_pow_card
  statement: {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : Multiset L}
  proof: by
  induction t using Quotient.inductionOn
  simp_all [List.prod_map_le_pow_length₀]

中文:
定理 prod_map_le_pow_card
  结论: {F L : 类型} [FunLike F L R] {f : F} {r : R} {t : Multiset L}
  证明: by
  induction t using Quotient.inductionOn
  simp_all [List.prod_map_le_pow_length₀]

Depends on / 依赖: List.prod_map_le_pow_length, Quotient, Quotient.inductionOn, inductionOn
-/
theorem prod_map_le_pow_card {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : Multiset L}
    (hf0 : forall x in t, 0 <= f x) (hf : forall x in t, f x <= r) :
    (map f t).prod <= r ^ card t := by
  induction t using Quotient.inductionOn
  simp_all [List.prod_map_le_pow_length₀]

variable {α : Type*}

/--
lemma `prod_map_nonneg` / 引理 `prod_map_nonneg`

English:
lemma prod_map_nonneg
  given: {s : Multiset α} {f : α -> R} (h : forall a in s, 0 <= f a)
  proof: by
  refine prod_nonneg fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

中文:
引理 prod_map_nonneg
  条件: {s : Multiset α} {f : α -> R} (h : 对任意 a in s, 0 <= f a)
  证明: by
  refine prod_nonneg fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

Depends on / 依赖: mem_map, mem_map.mp, prod_nonneg
-/
lemma prod_map_nonneg {s : Multiset α} {f : α -> R} (h : forall a in s, 0 <= f a) :
    0 <= (s.map f).prod := by
  refine prod_nonneg fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

/--
lemma `one_le_prod_map` / 引理 `one_le_prod_map`

English:
lemma one_le_prod_map
  given: {s : Multiset α} {f : α -> R} (h : forall a in s, 1 <= f a)
  proof: by
  refine one_le_prod fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

omit [PosMulMono R]

中文:
引理 one_le_prod_map
  条件: {s : Multiset α} {f : α -> R} (h : 对任意 a in s, 1 <= f a)
  证明: by
  refine one_le_prod fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

omit [PosMulMono R]

Depends on / 依赖: mem_map, mem_map.mp, one_le_prod
-/
lemma one_le_prod_map {s : Multiset α} {f : α -> R} (h : forall a in s, 1 <= f a) :
    1 <= (s.map f).prod := by
  refine one_le_prod fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

omit [PosMulMono R]
variable [PosMulStrictMono R] [NeZero (1 : R)]

/--
lemma `prod_pos` / 引理 `prod_pos`

English:
lemma prod_pos
  given: {s : Multiset R} (h : forall a in s, 0 < a)
  statement: 0 < s.prod
  proof: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_pos h

中文:
引理 prod_pos
  条件: {s : Multiset R} (h : 对任意 a in s, 0 < a)
  结论: 0 < s.prod
  证明: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_pos h

Depends on / 依赖: List.prod_pos, Quotient, Quotient.ind, mem_coe, prod_coe, prod_pos, quot_mk_to_coe
-/
lemma prod_pos {s : Multiset R} (h : forall a in s, 0 < a) : 0 < s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_pos h

/--
theorem `prod_map_lt_prod_map` / 定理 `prod_map_lt_prod_map`

English:
theorem prod_map_lt_prod_map
  statement: {ι : Type*} {s : Multiset ι} (hs : s != 0)
  proof: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe, ne_eq, coe_eq_zero] at *
  apply List.prod_map_lt_prod_map hs f g h0 h

中文:
定理 prod_map_lt_prod_map
  结论: {ι : 类型} {s : Multiset ι} (hs : s != 0)
  证明: by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe, ne_eq, coe_eq_zero] at *
  apply List.prod_map_lt_prod_map hs f g h0 h

Depends on / 依赖: List.prod_map_lt_prod_map, Quotient, Quotient.ind, coe_eq_zero, map_coe, mem_coe, ne_eq, prod_coe, prod_map_lt_prod_map, quot_mk_to_coe
-/
theorem prod_map_lt_prod_map {ι : Type*} {s : Multiset ι} (hs : s != 0)
    (f : ι -> R) (g : ι -> R) (h0 : forall i in s, 0 < f i) (h : forall i in s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe, ne_eq, coe_eq_zero] at *
  apply List.prod_map_lt_prod_map hs f g h0 h

end Multiset
