/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.FunLike.Basic

/-!
# Big operators on a list in ordered groups with zeros

This file contains the results concerning the interaction of list big operators with ordered
groups with zeros.
-/

public section

namespace List
variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

/--
lemma `prod_nonneg` / 引理 `prod_nonneg`

English:
lemma prod_nonneg
  given: {s : List R} (h : forall a in s, 0 <= a)
  statement: 0 <= s.prod
  proof: by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_nonneg h.1 (hind h.2)

中文:
引理 prod_nonneg
  条件: {s : List R} (h : 对任意 a in s, 0 <= a)
  结论: 0 <= s.prod
  证明: by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_nonneg h.1 (hind h.2)

Depends on / 依赖: forall_eq_or_imp, mem_cons, mul_nonneg, prod_cons
-/
lemma prod_nonneg {s : List R} (h : forall a in s, 0 <= a) : 0 <= s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_nonneg h.1 (hind h.2)


/--
lemma `one_le_prod` / 引理 `one_le_prod`

English:
lemma one_le_prod
  given: {s : List R} (h : forall a in s, 1 <= a)
  statement: 1 <= s.prod
  proof: by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

中文:
引理 one_le_prod
  条件: {s : List R} (h : 对任意 a in s, 1 <= a)
  结论: 1 <= s.prod
  证明: by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

Depends on / 依赖: forall_eq_or_imp, mem_cons, one_le_mul_of_one_le_of_one_le, prod_cons
-/
lemma one_le_prod {s : List R} (h : forall a in s, 1 <= a) : 1 <= s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

/--
theorem `prod_map_le_prod_map₀` / 定理 `prod_map_le_prod_map₀`

English:
theorem prod_map_le_prod_map₀
  statement: {ι : Type*} {s : List ι} (f : ι -> R) (g : ι -> R)
  proof: by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · grind
    · grind [prod_nonneg]
    · apply (h0 _ _).trans (h _ _) <;> simp only [mem_cons, true_o

中文:
定理 prod_map_le_prod_map₀
  结论: {ι : 类型} {s : List ι} (f : ι -> R) (g : ι -> R)
  证明: by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · grind
    · grind [prod_nonneg]
    · apply (h0 _ _).trans (h _ _) <;> simp only [mem_cons, true_o

Depends on / 依赖: PosMulMono, map_cons, mem_cons, mul_le_mul, posMulMono_iff_mulPosMono, prod_cons, prod_nonneg, true_or
-/
theorem prod_map_le_prod_map₀ {ι : Type*} {s : List ι} (f : ι -> R) (g : ι -> R)
    (h0 : forall i in s, 0 <= f i) (h : forall i in s, f i <= g i) :
    (map f s).prod <= (map g s).prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · grind
    · grind [prod_nonneg]
    · apply (h0 _ _).trans (h _ _) <;> simp only [mem_cons, true_or]

/--
theorem `prod_map_le_pow_length₀` / 定理 `prod_map_le_pow_length₀`

English:
theorem prod_map_le_pow_length₀
  statement: {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : List L}
  proof: by
  convert! prod_map_le_prod_map₀ f (Function.const L r) hf0 hf
  simp [map_const, prod_replicate]

omit [PosMulMono R]

中文:
定理 prod_map_le_pow_length₀
  结论: {F L : 类型} [FunLike F L R] {f : F} {r : R} {t : List L}
  证明: by
  convert! prod_map_le_prod_map₀ f (Function.const L r) hf0 hf
  simp [map_const, prod_replicate]

omit [PosMulMono R]

Depends on / 依赖: Function, Function.const, convert, map_const, prod_replicate
-/
theorem prod_map_le_pow_length₀ {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : List L}
    (hf0 : forall x in t, 0 <= f x) (hf : forall x in t, f x <= r) :
    (map f t).prod <= r ^ length t := by
  convert! prod_map_le_prod_map₀ f (Function.const L r) hf0 hf
  simp [map_const, prod_replicate]

omit [PosMulMono R]
variable [PosMulStrictMono R] [NeZero (1 : R)]

/--
lemma `prod_pos` / 引理 `prod_pos`

English:
lemma prod_pos
  given: {s : List R} (h : forall a in s, 0 < a)
  statement: 0 < s.prod
  proof: by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)

中文:
引理 prod_pos
  条件: {s : List R} (h : 对任意 a in s, 0 < a)
  结论: 0 < s.prod
  证明: by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)

Depends on / 依赖: forall_eq_or_imp, mem_cons, mul_pos, prod_cons
-/
lemma prod_pos {s : List R} (h : forall a in s, 0 < a) : 0 < s.prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)

/--
theorem `prod_map_lt_prod_map` / 定理 `prod_map_lt_prod_map`

English:
theorem prod_map_lt_prod_map
  statement: {ι : Type*} {s : List ι} (hs : s != [])
  proof: by
  match s with
  | [] => contradiction
  | a :: s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    apply mul_lt_mul
    · apply h
      simp
    · apply prod_map_le_prod_map₀
      · intro i hi
        apply le_of_lt
        apply

中文:
定理 prod_map_lt_prod_map
  结论: {ι : 类型} {s : List ι} (hs : s != [])
  证明: by
  match s with
  | [] => contradiction
  | a :: s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    apply mul_lt_mul
    · apply h
      simp
    · apply prod_map_le_prod_map₀
      · intro i hi
        apply le_of_lt
        apply

Depends on / 依赖: PosMulStrictMono, le_of_lt, map_cons, mul_lt_mul, posMulStrictMono_iff_mulPosStrictMono, prod_cons, prod_pos
-/
theorem prod_map_lt_prod_map {ι : Type*} {s : List ι} (hs : s != [])
    (f : ι -> R) (g : ι -> R) (h0 : forall i in s, 0 < f i) (h : forall i in s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  match s with
  | [] => contradiction
  | a :: s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    apply mul_lt_mul
    · apply h
      simp
    · apply prod_map_le_prod_map₀
      · intro i hi
        apply le_of_lt
        apply h0
        simp [hi]
      · intro i hi
        apply le_of_lt
        apply h
        simp [hi]
    · apply prod_pos
      grind
    · apply le_of_lt ((h0 _ _).trans (h _ _)) <;> simp

end List
