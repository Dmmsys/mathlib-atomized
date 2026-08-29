/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.Group.Defs
public import Batteries.Data.List.Lemmas

/-!
# Sums and products from lists

This file provides basic definitions for `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/

@[expose] public section

variable {ι M N : Type*}

namespace List
section Defs

attribute [to_additive existing] prod prod_nil prod_cons prod_one_cons prod_append prod_concat
  prod_flatten prod_eq_foldl

/--
Definition of `alternatingSum` / `alternatingSum` 的定义

English:
definition alternatingSum
  signature: {G : Type*} [Zero G] [Add G] [Neg G]

中文:
定义 alternatingSum
  签名: {G : 类型} [Zero G] [Add G] [Neg G]
-/
def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G -> G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t

/-- The alternating product of a list. -/
@[to_additive existing]
/--
Definition of `alternatingProd` / `alternatingProd` 的定义

English:
definition alternatingProd
  signature: {G : Type*} [One G] [Mul G] [Inv G]

中文:
定义 alternatingProd
  签名: {G : 类型} [One G] [Mul G] [Inv G]
-/
def alternatingProd {G : Type*} [One G] [Mul G] [Inv G] : List G -> G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternatingProd t

end Defs

section Mul

variable [Mul M] [One M] {a : M} {l : List M}

@[to_additive]
/--
lemma `prod_induction` / 引理 `prod_induction`

English:
lemma prod_induction
  proof: by
  induction l with
  | nil => simpa
  | cons a l ih =>
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih base.2)

中文:
引理 prod_induction
  证明: by
  induction l with
  | nil => simpa
  | cons a l ih =>
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih base.2)

Depends on / 依赖: List.prod_cons, forall_eq_or_imp, mem_cons, prod_cons
-/
lemma prod_induction
    (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (base : forall x in l, p x) :
    p l.prod := by
  induction l with
  | nil => simpa
  | cons a l ih =>
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih base.2)

end Mul

section MulOneClass

variable [MulOneClass M] {l : List M} {a : M}

@[to_additive]
/--
theorem `prod_map_one` / 定理 `prod_map_one`

English:
theorem prod_map_one
  given: {l : List ι}
  proof: by
  induction l with simp [*]

@[to_additive]

中文:
定理 prod_map_one
  条件: {l : List ι}
  证明: by
  induction l with simp [*]

@[to_additive]
-/
theorem prod_map_one {l : List ι} :
    (l.map fun _ => (1 : M)).prod = 1 := by
  induction l with simp [*]

@[to_additive]
/--
lemma `prod_induction_nonempty` / 引理 `prod_induction_nonempty`

English:
lemma prod_induction_nonempty
  proof: by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases hl_empty : l = []
    · simp [*]
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih hl_empty base.2)

中文:
引理 prod_induction_nonempty
  证明: by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases hl_empty : l = []
    · simp [*]
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih hl_empty base.2)

Depends on / 依赖: List.prod_cons, forall_eq_or_imp, hl_empty, mem_cons, prod_cons
-/
lemma prod_induction_nonempty
    (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (hl : l != []) (base : forall x in l, p x) :
    p l.prod := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases hl_empty : l = []
    · simp [*]
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih hl_empty base.2)

end MulOneClass

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
/--
theorem `prod_replicate` / 定理 `prod_replicate`

English:
theorem prod_replicate
  given: (n : Nat) (a : M)
  statement: (replicate n a).prod = a ^ n
  proof: by
  induction n with
  | zero => rw [pow_zero, replicate_zero, prod_nil]
  | succ n ih => rw [replicate_succ, prod_cons, ih, pow_succ']

@[to_additive sum_eq_card_nsmul]

中文:
定理 prod_replicate
  条件: (n : 自然数) (a : M)
  结论: (replicate n a).prod = a ^ n
  证明: by
  induction n with
  | zero => rw [pow_zero, replicate_zero, prod_nil]
  | succ n ih => rw [replicate_succ, prod_cons, ih, pow_succ']

@[to_additive sum_eq_card_nsmul]

Depends on / 依赖: pow_succ, pow_zero, prod_cons, prod_nil, replicate_succ, replicate_zero
-/
theorem prod_replicate (n : Nat) (a : M) : (replicate n a).prod = a ^ n := by
  induction n with
  | zero => rw [pow_zero, replicate_zero, prod_nil]
  | succ n ih => rw [replicate_succ, prod_cons, ih, pow_succ']

@[to_additive sum_eq_card_nsmul]
/--
theorem `prod_eq_pow_card` / 定理 `prod_eq_pow_card`

English:
theorem prod_eq_pow_card
  given: (l : List M) (m : M) (h : forall x in l, x = m)
  statement: l.prod = m ^ l.length
  proof: by
  rw [← prod_replicate]; rw [← List.eq_replicate_iff.mpr ⟨rfl]; rw [h⟩]

@[to_additive]

中文:
定理 prod_eq_pow_card
  条件: (l : List M) (m : M) (h : 对任意 x in l, x = m)
  结论: l.prod = m ^ l.length
  证明: by
  rw [← prod_replicate]; rw [← List.eq_replicate_iff.mpr ⟨rfl]; rw [h⟩]

@[to_additive]

Depends on / 依赖: List.eq_replicate_iff.mpr, eq_replicate_iff, prod_replicate
-/
theorem prod_eq_pow_card (l : List M) (m : M) (h : forall x in l, x = m) : l.prod = m ^ l.length := by
  rw [← prod_replicate]; rw [← List.eq_replicate_iff.mpr ⟨rfl]; rw [h⟩]

@[to_additive]
/--
theorem `prod_hom_rel` / 定理 `prod_hom_rel`

English:
theorem prod_hom_rel
  statement: (l : List ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N} (h₁ : r 1 1)
  proof: List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]

中文:
定理 prod_hom_rel
  结论: (l : List ι) {r : M -> N -> 命题} {f : ι -> M} {g : ι -> N} (h₁ : r 1 1)
  证明: List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]

Depends on / 依赖: List.recOn, map_cons, prod_cons
-/
theorem prod_hom_rel (l : List ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N} (h₁ : r 1 1)
    (h₂ : forall ⦃i a b⦄, r a b -> r (f i * a) (g i * b)) : r (l.map f).prod (l.map g).prod :=
  List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]

end Monoid

end List
