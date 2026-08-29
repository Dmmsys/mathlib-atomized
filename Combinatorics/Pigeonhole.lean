/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Pigeonhole principles

Given pigeons (possibly infinitely many) in pigeonholes, the
pigeonhole principle states that, if there are more pigeons than
pigeonholes, then there is a pigeonhole with two or more pigeons.

There are a few variations on this statement, and the conclusion can
be made stronger depending on how many pigeons you know you might
have.

The basic statements of the pigeonhole principle appear in the
following locations:

* `Data.Finset.Basic` has `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
* `Data.Fintype.Basic` has `Fintype.exists_ne_map_eq_of_card_lt`
* `Data.Fintype.Basic` has `Finite.exists_ne_map_eq_of_infinite`
* `Data.Fintype.Basic` has `Finite.exists_infinite_fiber`
* `Data.Set.Finite` has `Set.infinite.exists_ne_map_eq_of_mapsTo`

This module gives access to these pigeonhole principles along with 20 more.
The versions vary by:

* using a function between `Fintype`s or a function between possibly infinite types restricted to
  `Finset`s;
* counting pigeons by a general weight function (`∑ x ∈ s, w x`) or by heads (`#s`);
* using strict or non-strict inequalities;
* establishing upper or lower estimate on the number (or the total weight) of the pigeons in one
  pigeonhole;
* in case when we count pigeons by some weight function `w` and consider a function `f` between
  `Finset`s `s` and `t`, we can either assume that each pigeon is in one of the pigeonholes
  (`∀ x ∈ s, f x ∈ t`), or assume that for `y ∉ t`, the total weight of the pigeons in this
  pigeonhole `∑ x ∈ s with f x = y, w x` is nonpositive or nonnegative depending on
  the inequality we are proving.
* in the case where the "holes" are not necessarily disjoint, that is, a pigeon could be in multiple
  holes at the same time, a set-valued version is provided.

Lemma names follow `mathlib` convention (e.g.,
`Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`); "pigeonhole principle" is mentioned in the
docstrings instead of the names.

## See also

* `Ordinal.infinite_pigeonhole`: pigeonhole principle for cardinals, formulated using cofinality;

* `MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure`,
  `MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`: pigeonhole principle in a
  measure space.

## Tags

pigeonhole principle
-/

public section


universe u v w

variable {α : Type u} {β : Type v} {M : Type w} [DecidableEq β]

open Nat

namespace Finset

variable {s : Finset α} {t : Finset β} {f : α -> β} {w : α -> M} {b : M} {n : Nat}

/-!
### The pigeonhole principles on `Finset`s, pigeons counted by weight

In this section we prove the following version of the pigeonhole principle: if the total weight of a
finite set of pigeons is greater than `n • b`, and they are sorted into `n` pigeonholes, then for
some pigeonhole, the total weight of the pigeons in this pigeonhole is greater than `b`, and a few
variations of this theorem.

The principle is formalized in the following way, see
`Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`: if `f : α → β` is a function which maps all
elements of `s : Finset α` to `t : Finset β` and `#t • b < ∑ x ∈ s, w x`, where `w : α → M` is
a weight function taking values in a linearly ordered cancellative monoid, then for
some `y ∈ t`, the sum of the weights of all `x ∈ s` such that `f x = y` is greater than `b`.

There are a few bits we can change in this theorem:

* reverse all inequalities, with obvious adjustments to the name;
* replace the assumption `∀ a ∈ s, f a ∈ t` with `∀ y ∉ t, ∑ x ∈ s with f x = y, w x ≤ 0`,
  and replace `of_maps_to` with `of_sum_fiber_nonpos` in the name;
* use non-strict inequalities assuming `t` is nonempty.

We can do all these variations independently, so we have eight versions of the theorem.
-/

section

variable [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-!
#### Strict inequality versions
-/


/--
theorem `exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum` / 定理 `exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`

English:
theorem exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum
  statement: (hf : forall a in s, f a in t)
  proof: exists_lt_of_sum_lt by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

中文:
定理 存在_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum
  结论: (hf : 对任意 a in s, f a in t)
  证明: exists_lt_of_sum_lt by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

Depends on / 依赖: exists_lt_of_sum_lt, sum_const, sum_fiberwise_of_maps_to
-/
theorem exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (hf : forall a in s, f a in t)
    (hb : #t • b < ∑ x in s, w x) : exists y in t, b < ∑ x in s with f x = y, w x :=
exists_lt_of_sum_lt by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

/--
theorem `exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul` / 定理 `exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul`

English:
theorem exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul
  statement: (hf : forall a in s, f a in t)
  proof: exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (M := Mᵒᵈ) hf hb

中文:
定理 存在_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul
  结论: (hf : 对任意 a in s, f a in t)
  证明: exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (M := Mᵒᵈ) hf hb

Depends on / 依赖: exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum
-/
theorem exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul (hf : forall a in s, f a in t)
    (hb : ∑ x in s, w x < #t • b) : exists y in t, ∑ x in s with f x = y, w x < b :=
  exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (M := Mᵒᵈ) hf hb

/--
theorem `exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum` / 定理 `exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum`

English:
theorem exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
  proof: exists_lt_of_sum_lt
    calc
      ∑ _y in t, b < ∑ x in s, w x := by simpa
      _ <= ∑ y in t, ∑ x in s with f x = y, w x := sum_le_sum_fiberwise_of_sum_fiber_nonpos ht

中文:
定理 存在_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
  证明: exists_lt_of_sum_lt
    calc
      ∑ _y in t, b < ∑ x in s, w x := by simpa
      _ <= ∑ y in t, ∑ x in s with f x = y, w x := sum_le_sum_fiberwise_of_sum_fiber_nonpos ht

Depends on / 依赖: exists_lt_of_sum_lt, sum_le_sum_fiberwise_of_sum_fiber_nonpos
-/
theorem exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
    (ht : forall y ∉ t, ∑ x in s with f x = y, w x <= 0)
    (hb : #t • b < ∑ x in s, w x) : exists y in t, b < ∑ x in s with f x = y, w x :=
exists_lt_of_sum_lt
    calc
      ∑ _y in t, b < ∑ x in s, w x := by simpa
      _ <= ∑ y in t, ∑ x in s with f x = y, w x := sum_le_sum_fiberwise_of_sum_fiber_nonpos ht

/--
theorem `exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul` / 定理 `exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul`

English:
theorem exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
  proof: exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum (M := Mᵒᵈ) ht hb

中文:
定理 存在_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
  证明: exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum (M := Mᵒᵈ) ht hb

Depends on / 依赖: exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
-/
theorem exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
    (ht : forall y ∉ t, (0 : M) <= ∑ x in s with f x = y, w x) (hb : ∑ x in s, w x < #t • b) :
    exists y in t, ∑ x in s with f x = y, w x < b :=
  exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum (M := Mᵒᵈ) ht hb

/-!
#### Non-strict inequality versions
-/


/--
theorem `exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum` / 定理 `exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum`

English:
theorem exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
  statement: (hf : forall a in s, f a in t) (ht : t.Nonempty)
  proof: exists_le_of_sum_le ht by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

中文:
定理 存在_le_sum_fiber_of_maps_to_of_nsmul_le_sum
  结论: (hf : 对任意 a in s, f a in t) (ht : t.非空)
  证明: exists_le_of_sum_le ht by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

Depends on / 依赖: Equiv.ulift.symm, exists_le_of_sum_le, of_equiv, sum_const, sum_fiberwise_of_maps_to
-/
theorem exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (hf : forall a in s, f a in t) (ht : t.Nonempty)
    (hb : #t • b <= ∑ x in s, w x) : exists y in t, b <= ∑ x in s with f x = y, w x :=
exists_le_of_sum_le ht by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

/--
theorem `exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul` / 定理 `exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul`

English:
theorem exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul
  statement: (hf : forall a in s, f a in t) (ht : t.Nonempty)
  proof: exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb

中文:
定理 存在_sum_fiber_le_of_maps_to_of_sum_le_nsmul
  结论: (hf : 对任意 a in s, f a in t) (ht : t.非空)
  证明: exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb

Depends on / 依赖: exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
-/
theorem exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul (hf : forall a in s, f a in t) (ht : t.Nonempty)
    (hb : ∑ x in s, w x <= #t • b) : exists y in t, ∑ x in s with f x = y, w x <= b :=
  exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb

/--
theorem `exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum` / 定理 `exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum`

English:
theorem exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
  proof: exists_le_of_sum_le ht
    calc
      ∑ _y in t, b <= ∑ x in s, w x := by simpa
      _ <= ∑ y in t, ∑ x in s with f x = y, w x :=
        sum_le_sum_fiberwise_of_sum_fiber_nonpos hf

中文:
定理 存在_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
  证明: exists_le_of_sum_le ht
    calc
      ∑ _y in t, b <= ∑ x in s, w x := by simpa
      _ <= ∑ y in t, ∑ x in s with f x = y, w x :=
        sum_le_sum_fiberwise_of_sum_fiber_nonpos hf

Depends on / 依赖: Infinite, Uncountable, exists_le_of_sum_le, sum_le_sum_fiberwise_of_sum_fiber_nonpos
-/
theorem exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
    (hf : forall y ∉ t, ∑ x in s with f x = y, w x <= 0) (ht : t.Nonempty)
    (hb : #t • b <= ∑ x in s, w x) : exists y in t, b <= ∑ x in s with f x = y, w x :=
exists_le_of_sum_le ht
    calc
      ∑ _y in t, b <= ∑ x in s, w x := by simpa
      _ <= ∑ y in t, ∑ x in s with f x = y, w x :=
        sum_le_sum_fiberwise_of_sum_fiber_nonpos hf

/--
theorem `exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul` / 定理 `exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul`

English:
theorem exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
  proof: exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb

中文:
定理 存在_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
  证明: exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb

Depends on / 依赖: Countable, Countable.toSmall, exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum, toSmall
-/
theorem exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
    (hf : forall y ∉ t, (0 : M) <= ∑ x in s with f x = y, w x) (ht : t.Nonempty)
    (hb : ∑ x in s, w x <= #t • b) : exists y in t, ∑ x in s with f x = y, w x <= b :=
  exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb

end

variable [CommSemiring M] [LinearOrder M] [IsStrictOrderedRing M]

/-!
### The pigeonhole principles on `Finset`s, pigeons counted by heads

In this section we formalize a few versions of the following pigeonhole principle: there is a
pigeonhole with at least as many pigeons as the ceiling of the average number of pigeons across all
pigeonholes.

First, we can use strict or non-strict inequalities. While the versions with non-strict inequalities
are weaker than those with strict inequalities, sometimes it might be more convenient to apply the
weaker version. Second, we can either state that there exists a pigeonhole with at least `n`
pigeons, or state that there exists a pigeonhole with at most `n` pigeons. In the latter case we do
not need the assumption `∀ a ∈ s, f a ∈ t`.

So, we prove four theorems: `Finset.exists_lt_card_fiber_of_maps_to_of_mul_lt_card`,
`Finset.exists_le_card_fiber_of_maps_to_of_mul_le_card`,
`Finset.exists_card_fiber_lt_of_card_lt_mul`, and `Finset.exists_card_fiber_le_of_card_le_mul`. -/


/--
theorem `exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to` / 定理 `exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to`

English:
theorem exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
  statement: (hf : forall a in s, f a in t)
  proof: by
  simp_rw [cast_card] at ht ⊢
  exact exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf ht

中文:
定理 存在_lt_card_fiber_of_nsmul_lt_card_of_maps_to
  结论: (hf : 对任意 a in s, f a in t)
  证明: by
  simp_rw [cast_card] at ht ⊢
  exact exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf ht

Depends on / 依赖: cast_card, exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum, simp_rw
-/
theorem exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (hf : forall a in s, f a in t)
    (ht : #t • b < #s) : exists y in t, b < #{x in s | f x = y} := by
  simp_rw [cast_card] at ht ⊢
  exact exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf ht

/--
theorem `exists_lt_card_fiber_of_mul_lt_card_of_maps_to` / 定理 `exists_lt_card_fiber_of_mul_lt_card_of_maps_to`

English:
theorem exists_lt_card_fiber_of_mul_lt_card_of_maps_to
  statement: (hf : forall a in s, f a in t)
  proof: exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to hf hn

中文:
定理 存在_lt_card_fiber_of_mul_lt_card_of_maps_to
  结论: (hf : 对任意 a in s, f a in t)
  证明: exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to hf hn

Depends on / 依赖: exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
-/
theorem exists_lt_card_fiber_of_mul_lt_card_of_maps_to (hf : forall a in s, f a in t)
    (hn : #t * n < #s) : exists y in t, n < #{x in s | f x = y} :=
  exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to hf hn

/--
theorem `exists_card_fiber_lt_of_card_lt_nsmul` / 定理 `exists_card_fiber_lt_of_card_lt_nsmul`

English:
theorem exists_card_fiber_lt_of_card_lt_nsmul
  given: (ht : #s < #t • b)
  proof: by
  simp_rw [cast_card] at ht ⊢
  exact
    exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht

中文:
定理 存在_card_fiber_lt_of_card_lt_nsmul
  条件: (ht : #s < #t • b)
  证明: by
  simp_rw [cast_card] at ht ⊢
  exact
    exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht

Depends on / 依赖: cast_card, exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul, simp_rw, sum_nonneg, zero_le_one
-/
theorem exists_card_fiber_lt_of_card_lt_nsmul (ht : #s < #t • b) :
    exists y in t, #{x in s | f x = y} < b := by
  simp_rw [cast_card] at ht ⊢
  exact
    exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht

/--
theorem `exists_card_fiber_lt_of_card_lt_mul` / 定理 `exists_card_fiber_lt_of_card_lt_mul`

English:
theorem exists_card_fiber_lt_of_card_lt_mul
  given: (hn : #s < #t * n)
  statement: exists y in t, #{x in s | f x = y} < n
  proof: exists_card_fiber_lt_of_card_lt_nsmul hn

中文:
定理 存在_card_fiber_lt_of_card_lt_mul
  条件: (hn : #s < #t * n)
  结论: 存在 y in t, #{x in s | f x = y} < n
  证明: exists_card_fiber_lt_of_card_lt_nsmul hn

Depends on / 依赖: exists_card_fiber_lt_of_card_lt_nsmul
-/
theorem exists_card_fiber_lt_of_card_lt_mul (hn : #s < #t * n) : exists y in t, #{x in s | f x = y} < n :=
  exists_card_fiber_lt_of_card_lt_nsmul hn

/--
theorem `exists_le_card_fiber_of_nsmul_le_card_of_maps_to` / 定理 `exists_le_card_fiber_of_nsmul_le_card_of_maps_to`

English:
theorem exists_le_card_fiber_of_nsmul_le_card_of_maps_to
  statement: (hf : forall a in s, f a in t) (ht : t.Nonempty)
  proof: by
  simp_rw [cast_card] at hb ⊢
  exact exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht hb

中文:
定理 存在_le_card_fiber_of_nsmul_le_card_of_maps_to
  结论: (hf : 对任意 a in s, f a in t) (ht : t.非空)
  证明: by
  simp_rw [cast_card] at hb ⊢
  exact exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht hb

Depends on / 依赖: cast_card, exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum, simp_rw
-/
theorem exists_le_card_fiber_of_nsmul_le_card_of_maps_to (hf : forall a in s, f a in t) (ht : t.Nonempty)
    (hb : #t • b <= #s) : exists y in t, b <= #{x in s | f x = y} := by
  simp_rw [cast_card] at hb ⊢
  exact exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht hb

/--
theorem `exists_le_card_fiber_of_mul_le_card_of_maps_to` / 定理 `exists_le_card_fiber_of_mul_le_card_of_maps_to`

English:
theorem exists_le_card_fiber_of_mul_le_card_of_maps_to
  statement: (hf : forall a in s, f a in t) (ht : t.Nonempty)
  proof: exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht hn

中文:
定理 存在_le_card_fiber_of_mul_le_card_of_maps_to
  结论: (hf : 对任意 a in s, f a in t) (ht : t.非空)
  证明: exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht hn

Depends on / 依赖: exists_le_card_fiber_of_nsmul_le_card_of_maps_to
-/
theorem exists_le_card_fiber_of_mul_le_card_of_maps_to (hf : forall a in s, f a in t) (ht : t.Nonempty)
    (hn : #t * n <= #s) : exists y in t, n <= #{x in s | f x = y} :=
  exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht hn

/--
theorem `exists_card_fiber_le_of_card_le_nsmul` / 定理 `exists_card_fiber_le_of_card_le_nsmul`

English:
theorem exists_card_fiber_le_of_card_le_nsmul
  given: (ht : t.Nonempty) (hb : #s <= #t • b)
  proof: by
  simp_rw [cast_card] at hb ⊢
  refine
    exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht hb

中文:
定理 存在_card_fiber_le_of_card_le_nsmul
  条件: (ht : t.非空) (hb : #s <= #t • b)
  证明: by
  simp_rw [cast_card] at hb ⊢
  refine
    exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht hb

Depends on / 依赖: cast_card, exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul, simp_rw, sum_nonneg, zero_le_one
-/
theorem exists_card_fiber_le_of_card_le_nsmul (ht : t.Nonempty) (hb : #s <= #t • b) :
    exists y in t, #{x in s | f x = y} <= b := by
  simp_rw [cast_card] at hb ⊢
  refine
    exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht hb

/--
theorem `exists_card_fiber_le_of_card_le_mul` / 定理 `exists_card_fiber_le_of_card_le_mul`

English:
theorem exists_card_fiber_le_of_card_le_mul
  given: (ht : t.Nonempty) (hn : #s <= #t * n)
  proof: exists_card_fiber_le_of_card_le_nsmul ht hn

中文:
定理 存在_card_fiber_le_of_card_le_mul
  条件: (ht : t.非空) (hn : #s <= #t * n)
  证明: exists_card_fiber_le_of_card_le_nsmul ht hn

Depends on / 依赖: exists_card_fiber_le_of_card_le_nsmul
-/
theorem exists_card_fiber_le_of_card_le_mul (ht : t.Nonempty) (hn : #s <= #t * n) :
    exists y in t, #{x in s | f x = y} <= n :=
  exists_card_fiber_le_of_card_le_nsmul ht hn

/--
lemma `exists_mem_exists_mem_inf'_card_lt` / 引理 `exists_mem_exists_mem_inf'_card_lt`

English:
lemma exists_mem_exists_mem_inf'_card_lt
  statement: [DecidableEq α] [Fintype α] {f : α -> Finset β}
  proof: by
  set k := s.inf' h₁ (fun j => #(f j)) with hk
  contrapose! h₃
  suffices #s • k <= #(s.biUnion f) • k by simp_all
  simp only [← Finset.sum_const]
  calc ∑ j in s, k
    _ <= ∑ j in s, #(f j) := by gcongr with i hi; exact inf'_le _ hi
    _ = ∑ x in s.biUnion f, #{j | j in s ∧ x in f j} := by rw [sum_card_eq_sum_biUnion_card]
    _ <= ∑ x in s.biUnion f, k := by gcongr; grind

中文:
引理 存在_mem_存在_mem_inf'_card_lt
  结论: [DecidableEq α] [有限类型 α] {f : α -> 有限集 β}
  证明: by
  set k := s.inf' h₁ (fun j => #(f j)) with hk
  contrapose! h₃
  suffices #s • k <= #(s.biUnion f) • k by simp_all
  simp only [← Finset.sum_const]
  calc ∑ j in s, k
    _ <= ∑ j in s, #(f j) := by gcongr with i hi; exact inf'_le _ hi
    _ = ∑ x in s.biUnion f, #{j | j in s ∧ x in f j} := by rw [sum_card_eq_sum_biUnion_card]
    _ <= ∑ x in s.biUnion f, k := by gcongr; grind

Depends on / 依赖: Finset, Finset.sum_const, biUnion, contrapose, s.biUnion, s.inf, sum_card_eq_sum_biUnion_card, sum_const
-/
lemma exists_mem_exists_mem_inf'_card_lt [DecidableEq α] [Fintype α] {f : α -> Finset β}
    (h₁ : s.Nonempty) (h₂ : forall j in s, 0 < #(f j)) (h₃ : #(s.biUnion f) < #s) :
    exists a in s, exists x in f a, (s.inf' h₁ fun j => #(f j)) < #{j | j in s ∧ x in f j} := by
  set k := s.inf' h₁ (fun j => #(f j)) with hk
  contrapose! h₃
  suffices #s • k <= #(s.biUnion f) • k by simp_all
  simp only [← Finset.sum_const]
  calc ∑ j in s, k
    _ <= ∑ j in s, #(f j) := by gcongr with i hi; exact inf'_le _ hi
    _ = ∑ x in s.biUnion f, #{j | j in s ∧ x in f j} := by rw [sum_card_eq_sum_biUnion_card]
    _ <= ∑ x in s.biUnion f, k := by gcongr; grind

end Finset

namespace Fintype

open Finset

variable [Fintype α] [Fintype β] (f : α -> β) {w : α -> M} {b : M} {n : Nat}

section

variable [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-!
### The pigeonhole principles on `Fintypes`s, pigeons counted by weight

In this section we specialize theorems from the previous section to the special case of functions
between `Fintype`s and `s = univ`, `t = univ`. In this case the assumption `∀ x ∈ s, f x ∈ t` always
holds, so we have four theorems instead of eight. -/


/--
theorem `exists_lt_sum_fiber_of_nsmul_lt_sum` / 定理 `exists_lt_sum_fiber_of_nsmul_lt_sum`

English:
theorem exists_lt_sum_fiber_of_nsmul_lt_sum
  given: (hb : card β • b < ∑ x, w x)
  proof: let ⟨y, _, hy⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (fun _ _ => mem_univ _) hb
  ⟨y, hy⟩

中文:
定理 存在_lt_sum_fiber_of_nsmul_lt_sum
  条件: (hb : card β • b < ∑ x, w x)
  证明: let ⟨y, _, hy⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (fun _ _ => mem_univ _) hb
  ⟨y, hy⟩

Depends on / 依赖: exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum, mem_univ
-/
theorem exists_lt_sum_fiber_of_nsmul_lt_sum (hb : card β • b < ∑ x, w x) :
    exists y, b < ∑ x with f x = y, w x :=
  let ⟨y, _, hy⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (fun _ _ => mem_univ _) hb
  ⟨y, hy⟩

/--
theorem `exists_le_sum_fiber_of_nsmul_le_sum` / 定理 `exists_le_sum_fiber_of_nsmul_le_sum`

English:
theorem exists_le_sum_fiber_of_nsmul_le_sum
  given: [Nonempty β] (hb : card β • b <= ∑ x, w x)
  proof: let ⟨y, _, hy⟩ :=
    exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, hy⟩

中文:
定理 存在_le_sum_fiber_of_nsmul_le_sum
  条件: [非空 β] (hb : card β • b <= ∑ x, w x)
  证明: let ⟨y, _, hy⟩ :=
    exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, hy⟩

Depends on / 依赖: exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum, mem_univ, univ_nonempty
-/
theorem exists_le_sum_fiber_of_nsmul_le_sum [Nonempty β] (hb : card β • b <= ∑ x, w x) :
    exists y, b <= ∑ x with f x = y, w x :=
  let ⟨y, _, hy⟩ :=
    exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, hy⟩

/--
theorem `exists_sum_fiber_lt_of_sum_lt_nsmul` / 定理 `exists_sum_fiber_lt_of_sum_lt_nsmul`

English:
theorem exists_sum_fiber_lt_of_sum_lt_nsmul
  given: (hb : ∑ x, w x < card β • b)
  proof: exists_lt_sum_fiber_of_nsmul_lt_sum (M := Mᵒᵈ) _ hb

中文:
定理 存在_sum_fiber_lt_of_sum_lt_nsmul
  条件: (hb : ∑ x, w x < card β • b)
  证明: exists_lt_sum_fiber_of_nsmul_lt_sum (M := Mᵒᵈ) _ hb

Depends on / 依赖: exists_lt_sum_fiber_of_nsmul_lt_sum
-/
theorem exists_sum_fiber_lt_of_sum_lt_nsmul (hb : ∑ x, w x < card β • b) :
    exists y, ∑ x with f x = y, w x < b :=
  exists_lt_sum_fiber_of_nsmul_lt_sum (M := Mᵒᵈ) _ hb

/--
theorem `exists_sum_fiber_le_of_sum_le_nsmul` / 定理 `exists_sum_fiber_le_of_sum_le_nsmul`

English:
theorem exists_sum_fiber_le_of_sum_le_nsmul
  given: [Nonempty β] (hb : ∑ x, w x <= card β • b)
  proof: exists_le_sum_fiber_of_nsmul_le_sum (M := Mᵒᵈ) _ hb

中文:
定理 存在_sum_fiber_le_of_sum_le_nsmul
  条件: [非空 β] (hb : ∑ x, w x <= card β • b)
  证明: exists_le_sum_fiber_of_nsmul_le_sum (M := Mᵒᵈ) _ hb

Depends on / 依赖: exists_le_sum_fiber_of_nsmul_le_sum
-/
theorem exists_sum_fiber_le_of_sum_le_nsmul [Nonempty β] (hb : ∑ x, w x <= card β • b) :
    exists y, ∑ x with f x = y, w x <= b :=
  exists_le_sum_fiber_of_nsmul_le_sum (M := Mᵒᵈ) _ hb

end

variable [CommSemiring M] [LinearOrder M] [IsStrictOrderedRing M]

/--
theorem `exists_lt_card_fiber_of_nsmul_lt_card` / 定理 `exists_lt_card_fiber_of_nsmul_lt_card`

English:
theorem exists_lt_card_fiber_of_nsmul_lt_card
  given: (hb : card β • b < card α)
  proof: let ⟨y, _, h⟩ := exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (fun _ _ => mem_univ _) hb
  ⟨y, h⟩

中文:
定理 存在_lt_card_fiber_of_nsmul_lt_card
  条件: (hb : card β • b < card α)
  证明: let ⟨y, _, h⟩ := exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (fun _ _ => mem_univ _) hb
  ⟨y, h⟩

Depends on / 依赖: exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to, mem_univ
-/
theorem exists_lt_card_fiber_of_nsmul_lt_card (hb : card β • b < card α) :
    exists y : β, b < #{x | f x = y} :=
  let ⟨y, _, h⟩ := exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (fun _ _ => mem_univ _) hb
  ⟨y, h⟩

/--
theorem `exists_lt_card_fiber_of_mul_lt_card` / 定理 `exists_lt_card_fiber_of_mul_lt_card`

English:
theorem exists_lt_card_fiber_of_mul_lt_card
  given: (hn : card β * n < card α)
  proof: exists_lt_card_fiber_of_nsmul_lt_card _ hn

中文:
定理 存在_lt_card_fiber_of_mul_lt_card
  条件: (hn : card β * n < card α)
  证明: exists_lt_card_fiber_of_nsmul_lt_card _ hn

Depends on / 依赖: exists_lt_card_fiber_of_nsmul_lt_card
-/
theorem exists_lt_card_fiber_of_mul_lt_card (hn : card β * n < card α) :
    exists y : β, n < #{x | f x = y} :=
  exists_lt_card_fiber_of_nsmul_lt_card _ hn

/--
theorem `exists_card_fiber_lt_of_card_lt_nsmul` / 定理 `exists_card_fiber_lt_of_card_lt_nsmul`

English:
theorem exists_card_fiber_lt_of_card_lt_nsmul
  given: (hb : ↑(card α) < card β • b)
  proof: let ⟨y, _, h⟩ := Finset.exists_card_fiber_lt_of_card_lt_nsmul (f := f) hb
  ⟨y, h⟩

中文:
定理 存在_card_fiber_lt_of_card_lt_nsmul
  条件: (hb : ↑(card α) < card β • b)
  证明: let ⟨y, _, h⟩ := Finset.exists_card_fiber_lt_of_card_lt_nsmul (f := f) hb
  ⟨y, h⟩

Depends on / 依赖: Finset, Finset.exists_card_fiber_lt_of_card_lt_nsmul, exists_card_fiber_lt_of_card_lt_nsmul
-/
theorem exists_card_fiber_lt_of_card_lt_nsmul (hb : ↑(card α) < card β • b) :
    exists y : β, #{x | f x = y} < b :=
  let ⟨y, _, h⟩ := Finset.exists_card_fiber_lt_of_card_lt_nsmul (f := f) hb
  ⟨y, h⟩

/--
theorem `exists_card_fiber_lt_of_card_lt_mul` / 定理 `exists_card_fiber_lt_of_card_lt_mul`

English:
theorem exists_card_fiber_lt_of_card_lt_mul
  given: (hn : card α < card β * n)
  proof: exists_card_fiber_lt_of_card_lt_nsmul _ hn

中文:
定理 存在_card_fiber_lt_of_card_lt_mul
  条件: (hn : card α < card β * n)
  证明: exists_card_fiber_lt_of_card_lt_nsmul _ hn

Depends on / 依赖: exists_card_fiber_lt_of_card_lt_nsmul
-/
theorem exists_card_fiber_lt_of_card_lt_mul (hn : card α < card β * n) :
    exists y : β, #{x | f x = y} < n :=
  exists_card_fiber_lt_of_card_lt_nsmul _ hn

/--
theorem `exists_le_card_fiber_of_nsmul_le_card` / 定理 `exists_le_card_fiber_of_nsmul_le_card`

English:
theorem exists_le_card_fiber_of_nsmul_le_card
  given: [Nonempty β] (hb : card β • b <= card α)
  proof: let ⟨y, _, h⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, h⟩

中文:
定理 存在_le_card_fiber_of_nsmul_le_card
  条件: [非空 β] (hb : card β • b <= card α)
  证明: let ⟨y, _, h⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, h⟩

Depends on / 依赖: exists_le_card_fiber_of_nsmul_le_card_of_maps_to, mem_univ, univ_nonempty
-/
theorem exists_le_card_fiber_of_nsmul_le_card [Nonempty β] (hb : card β • b <= card α) :
    exists y : β, b <= #{x | f x = y} :=
  let ⟨y, _, h⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, h⟩

/--
theorem `exists_le_card_fiber_of_mul_le_card` / 定理 `exists_le_card_fiber_of_mul_le_card`

English:
theorem exists_le_card_fiber_of_mul_le_card
  given: [Nonempty β] (hn : card β * n <= card α)
  proof: exists_le_card_fiber_of_nsmul_le_card _ hn

中文:
定理 存在_le_card_fiber_of_mul_le_card
  条件: [非空 β] (hn : card β * n <= card α)
  证明: exists_le_card_fiber_of_nsmul_le_card _ hn

Depends on / 依赖: exists_le_card_fiber_of_nsmul_le_card
-/
theorem exists_le_card_fiber_of_mul_le_card [Nonempty β] (hn : card β * n <= card α) :
    exists y : β, n <= #{x | f x = y} :=
  exists_le_card_fiber_of_nsmul_le_card _ hn

/--
theorem `exists_card_fiber_le_of_card_le_nsmul` / 定理 `exists_card_fiber_le_of_card_le_nsmul`

English:
theorem exists_card_fiber_le_of_card_le_nsmul
  given: [Nonempty β] (hb : ↑(card α) <= card β • b)
  proof: let ⟨y, _, h⟩ := Finset.exists_card_fiber_le_of_card_le_nsmul univ_nonempty hb
  ⟨y, h⟩

中文:
定理 存在_card_fiber_le_of_card_le_nsmul
  条件: [非空 β] (hb : ↑(card α) <= card β • b)
  证明: let ⟨y, _, h⟩ := Finset.exists_card_fiber_le_of_card_le_nsmul univ_nonempty hb
  ⟨y, h⟩

Depends on / 依赖: Finset, Finset.exists_card_fiber_le_of_card_le_nsmul, exists_card_fiber_le_of_card_le_nsmul, univ_nonempty
-/
theorem exists_card_fiber_le_of_card_le_nsmul [Nonempty β] (hb : ↑(card α) <= card β • b) :
    exists y : β, #{x | f x = y} <= b :=
  let ⟨y, _, h⟩ := Finset.exists_card_fiber_le_of_card_le_nsmul univ_nonempty hb
  ⟨y, h⟩

/--
theorem `exists_card_fiber_le_of_card_le_mul` / 定理 `exists_card_fiber_le_of_card_le_mul`

English:
theorem exists_card_fiber_le_of_card_le_mul
  given: [Nonempty β] (hn : card α <= card β * n)
  proof: exists_card_fiber_le_of_card_le_nsmul _ hn

中文:
定理 存在_card_fiber_le_of_card_le_mul
  条件: [非空 β] (hn : card α <= card β * n)
  证明: exists_card_fiber_le_of_card_le_nsmul _ hn

Depends on / 依赖: exists_card_fiber_le_of_card_le_nsmul
-/
theorem exists_card_fiber_le_of_card_le_mul [Nonempty β] (hn : card α <= card β * n) :
    exists y : β, #{x | f x = y} <= n :=
  exists_card_fiber_le_of_card_le_nsmul _ hn

end Fintype

namespace Nat

open Set

/--
theorem `exists_lt_modEq_of_infinite` / 定理 `exists_lt_modEq_of_infinite`

English:
theorem exists_lt_modEq_of_infinite
  given: {s : Set Nat} (hs : s.Infinite) {k : Nat} (hk : 0 < k)
  proof: (hs.exists_lt_map_eq_of_mapsTo fun n _ => show n % k in Iio k from Nat.mod_lt n hk)
    finite_lt_nat k

中文:
定理 存在_lt_modEq_of_infinite
  条件: {s : 集合 自然数} (hs : s.无限) {k : 自然数} (hk : 0 < k)
  证明: (hs.exists_lt_map_eq_of_mapsTo fun n _ => show n % k in Iio k from Nat.mod_lt n hk)
    finite_lt_nat k

Depends on / 依赖: Nat.mod_lt, exists_lt_map_eq_of_mapsTo, finite_lt_nat, hs.exists_lt_map_eq_of_mapsTo, mod_lt
-/
theorem exists_lt_modEq_of_infinite {s : Set Nat} (hs : s.Infinite) {k : Nat} (hk : 0 < k) :
    exists m in s, exists n in s, m < n ∧ m ≡ n [MOD k] :=
(hs.exists_lt_map_eq_of_mapsTo fun n _ => show n % k in Iio k from Nat.mod_lt n hk)
    finite_lt_nat k

end Nat
