/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.List.MinMax
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!

# Tropicalization of finitary operations

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferable order/lattice structure, to support
`Real`, `Rat`, `EReal`, and others (`ERat` is not yet defined).

Minima over `List α` are defined as producing a value in `WithTop α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/

public section

variable {R S : Type*}

open Tropical Finset

/--
theorem `List.trop_sum` / 定理 `List.trop_sum`

English:
theorem List.trop_sum
  given: [AddMonoid R] (l : List R)
  statement: trop l.sum = List.prod (l.map trop)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

中文:
定理 List.trop_sum
  条件: [AddMonoid R] (l : List R)
  结论: trop l.sum = List.prod (l.map trop)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]
-/
theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map trop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

/--
theorem `Multiset.trop_sum` / 定理 `Multiset.trop_sum`

English:
theorem Multiset.trop_sum
  given: [AddCommMonoid R] (s : Multiset R)
  proof: Quotient.inductionOn s (by simpa using List.trop_sum)

中文:
定理 Multiset.trop_sum
  条件: [AddCommMonoid R] (s : Multiset R)
  证明: Quotient.inductionOn s (by simpa using List.trop_sum)

Depends on / 依赖: List.trop_sum, Quotient, Quotient.inductionOn, inductionOn, trop_sum
-/
theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)

/--
theorem `trop_sum` / 定理 `trop_sum`

English:
theorem trop_sum
  given: [AddCommMonoid R] (s : Finset S) (f : S -> R)
  proof: by
  convert! Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

中文:
定理 trop_sum
  条件: [AddCommMonoid R] (s : Finset S) (f : S -> R)
  证明: by
  convert! Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.map_map, Multiset.trop_sum, comp_apply, convert, map_map, s.val.map, trop_sum
-/
theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S -> R) :
    trop (∑ i in s, f i) = ∏ i in s, trop (f i) := by
  convert! Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/--
theorem `List.untrop_prod` / 定理 `List.untrop_prod`

English:
theorem List.untrop_prod
  given: [AddMonoid R] (l : List (Tropical R))
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

中文:
定理 List.untrop_prod
  条件: [AddMonoid R] (l : List (Tropical R))
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]
-/
theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.prod = List.sum (l.map untrop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

/--
theorem `Multiset.untrop_prod` / 定理 `Multiset.untrop_prod`

English:
theorem Multiset.untrop_prod
  given: [AddCommMonoid R] (s : Multiset (Tropical R))
  proof: Quotient.inductionOn s (by simpa using List.untrop_prod)

中文:
定理 Multiset.untrop_prod
  条件: [AddCommMonoid R] (s : Multiset (Tropical R))
  证明: Quotient.inductionOn s (by simpa using List.untrop_prod)

Depends on / 依赖: List.untrop_prod, Quotient, Quotient.inductionOn, inductionOn, untrop_prod
-/
theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)

/--
theorem `untrop_prod` / 定理 `untrop_prod`

English:
theorem untrop_prod
  given: [AddCommMonoid R] (s : Finset S) (f : S -> Tropical R)
  proof: by
  convert! Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

中文:
定理 untrop_prod
  条件: [AddCommMonoid R] (s : Finset S) (f : S -> Tropical R)
  证明: by
  convert! Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

Depends on / 依赖: Function, Function.comp_apply, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.coprodMap, Multiset, Multiset.map_map, Multiset.untrop_prod, comp_apply, convert, coprodMap, map_map, s.val.map, untrop_prod
-/
theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S -> Tropical R) :
    untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) := by
  convert! Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/--
theorem `List.trop_minimum` / 定理 `List.trop_minimum`

English:
theorem List.trop_minimum
  given: [LinearOrder R] (l : List R)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [List.minimum_cons, ← IH]

中文:
定理 List.trop_minimum
  条件: [LinearOrder R] (l : List R)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [List.minimum_cons, ← IH]

Depends on / 依赖: List.minimum_cons, minimum_cons
-/
theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ WithTop.some)) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [List.minimum_cons, ← IH]

/--
theorem `Multiset.trop_inf` / 定理 `Multiset.trop_inf`

English:
theorem Multiset.trop_inf
  given: [LinearOrder R] [OrderTop R] (s : Multiset R)
  proof: by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp [← IH]

中文:
定理 Multiset.trop_inf
  条件: [LinearOrder R] [OrderTop R] (s : Multiset R)
  证明: by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp [← IH]

Depends on / 依赖: Multiset, Multiset.induction
-/
theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp [← IH]

/--
theorem `Finset.trop_inf` / 定理 `Finset.trop_inf`

English:
theorem Finset.trop_inf
  given: [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> R)
  proof: by
  convert! Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

中文:
定理 Finset.trop_inf
  条件: [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> R)
  证明: by
  convert! Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.map_map, Multiset.trop_inf, comp_apply, convert, map_map, s.val.map, trop_inf
-/
theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> R) :
    trop (s.inf f) = ∑ i in s, trop (f i) := by
  convert! Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/--
theorem `trop_sInf_image` / 定理 `trop_sInf_image`

English:
theorem trop_sInf_image
  given: [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S -> WithTop R)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h]; rw [inf'_eq_inf]; rw [s.trop_inf]

中文:
定理 trop_sInf_image
  条件: [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S -> WithTop R)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h]; rw [inf'_eq_inf]; rw [s.trop_inf]

Depends on / 依赖: IsOpenImmersion, IsPreimmersion, Scheme, Set.image_empty, WithTop, WithTop.sInf_empty, _eq_csInf_image, _eq_inf, coe_empty, eq_empty_or_nonempty, image_empty, s.eq_empty_or_nonempty, s.trop_inf, sInf_empty, sum_empty, trop_inf, trop_top
-/
theorem trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S -> WithTop R) :
    trop (sInf (f '' s)) = ∑ i in s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h]; rw [inf'_eq_inf]; rw [s.trop_inf]

/--
theorem `trop_iInf` / 定理 `trop_iInf`

English:
theorem trop_iInf
  given: [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> WithTop R)
  proof: by
  rw [iInf]; rw [← Set.image_univ]; rw [← coe_univ]; rw [trop_sInf_image]

中文:
定理 trop_iInf
  条件: [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> WithTop R)
  证明: by
  rw [iInf]; rw [← Set.image_univ]; rw [← coe_univ]; rw [trop_sInf_image]

Depends on / 依赖: Set.image_univ, coe_univ, image_univ, trop_sInf_image
-/
theorem trop_iInf [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [iInf]; rw [← Set.image_univ]; rw [← coe_univ]; rw [trop_sInf_image]

/--
theorem `Multiset.untrop_sum` / 定理 `Multiset.untrop_sum`

English:
theorem Multiset.untrop_sum
  given: [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R))
  proof: by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]

中文:
定理 Multiset.untrop_sum
  条件: [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R))
  证明: by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]

Depends on / 依赖: Multiset, Multiset.induction, inf_cons, map_cons, sum_cons, untrop_add
-/
theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.sum = Multiset.inf (s.map untrop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]

/--
theorem `Finset.untrop_sum'` / 定理 `Finset.untrop_sum'`

English:
theorem Finset.untrop_sum'
  given: [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> Tropical R)
  proof: by
  convert! Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]

中文:
定理 Finset.untrop_sum'
  条件: [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> Tropical R)
  证明: by
  convert! Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]

Depends on / 依赖: Function, Function.comp_apply, IsPreimmersion, Multiset, Multiset.map_map, Multiset.untrop_sum, comp_apply, convert, inf_def, map_map, s.val.map, untrop_sum
-/
theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S -> Tropical R) :
    untrop (∑ i in s, f i) = s.inf (untrop ∘ f) := by
  convert! Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]

/--
theorem `untrop_sum_eq_sInf_image` / 定理 `untrop_sum_eq_sInf_image`

English:
theorem untrop_sum_eq_sInf_image
  statement: [ConditionallyCompleteLinearOrder R] (s : Finset S)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']

中文:
定理 untrop_sum_eq_sInf_image
  结论: [ConditionallyCompleteLinearOrder R] (s : Finset S)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']

Depends on / 依赖: Finset, Finset.untrop_sum, Set.image_empty, WithTop, WithTop.sInf_empty, _eq_csInf_image, _eq_inf, coe_empty, eq_empty_or_nonempty, image_empty, s.eq_empty_or_nonempty, sInf_empty, sum_empty, untrop_sum, untrop_zero
-/
theorem untrop_sum_eq_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S -> Tropical (WithTop R)) : untrop (∑ i in s, f i) = sInf (untrop ∘ f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']

/--
theorem `untrop_sum` / 定理 `untrop_sum`

English:
theorem untrop_sum
  given: [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> Tropical (WithTop R))
  proof: by
  rw [iInf]; rw [← Set.image_univ]; rw [← coe_univ]; rw [untrop_sum_eq_sInf_image]; rw [Function.comp_def]

中文:
定理 untrop_sum
  条件: [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> Tropical (WithTop R))
  证明: by
  rw [iInf]; rw [← Set.image_univ]; rw [← coe_univ]; rw [untrop_sum_eq_sInf_image]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Set.image_univ, coe_univ, comp_def, image_univ, untrop_sum_eq_sInf_image
-/
theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S -> Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [iInf]; rw [← Set.image_univ]; rw [← coe_univ]; rw [untrop_sum_eq_sInf_image]; rw [Function.comp_def]

/--
theorem `Finset.untrop_sum` / 定理 `Finset.untrop_sum`

English:
theorem Finset.untrop_sum
  statement: [ConditionallyCompleteLinearOrder R] (s : Finset S)
  proof: by
  simpa [← _root_.untrop_sum] using (sum_attach _ _).symm

中文:
定理 Finset.untrop_sum
  结论: [ConditionallyCompleteLinearOrder R] (s : Finset S)
  证明: by
  simpa [← _root_.untrop_sum] using (sum_attach _ _).symm

Depends on / 依赖: _root_, _root_.untrop_sum, sum_attach, untrop_sum
-/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S -> Tropical (WithTop R)) : untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← _root_.untrop_sum] using (sum_attach _ _).symm
