/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Multiset.OrderedMonoid
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Big operators on a finset in ordered groups

This file contains the results concerning the interaction of finset big operators with ordered
groups/monoids.
-/

public section

assert_not_exists Ring

open Function

variable {ι α β M N G k R : Type*}

namespace Finset

section OrderedCommMonoid

variable [CommMonoid M] [CommMonoid N] [Preorder N]

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x ∈ s, g x) ≤ ∏ x ∈ s, f (g x)`. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
/--
theorem `le_prod_nonempty_of_submultiplicative_on_pred` / 定理 `le_prod_nonempty_of_submultiplicative_on_pred`

English:
theorem le_prod_nonempty_of_submultiplicative_on_pred
  statement: [IsOrderedMonoid N] (f : M -> N) (p : M -> Prop)
  proof: by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  simp

中文:
定理 le_prod_nonempty_of_submultiplicative_on_pred
  结论: [IsOrderedMonoid N] (f : M -> N) (p : M -> 命题)
  证明: by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  simp

Depends on / 依赖: Multiset, Multiset.forall_mem_map_iff.mpr, Multiset.le_prod_nonempty_of_submultiplicative_on_pred, forall_mem_map_iff, h_mul, hp_mul, hs_nonempty, hs_nonempty.ne_empty, le_prod_nonempty_of_submultiplicative_on_pred, le_trans, ne_empty
-/
theorem le_prod_nonempty_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M -> N) (p : M -> Prop)
    (h_mul : forall x y, p x -> p y -> f (x * y) <= f x * f y) (hp_mul : forall x y, p x -> p y -> p (x * y))
    (g : ι -> M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : forall i in s, p (g i)) :
    f (∏ i in s, g i) <= ∏ i in s, f (g i) := by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  simp

/-- Let `{x | p x}` be an additive subsemigroup of an additive commutative monoid `M`. Let
`f : M → N` be a map subadditive on `{x | p x}`, i.e., `p x → p y → f (x + y) ≤ f x + f y`. Let
`g i`, `i ∈ s`, be a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_nonempty_of_subadditive]
/--
theorem `le_prod_nonempty_of_submultiplicative` / 定理 `le_prod_nonempty_of_submultiplicative`

English:
theorem le_prod_nonempty_of_submultiplicative
  statement: [IsOrderedMonoid N] (f : M -> N)
  proof: le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (fun x y _ _ => h_mul x y)
    (fun _ _ _ _ => trivial) g s hs fun _ _ => trivial

中文:
定理 le_prod_nonempty_of_submultiplicative
  结论: [IsOrderedMonoid N] (f : M -> N)
  证明: le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (fun x y _ _ => h_mul x y)
    (fun _ _ _ _ => trivial) g s hs fun _ _ => trivial

Depends on / 依赖: h_mul, le_prod_nonempty_of_submultiplicative_on_pred
-/
theorem le_prod_nonempty_of_submultiplicative [IsOrderedMonoid N] (f : M -> N)
    (h_mul : forall x y, f (x * y) <= f x * f y) {s : Finset ι} (hs : s.Nonempty) (g : ι -> M) :
    f (∏ i in s, g i) <= ∏ i in s, f (g i) :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (fun x y _ _ => h_mul x y)
    (fun _ _ _ _ => trivial) g s hs fun _ _ => trivial

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_of_subadditive_on_pred]
/--
theorem `le_prod_of_submultiplicative_on_pred` / 定理 `le_prod_of_submultiplicative_on_pred`

English:
theorem le_prod_of_submultiplicative_on_pred
  statement: [IsOrderedMonoid N] (f : M -> N) (p : M -> Prop)
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs

中文:
定理 le_prod_of_submultiplicative_on_pred
  结论: [IsOrderedMonoid N] (f : M -> N) (p : M -> 命题)
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs

Depends on / 依赖: eq_empty_or_nonempty, h_mul, h_one, hp_mul, hs_nonempty, le_prod_nonempty_of_submultiplicative_on_pred
-/
theorem le_prod_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M -> N) (p : M -> Prop)
    (h_one : f 1 <= 1) (h_mul : forall x y, p x -> p y -> f (x * y) <= f x * f y)
    (hp_mul : forall x y, p x -> p y -> p (x * y)) (g : ι -> M) {s : Finset ι} (hs : forall i in s, p (g i)) :
    f (∏ i in s, g i) <= ∏ i in s, f (g i) := by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs

/-- Let `{x | p x}` be a subsemigroup of a commutative additive monoid `M`. Let `f : M → N` be a map
such that `f 0 = 0` and `f` is subadditive on `{x | p x}`, i.e. `p x → p y → f (x + y) ≤ f x + f y`.
Let `g i`, `i ∈ s`, be a finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ x ∈ s, g x) ≤ ∑ x ∈ s, f (g x)`. -/
add_decl_doc le_sum_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_of_subadditive]
/--
theorem `le_prod_of_submultiplicative` / 定理 `le_prod_of_submultiplicative`

English:
theorem le_prod_of_submultiplicative
  statement: [IsOrderedMonoid N] (f : M -> N) (h_one : f 1 <= 1)
  proof: le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) (by simp)

中文:
定理 le_prod_of_submultiplicative
  结论: [IsOrderedMonoid N] (f : M -> N) (h_one : f 1 <= 1)
  证明: le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) (by simp)

Depends on / 依赖: Multiset, Multiset.le_prod_of_submultiplicative, h_mul, h_one, le_prod_of_submultiplicative, le_trans
-/
theorem le_prod_of_submultiplicative [IsOrderedMonoid N] (f : M -> N) (h_one : f 1 <= 1)
    (h_mul : forall x y, f (x * y) <= f x * f y) (s : Finset ι) (g : ι -> M) :
    f (∏ i in s, g i) <= ∏ i in s, f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) (by simp)

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y`, `f 0 = 0`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_of_subadditive

variable {f g : ι -> N} {s t : Finset ι}

/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i ∈ s, f i ≤ ∏ i ∈ s, g i`. -/
@[to_additive (attr := gcongr) sum_le_sum]
/--
theorem `prod_le_prod'` / 定理 `prod_le_prod'`

English:
theorem prod_le_prod'
  given: [MulLeftMono N] (h : forall i in s, f i <= g i)
  statement: ∏ i in s, f i <= ∏ i in s, g i
  proof: Multiset.prod_map_le_prod_map f g h

中文:
定理 prod_le_prod'
  条件: [MulLeftMono N] (h : 对任意 i in s, f i <= g i)
  结论: ∏ i in s, f i <= ∏ i in s, g i
  证明: Multiset.prod_map_le_prod_map f g h

Depends on / 依赖: Multiset, Multiset.prod_map_le_prod_map, prod_map_le_prod_map
-/
theorem prod_le_prod' [MulLeftMono N] (h : forall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i :=
  Multiset.prod_map_le_prod_map f g h

attribute [bound] sum_le_sum

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then
`∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`. -/
add_decl_doc sum_le_sum

/-- A finite product of monotone functions is monotone. -/
@[to_additive finsetSum /-- A finite sum of monotone functions is monotone. -/]
/--
theorem `_root_.Monotone.finsetProd'` / 定理 `_root_.Monotone.finsetProd'`

English:
theorem _root_.Monotone.finsetProd'
  statement: [MulLeftMono N] {γ : Type*} [Preorder γ]
  proof: fun _ _ hab => Finset.prod_le_prod' fun i hi => hf i hi hab

中文:
定理 _root_.Monotone.finsetProd'
  结论: [MulLeftMono N] {γ : 类型} [Preorder γ]
  证明: fun _ _ hab => Finset.prod_le_prod' fun i hi => hf i hi hab

Depends on / 依赖: Finset, Finset.prod_le_prod, prod_le_prod
-/
theorem _root_.Monotone.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ]
    {f : ι -> γ -> N} (hf : forall i in s, Monotone (f i)) :
    Monotone fun x => ∏ i in s, f i x :=
  fun _ _ hab => Finset.prod_le_prod' fun i hi => hf i hi hab

/-- A finite product of functions monotone on `u` is monotone on `u`. -/
@[to_additive finsetSum /-- A finite sum of functions monotone on `u` is monotone on `u`. -/]
/--
theorem `_root_.MonotoneOn.finsetProd'` / 定理 `_root_.MonotoneOn.finsetProd'`

English:
theorem _root_.MonotoneOn.finsetProd'
  statement: [MulLeftMono N] {γ : Type*} [Preorder γ] {u : Set γ}
  proof: fun _ ha _ hb hab => Finset.prod_le_prod' fun i hi => hf i hi ha hb hab

中文:
定理 _root_.MonotoneOn.finsetProd'
  结论: [MulLeftMono N] {γ : 类型} [Preorder γ] {u : Set γ}
  证明: fun _ ha _ hb hab => Finset.prod_le_prod' fun i hi => hf i hi ha hb hab

Depends on / 依赖: Finset, Finset.prod_le_prod, prod_le_prod
-/
theorem _root_.MonotoneOn.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ] {u : Set γ}
    {f : ι -> γ -> N} (hf : forall i in s, MonotoneOn (f i) u) :
    MonotoneOn (fun x => ∏ i in s, f i x) u :=
  fun _ ha _ hb hab => Finset.prod_le_prod' fun i hi => hf i hi ha hb hab

/-- A finite product of antitone functions is antitone. -/
@[to_additive finsetSum /-- A finite sum of antitone functions is antitone. -/]
/--
theorem `_root_.Antitone.finsetProd'` / 定理 `_root_.Antitone.finsetProd'`

English:
theorem _root_.Antitone.finsetProd'
  statement: [MulLeftMono N] {γ : Type*} [Preorder γ]
  proof: fun _ _ hab => Finset.prod_le_prod' fun i hi => hf i hi hab

中文:
定理 _root_.Antitone.finsetProd'
  结论: [MulLeftMono N] {γ : 类型} [Preorder γ]
  证明: fun _ _ hab => Finset.prod_le_prod' fun i hi => hf i hi hab

Depends on / 依赖: Finset, Finset.prod_le_prod, prod_le_prod
-/
theorem _root_.Antitone.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ]
    {f : ι -> γ -> N} (hf : forall i in s, Antitone (f i)) :
    Antitone fun x => ∏ i in s, f i x :=
  fun _ _ hab => Finset.prod_le_prod' fun i hi => hf i hi hab

/-- A finite product of functions antitone on `u` is antitone on `u`. -/
@[to_additive finsetSum /-- A finite sum of functions antitone on `u` is antitone on `u`. -/]
/--
theorem `_root_.AntitoneOn.finsetProd'` / 定理 `_root_.AntitoneOn.finsetProd'`

English:
theorem _root_.AntitoneOn.finsetProd'
  statement: [MulLeftMono N] {γ : Type*} [Preorder γ] {u : Set γ}
  proof: fun _ ha _ hb hab => Finset.prod_le_prod' fun i hi => hf i hi ha hb hab

@[to_additive sum_nonneg]

中文:
定理 _root_.AntitoneOn.finsetProd'
  结论: [MulLeftMono N] {γ : 类型} [Preorder γ] {u : Set γ}
  证明: fun _ ha _ hb hab => Finset.prod_le_prod' fun i hi => hf i hi ha hb hab

@[to_additive sum_nonneg]

Depends on / 依赖: Finset, Finset.prod_le_prod, prod_le_prod
-/
theorem _root_.AntitoneOn.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ] {u : Set γ}
    {f : ι -> γ -> N} (hf : forall i in s, AntitoneOn (f i) u) :
    AntitoneOn (fun x => ∏ i in s, f i x) u :=
  fun _ ha _ hb hab => Finset.prod_le_prod' fun i hi => hf i hi ha hb hab

@[to_additive sum_nonneg]
/--
theorem `one_le_prod'` / 定理 `one_le_prod'`

English:
theorem one_le_prod'
  given: [MulLeftMono N] (h : forall i in s, 1 <= f i)
  statement: 1 <= ∏ i in s, f i
  proof: le_trans (by rw [prod_const_one]) (prod_le_prod' h)

@[to_additive Finset.sum_nonneg']

中文:
定理 one_le_prod'
  条件: [MulLeftMono N] (h : 对任意 i in s, 1 <= f i)
  结论: 1 <= ∏ i in s, f i
  证明: le_trans (by rw [prod_const_one]) (prod_le_prod' h)

@[to_additive Finset.sum_nonneg']

Depends on / 依赖: le_trans, prod_const_one, prod_le_prod
-/
theorem one_le_prod' [MulLeftMono N] (h : forall i in s, 1 <= f i) : 1 <= ∏ i in s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)

@[to_additive Finset.sum_nonneg']
/--
theorem `one_le_prod''` / 定理 `one_le_prod''`

English:
theorem one_le_prod''
  given: [MulLeftMono N] (h : forall i : ι, 1 <= f i)
  statement: 1 <= ∏ i in s, f i
  proof: Finset.one_le_prod' fun i _ => h i

@[to_additive sum_nonpos]

中文:
定理 one_le_prod''
  条件: [MulLeftMono N] (h : 对任意 i : ι, 1 <= f i)
  结论: 1 <= ∏ i in s, f i
  证明: Finset.one_le_prod' fun i _ => h i

@[to_additive sum_nonpos]

Depends on / 依赖: Finset, Finset.one_le_prod, one_le_prod
-/
theorem one_le_prod'' [MulLeftMono N] (h : forall i : ι, 1 <= f i) : 1 <= ∏ i in s, f i :=
  Finset.one_le_prod' fun i _ => h i

@[to_additive sum_nonpos]
/--
theorem `prod_le_one'` / 定理 `prod_le_one'`

English:
theorem prod_le_one'
  given: [MulLeftMono N] (h : forall i in s, f i <= 1)
  statement: ∏ i in s, f i <= 1
  proof: (prod_le_prod' h).trans_eq (by rw [prod_const_one])

@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]

中文:
定理 prod_le_one'
  条件: [MulLeftMono N] (h : 对任意 i in s, f i <= 1)
  结论: ∏ i in s, f i <= 1
  证明: (prod_le_prod' h).trans_eq (by rw [prod_const_one])

@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]

Depends on / 依赖: prod_const_one, prod_le_prod, trans_eq
-/
theorem prod_le_one' [MulLeftMono N] (h : forall i in s, f i <= 1) : ∏ i in s, f i <= 1 :=
  (prod_le_prod' h).trans_eq (by rw [prod_const_one])

@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]
/--
theorem `prod_le_prod_of_subset_of_one_le'` / 定理 `prod_le_prod_of_subset_of_one_le'`

English:
theorem prod_le_prod_of_subset_of_one_le'
  statement: [MulLeftMono N] (h : s subseteq t)
  proof: by
  classical calc
      ∏ i in s, f i <= (∏ i in t \ s, f i) * ∏ i in s, f i :=
le_mul_of_one_le_left' one_le_prod' by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s union s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]

@[to_additive]

中文:
定理 prod_le_prod_of_subset_of_one_le'
  结论: [MulLeftMono N] (h : s subseteq t)
  证明: by
  classical calc
      ∏ i in s, f i <= (∏ i in t \ s, f i) * ∏ i in s, f i :=
le_mul_of_one_le_left' one_le_prod' by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s union s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]

@[to_additive]

Depends on / 依赖: and_imp, classical, le_mul_of_one_le_left, mem_sdiff, one_le_prod, prod_union, sdiff_disjoint, sdiff_union_of_subset
-/
theorem prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s subseteq t)
    (hf : forall i in t, i ∉ s -> 1 <= f i) : ∏ i in s, f i <= ∏ i in t, f i := by
  classical calc
      ∏ i in s, f i <= (∏ i in t \ s, f i) * ∏ i in s, f i :=
le_mul_of_one_le_left' one_le_prod' by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s union s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]

@[to_additive]
/--
theorem `prod_le_prod_of_subset_of_le_one'` / 定理 `prod_le_prod_of_subset_of_le_one'`

English:
theorem prod_le_prod_of_subset_of_le_one'
  proof: prod_le_prod_of_subset_of_one_le' (N := Nᵒᵈ) h hf

@[to_additive sum_mono_set_of_nonneg]

中文:
定理 prod_le_prod_of_subset_of_le_one'
  证明: prod_le_prod_of_subset_of_one_le' (N := Nᵒᵈ) h hf

@[to_additive sum_mono_set_of_nonneg]

Depends on / 依赖: prod_le_prod_of_subset_of_one_le
-/
theorem prod_le_prod_of_subset_of_le_one'
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι -> N} {s t : Finset ι} [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> f i <= 1) :
    ∏ i in t, f i <= ∏ i in s, f i :=
  prod_le_prod_of_subset_of_one_le' (N := Nᵒᵈ) h hf

@[to_additive sum_mono_set_of_nonneg]
/--
theorem `prod_mono_set_of_one_le'` / 定理 `prod_mono_set_of_one_le'`

English:
theorem prod_mono_set_of_one_le'
  given: [MulLeftMono N] (hf : forall x, 1 <= f x)
  proof: fun _ _ hst => prod_le_prod_of_subset_of_one_le' hst fun x _ _ => hf x

@[to_additive]

中文:
定理 prod_mono_set_of_one_le'
  条件: [MulLeftMono N] (hf : 对任意 x, 1 <= f x)
  证明: fun _ _ hst => prod_le_prod_of_subset_of_one_le' hst fun x _ _ => hf x

@[to_additive]

Depends on / 依赖: prod_le_prod_of_subset_of_one_le
-/
theorem prod_mono_set_of_one_le' [MulLeftMono N] (hf : forall x, 1 <= f x) :
    Monotone fun s => ∏ x in s, f x :=
  fun _ _ hst => prod_le_prod_of_subset_of_one_le' hst fun x _ _ => hf x

@[to_additive]
/--
theorem `prod_anti_set_of_le_one'` / 定理 `prod_anti_set_of_le_one'`

English:
theorem prod_anti_set_of_le_one'
  proof: fun _ _ hst => prod_le_prod_of_subset_of_le_one' hst (by simp [hf])

@[to_additive sum_le_univ_sum_of_nonneg]

中文:
定理 prod_anti_set_of_le_one'
  证明: fun _ _ hst => prod_le_prod_of_subset_of_le_one' hst (by simp [hf])

@[to_additive sum_le_univ_sum_of_nonneg]

Depends on / 依赖: prod_le_prod_of_subset_of_le_one
-/
theorem prod_anti_set_of_le_one'
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι -> N} [MulLeftMono N] (hf : forall (x : ι), f x <= 1) :
    Antitone fun (s : Finset ι) => ∏ x in s, f x :=
  fun _ _ hst => prod_le_prod_of_subset_of_le_one' hst (by simp [hf])

@[to_additive sum_le_univ_sum_of_nonneg]
/--
theorem `prod_le_univ_prod_of_one_le'` / 定理 `prod_le_univ_prod_of_one_le'`

English:
theorem prod_le_univ_prod_of_one_le'
  given: [MulLeftMono N] [Fintype ι] {s : Finset ι} (w : forall x, 1 <= f x)
  proof: prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ => w a

@[to_additive sum_eq_zero_iff_of_nonneg]

中文:
定理 prod_le_univ_prod_of_one_le'
  条件: [MulLeftMono N] [Fintype ι] {s : Finset ι} (w : 对任意 x, 1 <= f x)
  证明: prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ => w a

@[to_additive sum_eq_zero_iff_of_nonneg]

Depends on / 依赖: prod_le_prod_of_subset_of_one_le, subset_univ
-/
theorem prod_le_univ_prod_of_one_le' [MulLeftMono N] [Fintype ι] {s : Finset ι} (w : forall x, 1 <= f x) :
    ∏ x in s, f x <= ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ => w a

@[to_additive sum_eq_zero_iff_of_nonneg]
/--
theorem `prod_eq_one_iff_of_one_le'` / 定理 `prod_eq_one_iff_of_one_le'`

English:
theorem prod_eq_one_iff_of_one_le'
  statement: {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
  proof: by
  classical
    refine Finset.induction_on s
      (fun _ => ⟨fun _ _ h => False.elim (Finset.notMem_empty _ h), fun _ => rfl⟩) ?_
    intro a s ha ih H
    have : forall i in s, 1 <= f i := fun _ => H _ ∘ mem_insert_of_mem
    rw [prod_insert ha]; rw [mul_eq_one_iff_of_one_le (H _ <| mem_insert_

中文:
定理 prod_eq_one_iff_of_one_le'
  结论: {ι : 类型u_1} {N : 类型u_5} [CommMonoid N] [PartialOrder N]
  证明: by
  classical
    refine Finset.induction_on s
      (fun _ => ⟨fun _ _ h => False.elim (Finset.notMem_empty _ h), fun _ => rfl⟩) ?_
    intro a s ha ih H
    have : forall i in s, 1 <= f i := fun _ => H _ ∘ mem_insert_of_mem
    rw [prod_insert ha]; rw [mul_eq_one_iff_of_one_le (H _ <| mem_insert_

Depends on / 依赖: False.elim, Finset, Finset.induction_on, Finset.notMem_empty, classical, forall_mem_insert, induction_on, mem_insert_of_mem, mem_insert_self, mul_eq_one_iff_of_one_le, notMem_empty, one_le_prod, prod_insert
-/
theorem prod_eq_one_iff_of_one_le' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι -> N} {s : Finset ι} [MulLeftMono N] :
    (forall i in s, 1 <= f i) -> ((∏ i in s, f i) = 1 ↔ forall i in s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ => ⟨fun _ _ h => False.elim (Finset.notMem_empty _ h), fun _ => rfl⟩) ?_
    intro a s ha ih H
    have : forall i in s, 1 <= f i := fun _ => H _ ∘ mem_insert_of_mem
    rw [prod_insert ha]; rw [mul_eq_one_iff_of_one_le (H _ <| mem_insert_self _ _) (one_le_prod' this)]; rw [forall_mem_insert]; rw [ih this]

@[to_additive sum_pos_iff_of_nonneg]
/--
lemma `one_lt_prod_iff_of_one_le` / 引理 `one_lt_prod_iff_of_one_le`

English:
lemma one_lt_prod_iff_of_one_le
  statement: {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
  proof: by
  have hsum : 1 <= ∏ x in s, f x := one_le_prod' hf
  rw [hsum.lt_iff_ne']; rw [Ne]; rw [prod_eq_one_iff_of_one_le' hf]; rw [not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

@[to_additive sum_eq_zero_iff_of_nonpos]

中文:
引理 one_lt_prod_iff_of_one_le
  结论: {ι : 类型u_1} {N : 类型u_5} [CommMonoid N] [PartialOrder N]
  证明: by
  have hsum : 1 <= ∏ x in s, f x := one_le_prod' hf
  rw [hsum.lt_iff_ne']; rw [Ne]; rw [prod_eq_one_iff_of_one_le' hf]; rw [not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

@[to_additive sum_eq_zero_iff_of_nonpos]

Depends on / 依赖: contextual, exists_const_iff, exists_prop, hsum.lt_iff_ne, lt_iff_ne, not_forall, one_le_prod, prod_eq_one_iff_of_one_le
-/
lemma one_lt_prod_iff_of_one_le {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι -> N} {s : Finset ι} [MulLeftMono N] (hf : forall x in s, 1 <= f x) :
    1 < ∏ x in s, f x ↔ exists x in s, 1 < f x := by
  have hsum : 1 <= ∏ x in s, f x := one_le_prod' hf
  rw [hsum.lt_iff_ne']; rw [Ne]; rw [prod_eq_one_iff_of_one_le' hf]; rw [not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

@[to_additive sum_eq_zero_iff_of_nonpos]
/--
theorem `prod_eq_one_iff_of_le_one'` / 定理 `prod_eq_one_iff_of_le_one'`

English:
theorem prod_eq_one_iff_of_le_one'
  statement: {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
  proof: prod_eq_one_iff_of_one_le' (N := Nᵒᵈ)

@[to_additive]

中文:
定理 prod_eq_one_iff_of_le_one'
  结论: {ι : 类型u_1} {N : 类型u_5} [CommMonoid N] [PartialOrder N]
  证明: prod_eq_one_iff_of_one_le' (N := Nᵒᵈ)

@[to_additive]

Depends on / 依赖: prod_eq_one_iff_of_one_le
-/
theorem prod_eq_one_iff_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι -> N} {s : Finset ι} [MulLeftMono N] :
    (forall i in s, f i <= 1) -> ((∏ i in s, f i) = 1 ↔ forall i in s, f i = 1) :=
  prod_eq_one_iff_of_one_le' (N := Nᵒᵈ)

@[to_additive]
/--
lemma `prod_lt_one_iff_of_le_one` / 引理 `prod_lt_one_iff_of_le_one`

English:
lemma prod_lt_one_iff_of_le_one
  statement: {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
  proof: one_lt_prod_iff_of_one_le (N := Nᵒᵈ) hf

@[to_additive single_le_sum]

中文:
引理 prod_lt_one_iff_of_le_one
  结论: {ι : 类型u_1} {N : 类型u_5} [CommMonoid N] [PartialOrder N]
  证明: one_lt_prod_iff_of_one_le (N := Nᵒᵈ) hf

@[to_additive single_le_sum]

Depends on / 依赖: one_lt_prod_iff_of_one_le
-/
lemma prod_lt_one_iff_of_le_one {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι -> N} {s : Finset ι} [MulLeftMono N] (hf : forall x in s, f x <= 1) :
    ∏ x in s, f x < 1 ↔ exists x in s, f x < 1 :=
  one_lt_prod_iff_of_one_le (N := Nᵒᵈ) hf

@[to_additive single_le_sum]
/--
theorem `single_le_prod'` / 定理 `single_le_prod'`

English:
theorem single_le_prod'
  given: [MulLeftMono N] (hf : forall i in s, 1 <= f i) {a} (h : a in s)
  proof: calc
    f a = ∏ i in {a}, f i := (prod_singleton _ _).symm
    _ <= ∏ i in s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ => hf i hi

@[to_additive]

中文:
定理 single_le_prod'
  条件: [MulLeftMono N] (hf : 对任意 i in s, 1 <= f i) {a} (h : a in s)
  证明: calc
    f a = ∏ i in {a}, f i := (prod_singleton _ _).symm
    _ <= ∏ i in s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ => hf i hi

@[to_additive]

Depends on / 依赖: prod_le_prod_of_subset_of_one_le, prod_singleton, singleton_subset_iff
-/
theorem single_le_prod' [MulLeftMono N] (hf : forall i in s, 1 <= f i) {a} (h : a in s) :
    f a <= ∏ x in s, f x :=
  calc
    f a = ∏ i in {a}, f i := (prod_singleton _ _).symm
    _ <= ∏ i in s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ => hf i hi

@[to_additive]
/--
lemma `mul_le_prod` / 引理 `mul_le_prod`

English:
lemma mul_le_prod
  statement: [MulLeftMono N] {i j : ι} (hf : forall i in s, 1 <= f i) (hi : i in s) (hj : j in s)
  proof: calc
    f i * f j = ∏ k in .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ <= ∏ k in s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ => hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]

中文:
引理 mul_le_prod
  结论: [MulLeftMono N] {i j : ι} (hf : 对任意 i in s, 1 <= f i) (hi : i in s) (hj : j in s)
  证明: calc
    f i * f j = ∏ k in .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ <= ∏ k in s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ => hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]

Depends on / 依赖: cons_subset, prod_cons, prod_le_prod_of_subset_of_one_le, prod_singleton
-/
lemma mul_le_prod [MulLeftMono N] {i j : ι} (hf : forall i in s, 1 <= f i) (hi : i in s) (hj : j in s)
    (hne : i != j) :
    f i * f j <= ∏ k in s, f k :=
  calc
    f i * f j = ∏ k in .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ <= ∏ k in s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ => hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]
/--
theorem `prod_le_pow_card` / 定理 `prod_le_pow_card`

English:
theorem prod_le_pow_card
  given: [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : forall x in s, f x <= n)
  proof: by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp

@[to_additive card_nsmul_le_sum]

中文:
定理 prod_le_pow_card
  条件: [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : 对任意 x in s, f x <= n)
  证明: by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp

@[to_additive card_nsmul_le_sum]

Depends on / 依赖: Multiset, Multiset.prod_le_pow_card, prod_le_pow_card, s.val.map
-/
theorem prod_le_pow_card [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : forall x in s, f x <= n) :
    s.prod f <= n ^ #s := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp

@[to_additive card_nsmul_le_sum]
/--
theorem `pow_card_le_prod` / 定理 `pow_card_le_prod`

English:
theorem pow_card_le_prod
  given: [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : forall x in s, n <= f x)
  proof: Finset.prod_le_pow_card (N := Nᵒᵈ) _ _ _ h

中文:
定理 pow_card_le_prod
  条件: [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : 对任意 x in s, n <= f x)
  证明: Finset.prod_le_pow_card (N := Nᵒᵈ) _ _ _ h

Depends on / 依赖: Finset, Finset.prod_le_pow_card, prod_le_pow_card
-/
theorem pow_card_le_prod [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : forall x in s, n <= f x) :
    n ^ #s <= s.prod f := Finset.prod_le_pow_card (N := Nᵒᵈ) _ _ _ h

/--
theorem `card_biUnion_le_card_mul` / 定理 `card_biUnion_le_card_mul`

English:
theorem card_biUnion_le_card_mul
  statement: [DecidableEq β] (s : Finset ι) (f : ι -> Finset β) (n : Nat)
  proof: card_biUnion_le.trans sum_le_card_nsmul _ _ _ h

中文:
定理 card_biUnion_le_card_mul
  结论: [DecidableEq β] (s : Finset ι) (f : ι -> Finset β) (n : 自然数)
  证明: card_biUnion_le.trans sum_le_card_nsmul _ _ _ h

Depends on / 依赖: card_biUnion_le, card_biUnion_le.trans, sum_le_card_nsmul
-/
theorem card_biUnion_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι -> Finset β) (n : Nat)
    (h : forall a in s, #(f a) <= n) : #(s.biUnion f) <= #s * n :=
card_biUnion_le.trans sum_le_card_nsmul _ _ _ h

variable {ι' : Type*} [DecidableEq ι']

@[to_additive sum_fiberwise_le_sum_of_sum_fiber_nonneg]
/--
theorem `prod_fiberwise_le_prod_of_one_le_prod_fiber'` / 定理 `prod_fiberwise_le_prod_of_one_le_prod_fiber'`

English:
theorem prod_fiberwise_le_prod_of_one_le_prod_fiber'
  statement: [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'}
  proof: calc
    (∏ y in t, ∏ x in s with g x = y, f x) <=
        ∏ y in t union s.image g, ∏ x in s with g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ => h y
    _ = ∏ x in s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx => mem_union.2 <| Or.inr <| mem_image_of_mem 

中文:
定理 prod_fiberwise_le_prod_of_one_le_prod_fiber'
  结论: [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'}
  证明: calc
    (∏ y in t, ∏ x in s with g x = y, f x) <=
        ∏ y in t union s.image g, ∏ x in s with g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ => h y
    _ = ∏ x in s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx => mem_union.2 <| Or.inr <| mem_image_of_mem 

Depends on / 依赖: Or.inr, mem_image_of_mem, mem_union, prod_fiberwise_of_maps_to, prod_le_prod_of_subset_of_one_le, s.image, subset_union_left
-/
theorem prod_fiberwise_le_prod_of_one_le_prod_fiber' [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'}
    {f : ι -> N} (h : forall y ∉ t, (1 : N) <= ∏ x in s with g x = y, f x) :
    (∏ y in t, ∏ x in s with g x = y, f x) <= ∏ x in s, f x :=
  calc
    (∏ y in t, ∏ x in s with g x = y, f x) <=
        ∏ y in t union s.image g, ∏ x in s with g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ => h y
    _ = ∏ x in s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx => mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _

@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
/--
theorem `prod_le_prod_fiberwise_of_prod_fiber_le_one'` / 定理 `prod_le_prod_fiberwise_of_prod_fiber_le_one'`

English:
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one'
  statement: [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'}
  proof: prod_fiberwise_le_prod_of_one_le_prod_fiber' (N := Nᵒᵈ) h

@[to_additive]

中文:
定理 prod_le_prod_fiberwise_of_prod_fiber_le_one'
  结论: [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'}
  证明: prod_fiberwise_le_prod_of_one_le_prod_fiber' (N := Nᵒᵈ) h

@[to_additive]

Depends on / 依赖: prod_fiberwise_le_prod_of_one_le_prod_fiber
-/
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'}
    {f : ι -> N} (h : forall y ∉ t, ∏ x in s with g x = y, f x <= 1) :
    ∏ x in s, f x <= ∏ y in t, ∏ x in s with g x = y, f x :=
  prod_fiberwise_le_prod_of_one_le_prod_fiber' (N := Nᵒᵈ) h

@[to_additive]
/--
lemma `prod_image_le_of_one_le` / 引理 `prod_image_le_of_one_le`

English:
lemma prod_image_le_of_one_le
  statement: [MulLeftMono N]
  proof: by
  rw [prod_comp f g]
  refine prod_le_prod' fun a hag => ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  apply le_self_pow (hf a hag)
  rw [← Nat.pos_iff_ne_zero]; rw [card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

中文:
引理 prod_image_le_of_one_le
  结论: [MulLeftMono N]
  证明: by
  rw [prod_comp f g]
  refine prod_le_prod' fun a hag => ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  apply le_self_pow (hf a hag)
  rw [← Nat.pos_iff_ne_zero]; rw [card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

Depends on / 依赖: Finset, Finset.mem_image.mp, Nat.pos_iff_ne_zero, card_pos, le_self_pow, mem_filter, mem_filter.mpr, mem_image, pos_iff_ne_zero, prod_comp, prod_le_prod
-/
lemma prod_image_le_of_one_le [MulLeftMono N]
    {g : ι -> ι'} {f : ι' -> N} (hf : forall u in s.image g, 1 <= f u) :
    ∏ u in s.image g, f u <= ∏ u in s, f (g u) := by
  rw [prod_comp f g]
  refine prod_le_prod' fun a hag => ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  apply le_self_pow (hf a hag)
  rw [← Nat.pos_iff_ne_zero]; rw [card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

end OrderedCommMonoid

section ProdSum

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β]
  (s : Finset ι) {f : ι -> α} (g : α -> β)

/--
theorem `apply_prod_le_sum_apply` / 定理 `apply_prod_le_sum_apply`

English:
theorem apply_prod_le_sum_apply
  given: (h_one : g 1 <= 0) (h_mul : forall (a b : α), g (a * b) <= g a + g b)
  proof: by
  refine (Multiset.apply_prod_le_sum_map _ _ h_one h_mul).trans_eq ?_
  rw [Multiset.map_map]; rw [Function.comp_def]; rw [Finset.sum_map_val]

中文:
定理 apply_prod_le_sum_apply
  条件: (h_one : g 1 <= 0) (h_mul : 对任意 (a b : α), g (a * b) <= g a + g b)
  证明: by
  refine (Multiset.apply_prod_le_sum_map _ _ h_one h_mul).trans_eq ?_
  rw [Multiset.map_map]; rw [Function.comp_def]; rw [Finset.sum_map_val]

Depends on / 依赖: Finset, Finset.sum_map_val, Function, Function.comp_def, Multiset, Multiset.apply_prod_le_sum_map, Multiset.map_map, apply_prod_le_sum_map, comp_def, h_mul, h_one, map_map, sum_map_val, trans_eq
-/
theorem apply_prod_le_sum_apply (h_one : g 1 <= 0) (h_mul : forall (a b : α), g (a * b) <= g a + g b) :
    g (∏ x in s, f x) <= ∑ x in s, g (f x) := by
  refine (Multiset.apply_prod_le_sum_map _ _ h_one h_mul).trans_eq ?_
  rw [Multiset.map_map]; rw [Function.comp_def]; rw [Finset.sum_map_val]

/--
theorem `sum_apply_le_apply_prod` / 定理 `sum_apply_le_apply_prod`

English:
theorem sum_apply_le_apply_prod
  given: (h_one : 0 <= g 1) (h_mul : forall (a b : α), g a + g b <= g (a * b))
  proof: s.apply_prod_le_sum_apply (β := βᵒᵈ) g h_one h_mul

中文:
定理 sum_apply_le_apply_prod
  条件: (h_one : 0 <= g 1) (h_mul : 对任意 (a b : α), g a + g b <= g (a * b))
  证明: s.apply_prod_le_sum_apply (β := βᵒᵈ) g h_one h_mul

Depends on / 依赖: apply_prod_le_sum_apply, h_mul, h_one, s.apply_prod_le_sum_apply
-/
theorem sum_apply_le_apply_prod (h_one : 0 <= g 1) (h_mul : forall (a b : α), g a + g b <= g (a * b)) :
    ∑ x in s, g (f x) <= g (∏ x in s, f x) :=
  s.apply_prod_le_sum_apply (β := βᵒᵈ) g h_one h_mul

end ProdSum

@[to_additive]
/--
lemma `max_prod_le` / 引理 `max_prod_le`

English:
lemma max_prod_le
  given: [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι -> M} {s : Finset ι}
  proof: Multiset.max_prod_le

@[to_additive]

中文:
引理 max_prod_le
  条件: [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι -> M} {s : Finset ι}
  证明: Multiset.max_prod_le

@[to_additive]

Depends on / 依赖: Multiset, Multiset.max_prod_le, max_prod_le
-/
lemma max_prod_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι -> M} {s : Finset ι} :
    max (s.prod f) (s.prod g) <= s.prod (fun i => max (f i) (g i)) :=
  Multiset.max_prod_le

@[to_additive]
/--
lemma `prod_min_le` / 引理 `prod_min_le`

English:
lemma prod_min_le
  given: [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι -> M} {s : Finset ι}
  proof: Multiset.prod_min_le

中文:
引理 prod_min_le
  条件: [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι -> M} {s : Finset ι}
  证明: Multiset.prod_min_le

Depends on / 依赖: Multiset, Multiset.prod_min_le, prod_min_le
-/
lemma prod_min_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι -> M} {s : Finset ι} :
    s.prod (fun i => min (f i) (g i)) <= min (s.prod f) (s.prod g) :=
  Multiset.prod_min_le

/--
theorem `abs_sum_le_sum_abs` / 定理 `abs_sum_le_sum_abs`

English:
theorem abs_sum_le_sum_abs
  statement: {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  proof: le_sum_of_subadditive _ abs_zero.le abs_add_le s f

中文:
定理 abs_sum_le_sum_abs
  结论: {G : 类型} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  证明: le_sum_of_subadditive _ abs_zero.le abs_add_le s f

Depends on / 依赖: abs_add_le, abs_zero, abs_zero.le, le_sum_of_subadditive
-/
theorem abs_sum_le_sum_abs {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (f : ι -> G) (s : Finset ι) :
    |∑ i in s, f i| <= ∑ i in s, |f i| := le_sum_of_subadditive _ abs_zero.le abs_add_le s f

/--
theorem `abs_sum_of_nonneg` / 定理 `abs_sum_of_nonneg`

English:
theorem abs_sum_of_nonneg
  statement: {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
  proof: by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]

中文:
定理 abs_sum_of_nonneg
  结论: {G : 类型} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
  证明: by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]

Depends on / 依赖: Finset, Finset.sum_nonneg, abs_of_nonneg, sum_nonneg
-/
theorem abs_sum_of_nonneg {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
    {f : ι -> G} {s : Finset ι}
    (hf : forall i in s, 0 <= f i) : |∑ i in s, f i| = ∑ i in s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]

/--
theorem `abs_sum_of_nonneg'` / 定理 `abs_sum_of_nonneg'`

English:
theorem abs_sum_of_nonneg'
  statement: {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
  proof: by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]

中文:
定理 abs_sum_of_nonneg'
  结论: {G : 类型} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
  证明: by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]

Depends on / 依赖: Finset, Finset.sum_nonneg, abs_of_nonneg, sum_nonneg
-/
theorem abs_sum_of_nonneg' {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
    {f : ι -> G} {s : Finset ι}
    (hf : forall i, 0 <= f i) : |∑ i in s, f i| = ∑ i in s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]

section CommMonoid
variable [CommMonoid α] [LE α] [MulLeftMono α] {s : Finset ι} {f : ι -> α}

@[to_additive (attr := simp)]
/--
lemma `mulLECancellable_prod` / 引理 `mulLECancellable_prod`

English:
lemma mulLECancellable_prod
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

中文:
引理 mulLECancellable_prod
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma mulLECancellable_prod :
    MulLECancellable (∏ i in s, f i) ↔ forall ⦃i⦄, i in s -> MulLECancellable (f i) := by
  induction s using Finset.cons_induction <;> simp [*]

end CommMonoid

section Pigeonhole

variable [DecidableEq β]

/--
theorem `card_le_mul_card_image_of_maps_to` / 定理 `card_le_mul_card_image_of_maps_to`

English:
theorem card_le_mul_card_image_of_maps_to
  statement: {f : α -> β} {s : Finset α} {t : Finset β}
  proof: calc
    #s = ∑ b in t, #{a in s | f a = b} := card_eq_sum_card_fiberwise Hf
    _ <= ∑ _b in t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]

中文:
定理 card_le_mul_card_image_of_maps_to
  结论: {f : α -> β} {s : Finset α} {t : Finset β}
  证明: calc
    #s = ∑ b in t, #{a in s | f a = b} := card_eq_sum_card_fiberwise Hf
    _ <= ∑ _b in t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]

Depends on / 依赖: card_eq_sum_card_fiberwise, mul_comm, sum_le_sum
-/
theorem card_le_mul_card_image_of_maps_to {f : α -> β} {s : Finset α} {t : Finset β}
    (Hf : forall a in s, f a in t) (n : Nat) (hn : forall b in t, #{a in s | f a = b} <= n) : #s <= n * #t :=
  calc
    #s = ∑ b in t, #{a in s | f a = b} := card_eq_sum_card_fiberwise Hf
    _ <= ∑ _b in t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]

/--
theorem `card_le_mul_card_image` / 定理 `card_le_mul_card_image`

English:
theorem card_le_mul_card_image
  statement: {f : α -> β} (s : Finset α) (n : Nat)
  proof: card_le_mul_card_image_of_maps_to (fun _ => mem_image_of_mem _) n hn

中文:
定理 card_le_mul_card_image
  结论: {f : α -> β} (s : Finset α) (n : 自然数)
  证明: card_le_mul_card_image_of_maps_to (fun _ => mem_image_of_mem _) n hn

Depends on / 依赖: card_le_mul_card_image_of_maps_to, mem_image_of_mem
-/
theorem card_le_mul_card_image {f : α -> β} (s : Finset α) (n : Nat)
    (hn : forall b in s.image f, #{a in s | f a = b} <= n) : #s <= n * #(s.image f) :=
  card_le_mul_card_image_of_maps_to (fun _ => mem_image_of_mem _) n hn

/--
theorem `mul_card_image_le_card_of_maps_to` / 定理 `mul_card_image_le_card_of_maps_to`

English:
theorem mul_card_image_le_card_of_maps_to
  statement: {f : α -> β} {s : Finset α} {t : Finset β}
  proof: calc
    n * #t = ∑ _a in t, n := by simp [mul_comm]
    _ <= ∑ b in t, #{a in s | f a = b} := sum_le_sum hn
    _ = #s := by rw [← card_eq_sum_card_fiberwise Hf]

中文:
定理 mul_card_image_le_card_of_maps_to
  结论: {f : α -> β} {s : Finset α} {t : Finset β}
  证明: calc
    n * #t = ∑ _a in t, n := by simp [mul_comm]
    _ <= ∑ b in t, #{a in s | f a = b} := sum_le_sum hn
    _ = #s := by rw [← card_eq_sum_card_fiberwise Hf]

Depends on / 依赖: card_eq_sum_card_fiberwise, mul_comm, sum_le_sum
-/
theorem mul_card_image_le_card_of_maps_to {f : α -> β} {s : Finset α} {t : Finset β}
    (Hf : forall a in s, f a in t) (n : Nat) (hn : forall b in t, n <= #{a in s | f a = b}) :
    n * #t <= #s :=
  calc
    n * #t = ∑ _a in t, n := by simp [mul_comm]
    _ <= ∑ b in t, #{a in s | f a = b} := sum_le_sum hn
    _ = #s := by rw [← card_eq_sum_card_fiberwise Hf]

/--
theorem `mul_card_image_le_card` / 定理 `mul_card_image_le_card`

English:
theorem mul_card_image_le_card
  statement: {f : α -> β} (s : Finset α) (n : Nat)
  proof: mul_card_image_le_card_of_maps_to (fun _ => mem_image_of_mem _) n hn

中文:
定理 mul_card_image_le_card
  结论: {f : α -> β} (s : Finset α) (n : 自然数)
  证明: mul_card_image_le_card_of_maps_to (fun _ => mem_image_of_mem _) n hn

Depends on / 依赖: mem_image_of_mem, mul_card_image_le_card_of_maps_to
-/
theorem mul_card_image_le_card {f : α -> β} (s : Finset α) (n : Nat)
    (hn : forall b in s.image f, n <= #{a in s | f a = b}) : n * #(s.image f) <= #s :=
  mul_card_image_le_card_of_maps_to (fun _ => mem_image_of_mem _) n hn

end Pigeonhole

section DoubleCounting

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : Nat}

/--
theorem `sum_card_inter_le` / 定理 `sum_card_inter_le`

English:
theorem sum_card_inter_le
  given: (h : forall a in s, #{b in B | a in b} <= n)
  statement: (∑ t in B, #(s inter t)) <= #s * n
  proof: by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

中文:
定理 sum_card_inter_le
  条件: (h : 对任意 a in s, #{b in B | a in b} <= n)
  结论: (∑ t in B, #(s inter t)) <= #s * n
  证明: by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

Depends on / 依赖: card_eq_sum_ones, filter_mem_eq_inter, le_trans, s.sum_le_card_nsmul, simp_rw, sum_comm, sum_comm.le, sum_filter, sum_le_card_nsmul
-/
theorem sum_card_inter_le (h : forall a in s, #{b in B | a in b} <= n) : (∑ t in B, #(s inter t)) <= #s * n := by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

/--
lemma `sum_card_le` / 引理 `sum_card_le`

English:
lemma sum_card_le
  given: [Fintype α] (h : forall a, #{b in B | a in b} <= n)
  statement: ∑ s in B, #s <= Fintype.card α * n
  proof: calc
    ∑ s in B, #s = ∑ s in B, #(univ inter s) := by simp_rw [univ_inter]
    _ <= Fintype.card α * n := sum_card_inter_le fun a _ => h a

中文:
引理 sum_card_le
  条件: [Fintype α] (h : 对任意 a, #{b in B | a in b} <= n)
  结论: ∑ s in B, #s <= Fintype.card α * n
  证明: calc
    ∑ s in B, #s = ∑ s in B, #(univ inter s) := by simp_rw [univ_inter]
    _ <= Fintype.card α * n := sum_card_inter_le fun a _ => h a

Depends on / 依赖: Fintype, Fintype.card, simp_rw, sum_card_inter_le, univ_inter
-/
lemma sum_card_le [Fintype α] (h : forall a, #{b in B | a in b} <= n) : ∑ s in B, #s <= Fintype.card α * n :=
  calc
    ∑ s in B, #s = ∑ s in B, #(univ inter s) := by simp_rw [univ_inter]
    _ <= Fintype.card α * n := sum_card_inter_le fun a _ => h a

/--
theorem `le_sum_card_inter` / 定理 `le_sum_card_inter`

English:
theorem le_sum_card_inter
  given: (h : forall a in s, n <= #{b in B | a in b})
  statement: #s * n <= ∑ t in B, #(s inter t)
  proof: by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

中文:
定理 le_sum_card_inter
  条件: (h : 对任意 a in s, n <= #{b in B | a in b})
  结论: #s * n <= ∑ t in B, #(s inter t)
  证明: by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

Depends on / 依赖: card_eq_sum_ones, card_nsmul_le_sum, filter_mem_eq_inter, s.card_nsmul_le_sum, simp_rw, sum_comm, sum_comm.le, sum_filter
-/
theorem le_sum_card_inter (h : forall a in s, n <= #{b in B | a in b}) : #s * n <= ∑ t in B, #(s inter t) := by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

/--
theorem `le_sum_card` / 定理 `le_sum_card`

English:
theorem le_sum_card
  given: [Fintype α] (h : forall a, n <= #{b in B | a in b})
  proof: calc
    Fintype.card α * n <= ∑ s in B, #(univ inter s) := le_sum_card_inter fun a _ => h a
    _ = ∑ s in B, #s := by simp_rw [univ_inter]

中文:
定理 le_sum_card
  条件: [Fintype α] (h : 对任意 a, n <= #{b in B | a in b})
  证明: calc
    Fintype.card α * n <= ∑ s in B, #(univ inter s) := le_sum_card_inter fun a _ => h a
    _ = ∑ s in B, #s := by simp_rw [univ_inter]

Depends on / 依赖: Fintype, Fintype.card, le_sum_card_inter, simp_rw, univ_inter
-/
theorem le_sum_card [Fintype α] (h : forall a, n <= #{b in B | a in b}) :
    Fintype.card α * n <= ∑ s in B, #s :=
  calc
    Fintype.card α * n <= ∑ s in B, #(univ inter s) := le_sum_card_inter fun a _ => h a
    _ = ∑ s in B, #s := by simp_rw [univ_inter]

/--
theorem `sum_card_inter` / 定理 `sum_card_inter`

English:
theorem sum_card_inter
  given: (h : forall a in s, #{b in B | a in b} = n)
  proof: (sum_card_inter_le fun a ha => (h a ha).le).antisymm (le_sum_card_inter fun a ha => (h a ha).ge)

中文:
定理 sum_card_inter
  条件: (h : 对任意 a in s, #{b in B | a in b} = n)
  证明: (sum_card_inter_le fun a ha => (h a ha).le).antisymm (le_sum_card_inter fun a ha => (h a ha).ge)

Depends on / 依赖: antisymm, le_sum_card_inter, sum_card_inter_le
-/
theorem sum_card_inter (h : forall a in s, #{b in B | a in b} = n) :
    (∑ t in B, #(s inter t)) = #s * n :=
  (sum_card_inter_le fun a ha => (h a ha).le).antisymm (le_sum_card_inter fun a ha => (h a ha).ge)

/--
theorem `sum_card` / 定理 `sum_card`

English:
theorem sum_card
  given: [Fintype α] (h : forall a, #{b in B | a in b} = n)
  proof: by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ => h a, univ_inter]

中文:
定理 sum_card
  条件: [Fintype α] (h : 对任意 a, #{b in B | a in b} = n)
  证明: by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ => h a, univ_inter]

Depends on / 依赖: Fintype, Fintype.card, simp_rw, sum_card_inter, univ_inter
-/
theorem sum_card [Fintype α] (h : forall a, #{b in B | a in b} = n) :
    ∑ s in B, #s = Fintype.card α * n := by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ => h a, univ_inter]

/--
theorem `card_le_card_biUnion` / 定理 `card_le_card_biUnion`

English:
theorem card_le_card_biUnion
  statement: {s : Finset ι} {f : ι -> Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
  proof: by
  rw [card_biUnion hs]; rw [card_eq_sum_ones]
  exact sum_le_sum fun i hi => (hf i hi).card_pos

中文:
定理 card_le_card_biUnion
  结论: {s : Finset ι} {f : ι -> Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
  证明: by
  rw [card_biUnion hs]; rw [card_eq_sum_ones]
  exact sum_le_sum fun i hi => (hf i hi).card_pos

Depends on / 依赖: card_biUnion, card_eq_sum_ones, card_pos, sum_le_sum
-/
theorem card_le_card_biUnion {s : Finset ι} {f : ι -> Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
    (hf : forall i in s, (f i).Nonempty) : #s <= #(s.biUnion f) := by
  rw [card_biUnion hs]; rw [card_eq_sum_ones]
  exact sum_le_sum fun i hi => (hf i hi).card_pos

/--
theorem `card_le_card_biUnion_add_card_fiber` / 定理 `card_le_card_biUnion_add_card_fiber`

English:
theorem card_le_card_biUnion_add_card_fiber
  statement: {s : Finset ι} {f : ι -> Finset α}
  proof: by
  rw [← Finset.card_filter_add_card_filter_not fun i => f i = ∅]; rw [add_comm]
  grw [card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi =>
    nonempty_of_ne_empty (mem_filter.1 hi).2, filter_subset]

中文:
定理 card_le_card_biUnion_add_card_fiber
  结论: {s : Finset ι} {f : ι -> Finset α}
  证明: by
  rw [← Finset.card_filter_add_card_filter_not fun i => f i = ∅]; rw [add_comm]
  grw [card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi =>
    nonempty_of_ne_empty (mem_filter.1 hi).2, filter_subset]

Depends on / 依赖: Finset, Finset.card_filter_add_card_filter_not, add_comm, card_filter_add_card_filter_not, card_le_card_biUnion, filter_subset, hs.subset, mem_filter, nonempty_of_ne_empty, subset
-/
theorem card_le_card_biUnion_add_card_fiber {s : Finset ι} {f : ι -> Finset α}
    (hs : (s : Set ι).PairwiseDisjoint f) : #s <= #(s.biUnion f) + #{i in s | f i = ∅} := by
  rw [← Finset.card_filter_add_card_filter_not fun i => f i = ∅]; rw [add_comm]
  grw [card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi =>
    nonempty_of_ne_empty (mem_filter.1 hi).2, filter_subset]

/--
theorem `card_le_card_biUnion_add_one` / 定理 `card_le_card_biUnion_add_one`

English:
theorem card_le_card_biUnion_add_one
  statement: {s : Finset ι} {f : ι -> Finset α} (hf : Injective f)
  proof: by
  grw [card_le_card_biUnion_add_card_fiber hs,
card_le_one.2 fun _ hi _ hj => hf (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm]

中文:
定理 card_le_card_biUnion_add_one
  结论: {s : Finset ι} {f : ι -> Finset α} (hf : Injective f)
  证明: by
  grw [card_le_card_biUnion_add_card_fiber hs,
card_le_one.2 fun _ hi _ hj => hf (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm]

Depends on / 依赖: card_le_card_biUnion_add_card_fiber, card_le_one, mem_filter
-/
theorem card_le_card_biUnion_add_one {s : Finset ι} {f : ι -> Finset α} (hf : Injective f)
    (hs : (s : Set ι).PairwiseDisjoint f) : #s <= #(s.biUnion f) + 1 := by
  grw [card_le_card_biUnion_add_card_fiber hs,
card_le_one.2 fun _ hi _ hj => hf (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm]

end DoubleCounting

section CanonicallyOrderedMul

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι -> M} {s t : Finset ι}

/-- In a canonically-ordered monoid, a product bounds each of its terms.

See also `Finset.single_le_prod'`. -/
@[to_additive /-- In a canonically-ordered additive monoid, a sum bounds each of its terms.

See also `Finset.single_le_sum`. -/]
/--
lemma `single_le_prod_of_canonicallyOrdered` / 引理 `single_le_prod_of_canonicallyOrdered`

English:
lemma single_le_prod_of_canonicallyOrdered
  given: {i : ι} (hi : i in s)
  proof: have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  single_le_prod' (fun _ _ => one_le) hi

@[to_additive sum_le_sum_of_subset]

中文:
引理 single_le_prod_of_canonicallyOrdered
  条件: {i : ι} (hi : i in s)
  证明: have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  single_le_prod' (fun _ _ => one_le) hi

@[to_additive sum_le_sum_of_subset]

Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.toIsOrderedMonoid, one_le, single_le_prod, toIsOrderedMonoid
-/
lemma single_le_prod_of_canonicallyOrdered {i : ι} (hi : i in s) :
    f i <= ∏ j in s, f j :=
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  single_le_prod' (fun _ _ => one_le) hi

@[to_additive sum_le_sum_of_subset]
/--
theorem `prod_le_prod_of_subset'` / 定理 `prod_le_prod_of_subset'`

English:
theorem prod_le_prod_of_subset'
  given: (h : s subseteq t)
  statement: ∏ x in s, f x <= ∏ x in t, f x
  proof: have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ => one_le

@[to_additive sum_mono_set]

中文:
定理 prod_le_prod_of_subset'
  条件: (h : s subseteq t)
  结论: ∏ x in s, f x <= ∏ x in t, f x
  证明: have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ => one_le

@[to_additive sum_mono_set]

Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.toIsOrderedMonoid, one_le, prod_le_prod_of_subset_of_one_le, toIsOrderedMonoid
-/
theorem prod_le_prod_of_subset' (h : s subseteq t) : ∏ x in s, f x <= ∏ x in t, f x :=
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ => one_le

@[to_additive sum_mono_set]
/--
theorem `prod_mono_set'` / 定理 `prod_mono_set'`

English:
theorem prod_mono_set'
  given: (f : ι -> M)
  statement: Monotone fun s => ∏ x in s, f x
  proof: fun _ _ hs =>
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset' hs

@[to_additive sum_le_sum_of_ne_zero]

中文:
定理 prod_mono_set'
  条件: (f : ι -> M)
  结论: Monotone fun s => ∏ x in s, f x
  证明: fun _ _ hs =>
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset' hs

@[to_additive sum_le_sum_of_ne_zero]
-/
theorem prod_mono_set' (f : ι -> M) : Monotone fun s => ∏ x in s, f x := fun _ _ hs =>
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset' hs

@[to_additive sum_le_sum_of_ne_zero]
/--
theorem `prod_le_prod_of_ne_one'` / 定理 `prod_le_prod_of_ne_one'`

English:
theorem prod_le_prod_of_ne_one'
  given: (h : forall x in s, f x != 1 -> x in t)
  proof: by
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  classical calc
    ∏ x in s, f x = (∏ x in s with f x = 1, f x) * ∏ x in s with f x != 1, f x := by
      rw [← prod_union]; rw [filter_union_filter_not_eq]
      exact disjoint_filter.2 fun _ _ h n_h => n_h h
    _ <= ∏ x in t, f x :=


中文:
定理 prod_le_prod_of_ne_one'
  条件: (h : 对任意 x in s, f x != 1 -> x in t)
  证明: by
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  classical calc
    ∏ x in s, f x = (∏ x in s with f x = 1, f x) * ∏ x in s with f x != 1, f x := by
      rw [← prod_union]; rw [filter_union_filter_not_eq]
      exact disjoint_filter.2 fun _ _ h n_h => n_h h
    _ <= ∏ x in t, f x :=


Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.toIsOrderedMonoid, and_imp, classical, disjoint_filter, filter_union_filter_not_eq, le_of_eq, mem_filter, mul_le_of_le_one_of_le, prod_le_one, prod_le_prod_of_subset, prod_union, subset_iff, toIsOrderedMonoid
-/
theorem prod_le_prod_of_ne_one' (h : forall x in s, f x != 1 -> x in t) :
    ∏ x in s, f x <= ∏ x in t, f x := by
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  classical calc
    ∏ x in s, f x = (∏ x in s with f x = 1, f x) * ∏ x in s with f x != 1, f x := by
      rw [← prod_union]; rw [filter_union_filter_not_eq]
      exact disjoint_filter.2 fun _ _ h n_h => n_h h
    _ <= ∏ x in t, f x :=
      mul_le_of_le_one_of_le
        (prod_le_one' <| by simp only [mem_filter, and_imp]; exact fun _ _ => le_of_eq)
        (prod_le_prod_of_subset' <| by simpa only [subset_iff, mem_filter, and_imp])

@[to_additive sum_pos_iff]
/--
lemma `one_lt_prod_iff` / 引理 `one_lt_prod_iff`

English:
lemma one_lt_prod_iff
  statement: {ι M : Type*} [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M]
  proof: have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
Finset.one_lt_prod_iff_of_one_le fun _ _ => one_le

中文:
引理 one_lt_prod_iff
  结论: {ι M : 类型} [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M]
  证明: have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
Finset.one_lt_prod_iff_of_one_le fun _ _ => one_le

Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.toIsOrderedMonoid, Finset, Finset.one_lt_prod_iff_of_one_le, one_le, one_lt_prod_iff_of_one_le, toIsOrderedMonoid
-/
lemma one_lt_prod_iff {ι M : Type*} [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M]
    {f : ι -> M} {s : Finset ι} : 1 < ∏ x in s, f x ↔ exists x in s, 1 < f x :=
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
Finset.one_lt_prod_iff_of_one_le fun _ _ => one_le

/-- In a canonically-ordered monoid, if `S'` is contained in `(S.erase d) ∪ {d'}` and
`f d' < f d` for some `d ∈ S`, then the product of `f` over `S'` is strictly less than over `S`. -/
@[to_additive /-- In a canonically-ordered additive monoid, if `S'` is contained in
`(S.erase d) ∪ {d'}` and `f d' < f d` for some `d ∈ S`, then the sum of `f` over `S'` is
strictly less than over `S`. -/]
/--
lemma `prod_lt_prod_of_subset_erase_union_singleton` / 引理 `prod_lt_prod_of_subset_erase_union_singleton`

English:
lemma prod_lt_prod_of_subset_erase_union_singleton
  statement: {ι M : Type*} [DecidableEq ι] [CommMonoid M]
  proof: by
  have hd_not : d ∉ S' := fun hd => (Finset.mem_union.mp (hS' hd)).elim
    (fun h => (Finset.mem_erase.mp h).1 rfl)
    (fun h => hlt.ne' (congrArg f (Finset.mem_singleton.mp h)))
  by_cases hd'S : d' in S
  · calc ∏ x in S', f x
        <= ∏ x in S.erase d, f x := Finset.prod_le_prod_of_subset'

中文:
引理 prod_lt_prod_of_subset_erase_union_singleton
  结论: {ι M : 类型} [DecidableEq ι] [CommMonoid M]
  证明: by
  have hd_not : d ∉ S' := fun hd => (Finset.mem_union.mp (hS' hd)).elim
    (fun h => (Finset.mem_erase.mp h).1 rfl)
    (fun h => hlt.ne' (congrArg f (Finset.mem_singleton.mp h)))
  by_cases hd'S : d' in S
  · calc ∏ x in S', f x
        <= ∏ x in S.erase d, f x := Finset.prod_le_prod_of_subset'

Depends on / 依赖: Finset, Finset.mem_erase.mp, Finset.mem_erase.mpr, Finset.mem_of_mem_erase, Finset.mem_singleton.mp, Finset.mem_union.mp, Finset.prod_le_prod_of_subset, S.erase, hd_not, hlt.ne, mem_erase, mem_of_mem_erase, mem_singleton, mem_union, prod_le_prod_of_subset
-/
lemma prod_lt_prod_of_subset_erase_union_singleton {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    [PartialOrder M] [CanonicallyOrderedMul M] [MulLeftStrictMono M] {S S' : Finset ι} {f : ι -> M}
    {d d' : ι} (hd_mem : d in S) (hS' : S' subseteq S.erase d union {d'}) (hlt : f d' < f d) :
    ∏ x in S', f x < ∏ x in S, f x := by
  have hd_not : d ∉ S' := fun hd => (Finset.mem_union.mp (hS' hd)).elim
    (fun h => (Finset.mem_erase.mp h).1 rfl)
    (fun h => hlt.ne' (congrArg f (Finset.mem_singleton.mp h)))
  by_cases hd'S : d' in S
  · calc ∏ x in S', f x
        <= ∏ x in S.erase d, f x := Finset.prod_le_prod_of_subset' (fun x hx =>
          Finset.mem_erase.mpr ⟨fun h => hd_not (h ▸ hx),
            match Finset.mem_union.mp (hS' hx) with
            | .inl h => Finset.mem_of_mem_erase h
            | .inr h => Finset.mem_singleton.mp h ▸ hd'S⟩)
      _ < (∏ x in S.erase d, f x) * f d :=
          lt_mul_of_one_lt_right' _ (one_le.trans_lt hlt)
      _ = ∏ x in S, f x := Finset.prod_erase_mul S f hd_mem
  · calc ∏ x in S', f x
        <= ∏ x in S.erase d union {d'}, f x := Finset.prod_le_prod_of_subset' hS'
      _ = (∏ x in S.erase d, f x) * f d' := by
          rw [Finset.prod_union (Finset.disjoint_singleton_right.mpr
            (fun h => hd'S (Finset.mem_of_mem_erase h)))]; rw [Finset.prod_singleton]
      _ < (∏ x in S.erase d, f x) * f d := mul_lt_mul_right hlt _
      _ = ∏ x in S, f x := Finset.prod_erase_mul S f hd_mem

end CanonicallyOrderedMul

section OrderedCancelCommMonoid

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι -> M} {s t : Finset ι}

@[to_additive sum_lt_sum]
/--
theorem `prod_lt_prod'` / 定理 `prod_lt_prod'`

English:
theorem prod_lt_prod'
  given: [MulLeftStrictMono M] (hle : forall i in s, f i <= g i) (hlt : exists i in s, f i < g i)
  proof: Multiset.prod_lt_prod' hle hlt

中文:
定理 prod_lt_prod'
  条件: [MulLeftStrictMono M] (hle : 对任意 i in s, f i <= g i) (hlt : 存在 i in s, f i < g i)
  证明: Multiset.prod_lt_prod' hle hlt

Depends on / 依赖: Multiset, Multiset.prod_lt_prod, prod_lt_prod
-/
theorem prod_lt_prod' [MulLeftStrictMono M] (hle : forall i in s, f i <= g i) (hlt : exists i in s, f i < g i) :
    ∏ i in s, f i < ∏ i in s, g i :=
  Multiset.prod_lt_prod' hle hlt

/-- In an ordered commutative monoid, if each factor `f i` of one nontrivial finite product is
strictly less than the corresponding factor `g i` of another nontrivial finite product, then
`s.prod f < s.prod g`. -/
@[to_additive (attr := gcongr) sum_lt_sum_of_nonempty]
/--
theorem `prod_lt_prod_of_nonempty'` / 定理 `prod_lt_prod_of_nonempty'`

English:
theorem prod_lt_prod_of_nonempty'
  statement: [MulLeftStrictMono M] (hs : s.Nonempty)
  proof: Multiset.prod_lt_prod_of_nonempty' (by aesop) hlt

中文:
定理 prod_lt_prod_of_nonempty'
  结论: [MulLeftStrictMono M] (hs : s.Nonempty)
  证明: Multiset.prod_lt_prod_of_nonempty' (by aesop) hlt

Depends on / 依赖: Multiset, Multiset.prod_lt_prod_of_nonempty, prod_lt_prod_of_nonempty
-/
theorem prod_lt_prod_of_nonempty' [MulLeftStrictMono M] (hs : s.Nonempty)
  (hlt : forall i in s, f i < g i) :
    ∏ i in s, f i < ∏ i in s, g i :=
  Multiset.prod_lt_prod_of_nonempty' (by aesop) hlt

/-- In an ordered additive commutative monoid, if each summand `f i` of one nontrivial finite sum is
strictly less than the corresponding summand `g i` of another nontrivial finite sum, then
`s.sum f < s.sum g`. -/
add_decl_doc sum_lt_sum_of_nonempty

@[to_additive sum_lt_sum_of_subset]
/--
theorem `prod_lt_prod_of_subset'` / 定理 `prod_lt_prod_of_subset'`

English:
theorem prod_lt_prod_of_subset'
  statement: [MulLeftStrictMono M] (h : s subseteq t) {i : ι} (ht : i in t)
  proof: by
  classical calc
    ∏ j in s, f j < ∏ j in insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j in s, f j) hlt
    _ <= ∏ j in t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
     

中文:
定理 prod_lt_prod_of_subset'
  结论: [MulLeftStrictMono M] (h : s subseteq t) {i : ι} (ht : i in t)
  证明: by
  classical calc
    ∏ j in s, f j < ∏ j in insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j in s, f j) hlt
    _ <= ∏ j in t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
     

Depends on / 依赖: Finset, Finset.insert_subset_iff, classical, insert, insert_subset_iff, lt_mul_of_one_lt_left, mem_insert, not_or, prod_insert, prod_le_prod_of_subset_of_one_le
-/
theorem prod_lt_prod_of_subset' [MulLeftStrictMono M] (h : s subseteq t) {i : ι} (ht : i in t)
  (hs : i ∉ s) (hlt : 1 < f i)
    (hle : forall j in t, j ∉ s -> 1 <= f j) : ∏ j in s, f j < ∏ j in t, f j := by
  classical calc
    ∏ j in s, f j < ∏ j in insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j in s, f j) hlt
    _ <= ∏ j in t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
        simp only [mem_insert, not_or] at h'x
        exact hle x hx h'x.2

@[to_additive single_lt_sum]
/--
theorem `single_lt_prod'` / 定理 `single_lt_prod'`

English:
theorem single_lt_prod'
  statement: [MulLeftStrictMono M] {i j : ι} (hij : j != i) (hi : i in s) (hj : j in s)
  proof: calc
    f i = ∏ k in {i}, f k := by rw [prod_singleton]
    _ < ∏ k in s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki => hle k hks (mt mem_singleton.2 hki)

@[to_additive sum_pos]

中文:
定理 single_lt_prod'
  结论: [MulLeftStrictMono M] {i j : ι} (hij : j != i) (hi : i in s) (hj : j in s)
  证明: calc
    f i = ∏ k in {i}, f k := by rw [prod_singleton]
    _ < ∏ k in s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki => hle k hks (mt mem_singleton.2 hki)

@[to_additive sum_pos]

Depends on / 依赖: mem_singleton, prod_lt_prod_of_subset, prod_singleton, singleton_subset_iff
-/
theorem single_lt_prod' [MulLeftStrictMono M] {i j : ι} (hij : j != i) (hi : i in s) (hj : j in s)
    (hlt : 1 < f j) (hle : forall k in s, k != i -> 1 <= f k) : f i < ∏ k in s, f k :=
  calc
    f i = ∏ k in {i}, f k := by rw [prod_singleton]
    _ < ∏ k in s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki => hle k hks (mt mem_singleton.2 hki)

@[to_additive sum_pos]
/--
theorem `one_lt_prod` / 定理 `one_lt_prod`

English:
theorem one_lt_prod
  given: [MulLeftStrictMono M] (h : forall i in s, 1 < f i) (hs : s.Nonempty)
  proof: lt_of_le_of_lt (by rw [prod_const_one]) prod_lt_prod_of_nonempty' hs h

@[to_additive]

中文:
定理 one_lt_prod
  条件: [MulLeftStrictMono M] (h : 对任意 i in s, 1 < f i) (hs : s.Nonempty)
  证明: lt_of_le_of_lt (by rw [prod_const_one]) prod_lt_prod_of_nonempty' hs h

@[to_additive]

Depends on / 依赖: lt_of_le_of_lt, prod_const_one, prod_lt_prod_of_nonempty
-/
theorem one_lt_prod [MulLeftStrictMono M] (h : forall i in s, 1 < f i) (hs : s.Nonempty) :
    1 < ∏ i in s, f i :=
lt_of_le_of_lt (by rw [prod_const_one]) prod_lt_prod_of_nonempty' hs h

@[to_additive]
/--
theorem `prod_lt_one` / 定理 `prod_lt_one`

English:
theorem prod_lt_one
  given: [MulLeftStrictMono M] (h : forall i in s, f i < 1) (hs : s.Nonempty)
  proof: (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])

@[to_additive sum_pos']

中文:
定理 prod_lt_one
  条件: [MulLeftStrictMono M] (h : 对任意 i in s, f i < 1) (hs : s.Nonempty)
  证明: (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])

@[to_additive sum_pos']

Depends on / 依赖: prod_const_one, prod_lt_prod_of_nonempty, trans_le
-/
theorem prod_lt_one [MulLeftStrictMono M] (h : forall i in s, f i < 1) (hs : s.Nonempty) :
    ∏ i in s, f i < 1 :=
  (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])

@[to_additive sum_pos']
/--
theorem `one_lt_prod'` / 定理 `one_lt_prod'`

English:
theorem one_lt_prod'
  given: [MulLeftStrictMono M] (h : forall i in s, 1 <= f i) (hs : exists i in s, 1 < f i)
  proof: prod_const_one.symm.trans_lt prod_lt_prod' h hs

@[to_additive]

中文:
定理 one_lt_prod'
  条件: [MulLeftStrictMono M] (h : 对任意 i in s, 1 <= f i) (hs : 存在 i in s, 1 < f i)
  证明: prod_const_one.symm.trans_lt prod_lt_prod' h hs

@[to_additive]

Depends on / 依赖: prod_const_one, prod_const_one.symm.trans_lt, prod_lt_prod, trans_lt
-/
theorem one_lt_prod' [MulLeftStrictMono M] (h : forall i in s, 1 <= f i) (hs : exists i in s, 1 < f i) :
    1 < ∏ i in s, f i :=
prod_const_one.symm.trans_lt prod_lt_prod' h hs

@[to_additive]
/--
theorem `prod_lt_one'` / 定理 `prod_lt_one'`

English:
theorem prod_lt_one'
  given: [MulLeftStrictMono M] (h : forall i in s, f i <= 1) (hs : exists i in s, f i < 1)
  proof: prod_const_one.le.trans_lt' prod_lt_prod' h hs

@[to_additive]

中文:
定理 prod_lt_one'
  条件: [MulLeftStrictMono M] (h : 对任意 i in s, f i <= 1) (hs : 存在 i in s, f i < 1)
  证明: prod_const_one.le.trans_lt' prod_lt_prod' h hs

@[to_additive]

Depends on / 依赖: prod_const_one, prod_const_one.le.trans_lt, prod_lt_prod, trans_lt
-/
theorem prod_lt_one' [MulLeftStrictMono M] (h : forall i in s, f i <= 1) (hs : exists i in s, f i < 1) :
    ∏ i in s, f i < 1 :=
prod_const_one.le.trans_lt' prod_lt_prod' h hs

@[to_additive]
/--
theorem `prod_eq_prod_iff_of_le` / 定理 `prod_eq_prod_iff_of_le`

English:
theorem prod_eq_prod_iff_of_le
  statement: {ι M : Type*} [CommMonoid M] [PartialOrder M]
  proof: by
  classical
    revert h
    refine Finset.induction_on s (fun _ => ⟨fun _ _ h => False.elim (Finset.notMem_empty _ h),
      fun _ => rfl⟩) fun a s ha ih H => ?_
    specialize ih fun i => H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha]; rw [Finset.prod_insert ha]; rw [Finset.foral

中文:
定理 prod_eq_prod_iff_of_le
  结论: {ι M : 类型} [CommMonoid M] [PartialOrder M]
  证明: by
  classical
    revert h
    refine Finset.induction_on s (fun _ => ⟨fun _ _ h => False.elim (Finset.notMem_empty _ h),
      fun _ => rfl⟩) fun a s ha ih H => ?_
    specialize ih fun i => H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha]; rw [Finset.prod_insert ha]; rw [Finset.foral

Depends on / 依赖: False.elim, Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.mem_insert_of_mem, Finset.notMem_empty, Finset.prod_insert, Finset.prod_le_prod, classical, forall_mem_insert, induction_on, mem_insert_of_mem, mem_insert_self, mul_eq_mul_iff_eq_and_eq, notMem_empty, prod_insert, prod_le_prod, revert, s.mem_insert_self, specialize
-/
theorem prod_eq_prod_iff_of_le {ι M : Type*} [CommMonoid M] [PartialOrder M]
  [IsOrderedCancelMonoid M] {s : Finset ι} {f g : ι -> M} (h : forall i in s, f i <= g i) :
    ((∏ i in s, f i) = ∏ i in s, g i) ↔ forall i in s, f i = g i := by
  classical
    revert h
    refine Finset.induction_on s (fun _ => ⟨fun _ _ h => False.elim (Finset.notMem_empty _ h),
      fun _ => rfl⟩) fun a s ha ih H => ?_
    specialize ih fun i => H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha]; rw [Finset.prod_insert ha]; rw [Finset.forall_mem_insert]; rw [← ih]
    exact
      mul_eq_mul_iff_eq_and_eq (H a (s.mem_insert_self a))
        (Finset.prod_le_prod' fun i => H i ∘ Finset.mem_insert_of_mem)

/--
lemma `prod_sdiff_le_prod_sdiff` / 引理 `prod_sdiff_le_prod_sdiff`

English:
lemma prod_sdiff_le_prod_sdiff
  given: [DecidableEq ι]
  proof: by
  rw [← mul_le_mul_iff_right]; rw [← prod_union (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]; rw [← prod_union]; rw [inter_comm]; rw [sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s

中文:
引理 prod_sdiff_le_prod_sdiff
  条件: [DecidableEq ι]
  证明: by
  rw [← mul_le_mul_iff_right]; rw [← prod_union (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]; rw [← prod_union]; rw [inter_comm]; rw [sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s
-/
@[to_additive] lemma prod_sdiff_le_prod_sdiff [DecidableEq ι] :
    ∏ i in s \ t, f i <= ∏ i in t \ s, f i ↔ ∏ i in s, f i <= ∏ i in t, f i := by
  rw [← mul_le_mul_iff_right]; rw [← prod_union (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]; rw [← prod_union]; rw [inter_comm]; rw [sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s

/--
lemma `prod_sdiff_lt_prod_sdiff` / 引理 `prod_sdiff_lt_prod_sdiff`

English:
lemma prod_sdiff_lt_prod_sdiff
  statement: {ι M : Type*} [CommMonoid M] [PartialOrder M]
  proof: by
  rw [← mul_lt_mul_iff_right]; rw [← prod_union (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]; rw [← prod_union]; rw [inter_comm]; rw [sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s

中文:
引理 prod_sdiff_lt_prod_sdiff
  结论: {ι M : 类型} [CommMonoid M] [PartialOrder M]
  证明: by
  rw [← mul_lt_mul_iff_right]; rw [← prod_union (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]; rw [← prod_union]; rw [inter_comm]; rw [sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s
-/
@[to_additive] lemma prod_sdiff_lt_prod_sdiff {ι M : Type*} [CommMonoid M] [PartialOrder M]
  [IsOrderedCancelMonoid M] [DecidableEq ι] {s t : Finset ι} {f : ι -> M} :
    ∏ i in s \ t, f i < ∏ i in t \ s, f i ↔ ∏ i in s, f i < ∏ i in t, f i := by
  rw [← mul_lt_mul_iff_right]; rw [← prod_union (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]; rw [← prod_union]; rw [inter_comm]; rw [sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [CommMonoid M] [LinearOrder M] {f g : ι -> M} {s t : Finset ι}

@[to_additive exists_lt_of_sum_lt]
/--
theorem `exists_lt_of_prod_lt'` / 定理 `exists_lt_of_prod_lt'`

English:
theorem exists_lt_of_prod_lt'
  given: [MulLeftMono M] (Hlt : ∏ i in s, f i < ∏ i in s, g i)
  proof: by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle

中文:
定理 exists_lt_of_prod_lt'
  条件: [MulLeftMono M] (Hlt : ∏ i in s, f i < ∏ i in s, g i)
  证明: by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle

Depends on / 依赖: contrapose, prod_le_prod
-/
theorem exists_lt_of_prod_lt' [MulLeftMono M] (Hlt : ∏ i in s, f i < ∏ i in s, g i) :
    exists i in s, f i < g i := by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle

variable [IsOrderedCancelMonoid M]

@[to_additive exists_le_of_sum_le]
/--
theorem `exists_le_of_prod_le'` / 定理 `exists_le_of_prod_le'`

English:
theorem exists_le_of_prod_le'
  given: (hs : s.Nonempty) (Hle : ∏ i in s, f i <= ∏ i in s, g i)
  proof: by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]

中文:
定理 exists_le_of_prod_le'
  条件: (hs : s.Nonempty) (Hle : ∏ i in s, f i <= ∏ i in s, g i)
  证明: by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]

Depends on / 依赖: contrapose, prod_lt_prod_of_nonempty
-/
theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i in s, f i <= ∏ i in s, g i) :
    exists i in s, f i <= g i := by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
/--
theorem `exists_one_lt_of_prod_one_of_exists_ne_one'` / 定理 `exists_one_lt_of_prod_one_of_exists_ne_one'`

English:
theorem exists_one_lt_of_prod_one_of_exists_ne_one'
  statement: (f : ι -> M) (h₁ : ∏ i in s, f i = 1)
  proof: by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : exists i in s, f i != 1 := h₂
  apply ne_of_lt
  calc
    ∏ j in s, f j < ∏ j in s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one

中文:
定理 exists_one_lt_of_prod_one_of_exists_ne_one'
  结论: (f : ι -> M) (h₁ : ∏ i in s, f i = 1)
  证明: by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : exists i in s, f i != 1 := h₂
  apply ne_of_lt
  calc
    ∏ j in s, f j < ∏ j in s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one

Depends on / 依赖: contrapose, i_ne, lt_of_ne, ne_of_lt, prod_const_one, prod_lt_prod
-/
theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι -> M) (h₁ : ∏ i in s, f i = 1)
    (h₂ : exists i in s, f i != 1) : exists i in s, 1 < f i := by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : exists i in s, f i != 1 := h₂
  apply ne_of_lt
  calc
    ∏ j in s, f j < ∏ j in s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one

end LinearOrderedCancelCommMonoid

/--
theorem `apply_sup_le_sum` / 定理 `apply_sup_le_sum`

English:
theorem apply_sup_le_sum
  statement: [SemilatticeSup α] [OrderBot α]
  proof: by
  classical
  refine t.induction_on zero.le fun i t it h => ?_
  simpa only [sup_insert, Finset.sum_insert it] using ih.trans (by gcongr)

中文:
定理 apply_sup_le_sum
  结论: [SemilatticeSup α] [OrderBot α]
  证明: by
  classical
  refine t.induction_on zero.le fun i t it h => ?_
  simpa only [sup_insert, Finset.sum_insert it] using ih.trans (by gcongr)

Depends on / 依赖: Finset, Finset.sum_insert, classical, ih.trans, induction_on, sum_insert, sup_insert, t.induction_on, zero.le
-/
theorem apply_sup_le_sum [SemilatticeSup α] [OrderBot α]
    [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : α -> β} (zero : f ⊥ = 0) (ih : forall {s t}, f (s ⊔ t) <= f s + f t)
    {s : ι -> α} (t : Finset ι) :
    f (t.sup s) <= ∑ i in t, f (s i) := by
  classical
  refine t.induction_on zero.le fun i t it h => ?_
  simpa only [sup_insert, Finset.sum_insert it] using ih.trans (by gcongr)

/--
theorem `apply_union_le_sum` / 定理 `apply_union_le_sum`

English:
theorem apply_union_le_sum
  statement: [AddCommMonoid β] [Preorder β] [AddLeftMono β]
  proof: Finset.sup_set_eq_biUnion t s ▸ t.apply_sup_le_sum zero (by simpa)

中文:
定理 apply_union_le_sum
  结论: [AddCommMonoid β] [Preorder β] [AddLeftMono β]
  证明: Finset.sup_set_eq_biUnion t s ▸ t.apply_sup_le_sum zero (by simpa)

Depends on / 依赖: Finset, Finset.sup_set_eq_biUnion, apply_sup_le_sum, sup_set_eq_biUnion, t.apply_sup_le_sum
-/
theorem apply_union_le_sum [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : Set α -> β} (zero : f ∅ = 0) (ih : forall {s t}, f (s union t) <= f s + f t)
    {s : ι -> Set α} (t : Finset ι) :
    f (⋃ i in t, s i) <= ∑ i in t, f (s i) :=
  Finset.sup_set_eq_biUnion t s ▸ t.apply_sup_le_sum zero (by simpa)

/--
theorem `sum_le_one_iff` / 定理 `sum_le_one_iff`

English:
theorem sum_le_one_iff
  given: {s : Finset α} {f : α -> Nat}
  proof: by
  classical
  refine ⟨fun h x y hsx hsy hfx hfy => ?_, fun h => ?_⟩
  · replace h := (sum_mono_set f (show {x, y} subseteq s by grind)).trans h
    grind
  · by_cases! hx : exists x in s, f x != 0
    · obtain ⟨x, hsx, hfx⟩ := hx
      have hs : forall y in s \ {x}, f y = 0 := by grind
      simp

中文:
定理 sum_le_one_iff
  条件: {s : Finset α} {f : α -> 自然数}
  证明: by
  classical
  refine ⟨fun h x y hsx hsy hfx hfy => ?_, fun h => ?_⟩
  · replace h := (sum_mono_set f (show {x, y} subseteq s by grind)).trans h
    grind
  · by_cases! hx : exists x in s, f x != 0
    · obtain ⟨x, hsx, hfx⟩ := hx
      have hs : forall y in s \ {x}, f y = 0 := by grind
      simp

Depends on / 依赖: classical, replace, singleton_subset_iff, subseteq, sum_congr, sum_mono_set, sum_sdiff
-/
theorem sum_le_one_iff {s : Finset α} {f : α -> Nat} :
    ∑ x in s, f x <= 1 ↔ forall x y, x in s -> y in s -> f x != 0 -> f y != 0 -> x = y ∧ f x = 1 := by
  classical
  refine ⟨fun h x y hsx hsy hfx hfy => ?_, fun h => ?_⟩
  · replace h := (sum_mono_set f (show {x, y} subseteq s by grind)).trans h
    grind
  · by_cases! hx : exists x in s, f x != 0
    · obtain ⟨x, hsx, hfx⟩ := hx
      have hs : forall y in s \ {x}, f y = 0 := by grind
      simp [← sum_sdiff (singleton_subset_iff.2 hsx), sum_congr rfl hs, (h x x hsx hsx hfx hfx).2]
    · simp [sum_congr rfl hx]

end Finset

namespace Fintype
section OrderedCommMonoid
variable [Fintype ι] [CommMonoid M] [Preorder M] [MulLeftMono M] {f : ι -> M}

@[to_additive (attr := mono) sum_mono]
/--
theorem `prod_mono'` / 定理 `prod_mono'`

English:
theorem prod_mono'
  statement: Monotone fun f : ι -> M => ∏ i, f i
  proof: fun _ _ hfg =>
  Finset.prod_le_prod' fun x _ => hfg x

@[to_additive sum_nonneg]

中文:
定理 prod_mono'
  结论: Monotone fun f : ι -> M => ∏ i, f i
  证明: fun _ _ hfg =>
  Finset.prod_le_prod' fun x _ => hfg x

@[to_additive sum_nonneg]
-/
theorem prod_mono' : Monotone fun f : ι -> M => ∏ i, f i := fun _ _ hfg =>
  Finset.prod_le_prod' fun x _ => hfg x

@[to_additive sum_nonneg]
/--
lemma `one_le_prod` / 引理 `one_le_prod`

English:
lemma one_le_prod
  given: (hf : 1 <= f)
  statement: 1 <= ∏ i, f i
  proof: Finset.one_le_prod' fun _ _ => hf _

中文:
引理 one_le_prod
  条件: (hf : 1 <= f)
  结论: 1 <= ∏ i, f i
  证明: Finset.one_le_prod' fun _ _ => hf _

Depends on / 依赖: Finset, Finset.one_le_prod, one_le_prod
-/
lemma one_le_prod (hf : 1 <= f) : 1 <= ∏ i, f i := Finset.one_le_prod' fun _ _ => hf _

/--
lemma `prod_le_one` / 引理 `prod_le_one`

English:
lemma prod_le_one
  given: (hf : f <= 1)
  statement: ∏ i, f i <= 1
  proof: Finset.prod_le_one' fun _ _ => hf _

@[to_additive]

中文:
引理 prod_le_one
  条件: (hf : f <= 1)
  结论: ∏ i, f i <= 1
  证明: Finset.prod_le_one' fun _ _ => hf _

@[to_additive]
-/
@[to_additive] lemma prod_le_one (hf : f <= 1) : ∏ i, f i <= 1 := Finset.prod_le_one' fun _ _ => hf _

@[to_additive]
/--
lemma `prod_eq_one_iff_of_one_le` / 引理 `prod_eq_one_iff_of_one_le`

English:
lemma prod_eq_one_iff_of_one_le
  statement: {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
  proof: (Finset.prod_eq_one_iff_of_one_le' fun i _ => hf i).trans by simp [funext_iff]

@[to_additive]

中文:
引理 prod_eq_one_iff_of_one_le
  结论: {ι M : 类型} [Fintype ι] [CommMonoid M] [PartialOrder M]
  证明: (Finset.prod_eq_one_iff_of_one_le' fun i _ => hf i).trans by simp [funext_iff]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_one_iff_of_one_le, funext_iff, prod_eq_one_iff_of_one_le
-/
lemma prod_eq_one_iff_of_one_le {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
    [MulLeftMono M] {f : ι -> M} (hf : 1 <= f) : ∏ i, f i = 1 ↔ f = 1 :=
(Finset.prod_eq_one_iff_of_one_le' fun i _ => hf i).trans by simp [funext_iff]

@[to_additive]
/--
lemma `prod_eq_one_iff_of_le_one` / 引理 `prod_eq_one_iff_of_le_one`

English:
lemma prod_eq_one_iff_of_le_one
  statement: {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
  proof: (Finset.prod_eq_one_iff_of_le_one' fun i _ => hf i).trans by simp [funext_iff]

中文:
引理 prod_eq_one_iff_of_le_one
  结论: {ι M : 类型} [Fintype ι] [CommMonoid M] [PartialOrder M]
  证明: (Finset.prod_eq_one_iff_of_le_one' fun i _ => hf i).trans by simp [funext_iff]

Depends on / 依赖: Finset, Finset.prod_eq_one_iff_of_le_one, funext_iff, prod_eq_one_iff_of_le_one
-/
lemma prod_eq_one_iff_of_le_one {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
    [MulLeftMono M] {f : ι -> M} (hf : f <= 1) : ∏ i, f i = 1 ↔ f = 1 :=
(Finset.prod_eq_one_iff_of_le_one' fun i _ => hf i).trans by simp [funext_iff]

end OrderedCommMonoid

section OrderedCancelCommMonoid
variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι -> M}

@[to_additive sum_strictMono]
/--
theorem `prod_strictMono'` / 定理 `prod_strictMono'`

English:
theorem prod_strictMono'
  statement: StrictMono fun f : ι -> M => ∏ x, f x
  proof: fun _ _ hfg =>
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ => hle i) ⟨i, Finset.mem_univ i, hlt⟩

@[to_additive sum_pos]

中文:
定理 prod_strictMono'
  结论: StrictMono fun f : ι -> M => ∏ x, f x
  证明: fun _ _ hfg =>
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ => hle i) ⟨i, Finset.mem_univ i, hlt⟩

@[to_additive sum_pos]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_lt_prod, Pi.lt_def.mp, lt_def, mem_univ, prod_lt_prod
-/
theorem prod_strictMono' : StrictMono fun f : ι -> M => ∏ x, f x :=
  fun _ _ hfg =>
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ => hle i) ⟨i, Finset.mem_univ i, hlt⟩

@[to_additive sum_pos]
/--
lemma `one_lt_prod` / 引理 `one_lt_prod`

English:
lemma one_lt_prod
  given: (hf : 1 < f)
  statement: 1 < ∏ i, f i
  proof: Finset.one_lt_prod' (fun _ _ => hf.le _) by simpa using (Pi.lt_def.1 hf).2

@[to_additive]

中文:
引理 one_lt_prod
  条件: (hf : 1 < f)
  结论: 1 < ∏ i, f i
  证明: Finset.one_lt_prod' (fun _ _ => hf.le _) by simpa using (Pi.lt_def.1 hf).2

@[to_additive]

Depends on / 依赖: Finset, Finset.one_lt_prod, Pi.lt_def, hf.le, lt_def, one_lt_prod
-/
lemma one_lt_prod (hf : 1 < f) : 1 < ∏ i, f i :=
Finset.one_lt_prod' (fun _ _ => hf.le _) by simpa using (Pi.lt_def.1 hf).2

@[to_additive]
/--
lemma `prod_lt_one` / 引理 `prod_lt_one`

English:
lemma prod_lt_one
  given: (hf : f < 1)
  statement: ∏ i, f i < 1
  proof: Finset.prod_lt_one' (fun _ _ => hf.le _) by simpa using (Pi.lt_def.1 hf).2

@[to_additive sum_pos_iff_of_nonneg]

中文:
引理 prod_lt_one
  条件: (hf : f < 1)
  结论: ∏ i, f i < 1
  证明: Finset.prod_lt_one' (fun _ _ => hf.le _) by simpa using (Pi.lt_def.1 hf).2

@[to_additive sum_pos_iff_of_nonneg]

Depends on / 依赖: Finset, Finset.prod_lt_one, Pi.lt_def, hf.le, lt_def, prod_lt_one
-/
lemma prod_lt_one (hf : f < 1) : ∏ i, f i < 1 :=
Finset.prod_lt_one' (fun _ _ => hf.le _) by simpa using (Pi.lt_def.1 hf).2

@[to_additive sum_pos_iff_of_nonneg]
/--
lemma `one_lt_prod_iff_of_one_le` / 引理 `one_lt_prod_iff_of_one_le`

English:
lemma one_lt_prod_iff_of_one_le
  given: (hf : 1 <= f)
  statement: 1 < ∏ i, f i ↔ 1 < f
  proof: by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]

@[to_additive]

中文:
引理 one_lt_prod_iff_of_one_le
  条件: (hf : 1 <= f)
  结论: 1 < ∏ i, f i ↔ 1 < f
  证明: by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]

@[to_additive]

Depends on / 依赖: eq_or_lt, hf.eq_or_lt, one_lt_prod
-/
lemma one_lt_prod_iff_of_one_le (hf : 1 <= f) : 1 < ∏ i, f i ↔ 1 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]

@[to_additive]
/--
lemma `prod_lt_one_iff_of_le_one` / 引理 `prod_lt_one_iff_of_le_one`

English:
lemma prod_lt_one_iff_of_le_one
  given: (hf : f <= 1)
  statement: ∏ i, f i < 1 ↔ f < 1
  proof: by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]

中文:
引理 prod_lt_one_iff_of_le_one
  条件: (hf : f <= 1)
  结论: ∏ i, f i < 1 ↔ f < 1
  证明: by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]

Depends on / 依赖: eq_or_lt, hf.eq_or_lt, prod_lt_one
-/
lemma prod_lt_one_iff_of_le_one (hf : f <= 1) : ∏ i, f i < 1 ↔ f < 1 := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]

end OrderedCancelCommMonoid
end Fintype

namespace Multiset

/--
theorem `finsetSum_eq_sup_iff_disjoint` / 定理 `finsetSum_eq_sup_iff_disjoint`

English:
theorem finsetSum_eq_sup_iff_disjoint
  given: [DecidableEq α] {i : Finset β} {f : β -> Multiset α}
  proof: by
  induction i using Finset.cons_induction_on with
  | empty =>
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero]
  | cons z i hz hr =>
    simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_unio

中文:
定理 finsetSum_eq_sup_iff_disjoint
  条件: [DecidableEq α] {i : Finset β} {f : β -> Multiset α}
  证明: by
  induction i using Finset.cons_induction_on with
  | empty =>
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero]
  | cons z i hz hr =>
    simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_unio

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.mem_cons, Finset.notMem_empty, Finset.sum_cons, Finset.sum_empty, Finset.sup_cons, Finset.sup_empty, IsEmpty, IsEmpty.forall_iff, Multiset, Multiset.sup_eq_union, bot_eq_zero, cons_induction_on, contextual, eq_comm, forall_and, forall_eq_or_imp, forall_iff, imp_and
-/
theorem finsetSum_eq_sup_iff_disjoint [DecidableEq α] {i : Finset β} {f : β -> Multiset α} :
    i.sum f = i.sup f ↔ forall x in i, forall y in i, x != y -> Disjoint (f x) (f y) := by
  induction i using Finset.cons_induction_on with
  | empty =>
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero]
  | cons z i hz hr =>
    simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union,
      forall_eq_or_imp, Ne, not_true_eq_false, IsEmpty.forall_iff, true_and,
      imp_and, forall_and, ← hr, @eq_comm _ z]
    have := fun x (H : x in i) => ne_of_mem_of_not_mem H hz
    simp +contextual only [this, not_false_iff, true_imp_iff]
    simp_rw [← disjoint_finsetSum_left, ← disjoint_finsetSum_right, disjoint_comm, ← and_assoc,
      and_self_iff]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))

@[deprecated (since := "2026-04-08")]
alias finset_sum_eq_sup_iff_disjoint := finsetSum_eq_sup_iff_disjoint

/--
theorem `sup_powerset_len` / 定理 `sup_powerset_len`

English:
theorem sup_powerset_len
  given: [DecidableEq α] (x : Multiset α)
  proof: by
  convert bind_powerset_len x
  rw [Multiset.bind]; rw [Multiset.join]; rw [← Finset.range_val]; rw [← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finsetSum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)

中文:
定理 sup_powerset_len
  条件: [DecidableEq α] (x : Multiset α)
  证明: by
  convert bind_powerset_len x
  rw [Multiset.bind]; rw [Multiset.join]; rw [← Finset.range_val]; rw [← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finsetSum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)

Depends on / 依赖: Eq.symm, Finset, Finset.range_val, Finset.sum_eq_multiset_sum, Multiset, Multiset.bind, Multiset.join, bind_powerset_len, convert, finsetSum_eq_sup_iff_disjoint, finsetSum_eq_sup_iff_disjoint.mpr, pairwise_disjoint_powersetCard, range_val, sum_eq_multiset_sum
-/
theorem sup_powerset_len [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset := by
  convert bind_powerset_len x
  rw [Multiset.bind]; rw [Multiset.join]; rw [← Finset.range_val]; rw [← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finsetSum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)

/--
theorem `card_le_card_toFinset_add_one_iff` / 定理 `card_le_card_toFinset_add_one_iff`

English:
theorem card_le_card_toFinset_add_one_iff
  given: [DecidableEq α] {m : Multiset α}
  proof: by
  rw [← m.toFinset_sum_count_eq]; rw [m.toFinset.card_eq_sum_ones]; rw [← tsub_le_iff_left]; rw [← Finset.sum_tsub_distrib _ (by simp [one_le_count_iff_mem]), Finset.sum_le_one_iff]
  simp only [← pos_iff_ne_zero, Nat.sub_pos_iff_lt, mem_toFinset, Nat.pred_eq_succ_iff]
  exact ⟨fun h x y hx hy =>

中文:
定理 card_le_card_toFinset_add_one_iff
  条件: [DecidableEq α] {m : Multiset α}
  证明: by
  rw [← m.toFinset_sum_count_eq]; rw [m.toFinset.card_eq_sum_ones]; rw [← tsub_le_iff_left]; rw [← Finset.sum_tsub_distrib _ (by simp [one_le_count_iff_mem]), Finset.sum_le_one_iff]
  simp only [← pos_iff_ne_zero, Nat.sub_pos_iff_lt, mem_toFinset, Nat.pred_eq_succ_iff]
  exact ⟨fun h x y hx hy =>

Depends on / 依赖: Finset, Finset.sum_le_one_iff, Finset.sum_tsub_distrib, Nat.pred_eq_succ_iff, Nat.sub_pos_iff_lt, card_eq_sum_ones, hx.le, hy.le, m.toFinset.card_eq_sum_ones, m.toFinset_sum_count_eq, mem_toFinset, one_le_count_iff_mem, one_le_count_iff_mem.mp, pos_iff_ne_zero, pred_eq_succ_iff, sub_pos_iff_lt, sum_le_one_iff, sum_tsub_distrib, toFinset, toFinset_sum_count_eq
-/
theorem card_le_card_toFinset_add_one_iff [DecidableEq α] {m : Multiset α} :
    m.card <= m.toFinset.card + 1 ↔
      forall x y, 1 < m.count x -> 1 < m.count y -> x = y ∧ m.count x = 2 := by
  rw [← m.toFinset_sum_count_eq]; rw [m.toFinset.card_eq_sum_ones]; rw [← tsub_le_iff_left]; rw [← Finset.sum_tsub_distrib _ (by simp [one_le_count_iff_mem]), Finset.sum_le_one_iff]
  simp only [← pos_iff_ne_zero, Nat.sub_pos_iff_lt, mem_toFinset, Nat.pred_eq_succ_iff]
  exact ⟨fun h x y hx hy => h x y (one_le_count_iff_mem.mp hx.le)
    (one_le_count_iff_mem.mp hy.le) hx hy, fun h x y _ _ hx hy => h x y hx hy⟩

end Multiset
