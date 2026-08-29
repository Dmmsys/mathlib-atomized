/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Kim Morrison, Eric Rodriguez
-/
module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Finset.Sort

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisfies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `Nat.count`.

## Main definitions

* `Nat.nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `Nat.nth p n = 0`.

## Main results

* `Nat.nth_eq_orderEmbOfFin`: For a finitely-often true `p`, gives the cardinality of the set of
  numbers satisfying `p` above particular values of `nth p`
* `Nat.gc_count_nth`: Establishes a Galois connection between `Nat.nth p` and `Nat.count p`.
* `Nat.nth_eq_orderIsoOfNat`: For an infinitely-often true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

## Implementation details

Much of the below was written before `Set.encard` existed and partly for this reason uses the
pattern `∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card` rather than `n < {x | p x}.encard`.
We should consider changing this.

There has been some discussion on the subject of whether both of `nth` and
`Nat.Subtype.orderIsoOfNat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

@[expose] public section


open Finset

namespace Nat

variable (p : Nat -> Prop)

/--
Definition of `nth` / `nth` 的定义

English:
definition nth
  signature: (p : Nat -> Prop) (n : Nat)
  body: by
  classical exact
    if h : Set.Finite (Set.ofPred p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (Set.ofPred p) (Set.Infinite.to_subtype h) n

中文:
定义 nth
  签名: (p : 自然数 -> 命题) (n : 自然数)
  定义体: by
  classical exact
    if h : Set.Finite (Set.ofPred p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (Set.ofPred p) (Set.Infinite.to_subtype h) n

Depends on / 依赖: Finite, Infinite, Nat.Subtype.orderIsoOfNat, Set.Finite, Set.Infinite.to_subtype, Set.ofPred, Subtype, classical, h.toFinset.sort.getD, ofPred, orderIsoOfNat, toFinset, to_subtype
-/
noncomputable def nth (p : Nat -> Prop) (n : Nat) : Nat := by
  classical exact
    if h : Set.Finite (Set.ofPred p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (Set.ofPred p) (Set.Infinite.to_subtype h) n

variable {p}



/--
theorem `nth_of_card_le` / 定理 `nth_of_card_le`

English:
theorem nth_of_card_le
  given: (hf : (Set.ofPred p).Finite) {n : Nat} (hn : #hf.toFinset <= n)
  proof: by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]

中文:
定理 nth_of_card_le
  条件: (hf : (Set.ofPred p).Finite) {n : 自然数} (hn : #hf.toFinset <= n)
  证明: by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]

Depends on / 依赖: Finset, Finset.length_sort, List.getD_eq_default, dif_pos, getD_eq_default, length_sort
-/
theorem nth_of_card_le (hf : (Set.ofPred p).Finite) {n : Nat} (hn : #hf.toFinset <= n) :
    nth p n = 0 := by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]

/--
theorem `nth_eq_getD_sort` / 定理 `nth_eq_getD_sort`

English:
theorem nth_eq_getD_sort
  given: (h : (Set.ofPred p).Finite) (n : Nat)
  proof: dif_pos h

中文:
定理 nth_eq_getD_sort
  条件: (h : (Set.ofPred p).Finite) (n : 自然数)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
theorem nth_eq_getD_sort (h : (Set.ofPred p).Finite) (n : Nat) :
    nth p n = h.toFinset.sort.getD n 0 :=
  dif_pos h

/--
theorem `nth_eq_orderEmbOfFin` / 定理 `nth_eq_orderEmbOfFin`

English:
theorem nth_eq_orderEmbOfFin
  given: (hf : (Set.ofPred p).Finite) {n : Nat} (hn : n < #hf.toFinset)
  proof: by
  rw [nth_eq_getD_sort hf]; rw [Finset.orderEmbOfFin_apply]; rw [List.getD_eq_getElem]; rw [Fin.getElem_fin]

中文:
定理 nth_eq_orderEmbOfFin
  条件: (hf : (Set.ofPred p).Finite) {n : 自然数} (hn : n < #hf.toFinset)
  证明: by
  rw [nth_eq_getD_sort hf]; rw [Finset.orderEmbOfFin_apply]; rw [List.getD_eq_getElem]; rw [Fin.getElem_fin]

Depends on / 依赖: Fin.getElem_fin, Finset, Finset.orderEmbOfFin_apply, List.getD_eq_getElem, getD_eq_getElem, getElem_fin, nth_eq_getD_sort, orderEmbOfFin_apply
-/
theorem nth_eq_orderEmbOfFin (hf : (Set.ofPred p).Finite) {n : Nat} (hn : n < #hf.toFinset) :
    nth p n = hf.toFinset.orderEmbOfFin rfl ⟨n, hn⟩ := by
  rw [nth_eq_getD_sort hf]; rw [Finset.orderEmbOfFin_apply]; rw [List.getD_eq_getElem]; rw [Fin.getElem_fin]

/--
theorem `nth_strictMonoOn` / 定理 `nth_strictMonoOn`

English:
theorem nth_strictMonoOn
  given: (hf : (Set.ofPred p).Finite)
  proof: by
  rintro m (hm : m < _) n (hn : n < _) h
  simp only [nth_eq_orderEmbOfFin, *]
  exact OrderEmbedding.strictMono _ h

中文:
定理 nth_strictMonoOn
  条件: (hf : (Set.ofPred p).Finite)
  证明: by
  rintro m (hm : m < _) n (hn : n < _) h
  simp only [nth_eq_orderEmbOfFin, *]
  exact OrderEmbedding.strictMono _ h

Depends on / 依赖: OrderEmbedding, OrderEmbedding.strictMono, nth_eq_orderEmbOfFin, strictMono
-/
theorem nth_strictMonoOn (hf : (Set.ofPred p).Finite) :
    StrictMonoOn (nth p) (Set.Iio #hf.toFinset) := by
  rintro m (hm : m < _) n (hn : n < _) h
  simp only [nth_eq_orderEmbOfFin, *]
  exact OrderEmbedding.strictMono _ h

/--
theorem `nth_lt_nth_of_lt_card` / 定理 `nth_lt_nth_of_lt_card`

English:
theorem nth_lt_nth_of_lt_card
  statement: (hf : (Set.ofPred p).Finite) {m n : Nat} (h : m < n)
  proof: nth_strictMonoOn hf (h.trans hn) hn h

中文:
定理 nth_lt_nth_of_lt_card
  结论: (hf : (Set.ofPred p).Finite) {m n : 自然数} (h : m < n)
  证明: nth_strictMonoOn hf (h.trans hn) hn h

Depends on / 依赖: h.trans, nth_strictMonoOn
-/
theorem nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : m < n)
    (hn : n < #hf.toFinset) : nth p m < nth p n :=
  nth_strictMonoOn hf (h.trans hn) hn h

/--
theorem `nth_le_nth_of_lt_card` / 定理 `nth_le_nth_of_lt_card`

English:
theorem nth_le_nth_of_lt_card
  statement: (hf : (Set.ofPred p).Finite) {m n : Nat} (h : m <= n)
  proof: (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h

中文:
定理 nth_le_nth_of_lt_card
  结论: (hf : (Set.ofPred p).Finite) {m n : 自然数} (h : m <= n)
  证明: (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h

Depends on / 依赖: h.trans_lt, monotoneOn, nth_strictMonoOn, trans_lt
-/
theorem nth_le_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : m <= n)
    (hn : n < #hf.toFinset) : nth p m <= nth p n :=
  (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h

/--
theorem `lt_of_nth_lt_nth_of_lt_card` / 定理 `lt_of_nth_lt_nth_of_lt_card`

English:
theorem lt_of_nth_lt_nth_of_lt_card
  statement: (hf : (Set.ofPred p).Finite) {m n : Nat} (h : nth p m < nth p n)
  proof: not_le.1 fun hle => h.not_ge nth_le_nth_of_lt_card hf hle hm

中文:
定理 lt_of_nth_lt_nth_of_lt_card
  结论: (hf : (Set.ofPred p).Finite) {m n : 自然数} (h : nth p m < nth p n)
  证明: not_le.1 fun hle => h.not_ge nth_le_nth_of_lt_card hf hle hm

Depends on / 依赖: h.not_ge, not_ge, not_le, nth_le_nth_of_lt_card
-/
theorem lt_of_nth_lt_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : nth p m < nth p n)
    (hm : m < #hf.toFinset) : m < n :=
not_le.1 fun hle => h.not_ge nth_le_nth_of_lt_card hf hle hm

/--
theorem `le_of_nth_le_nth_of_lt_card` / 定理 `le_of_nth_le_nth_of_lt_card`

English:
theorem le_of_nth_le_nth_of_lt_card
  statement: (hf : (Set.ofPred p).Finite) {m n : Nat} (h : nth p m <= nth p n)
  proof: not_lt.1 fun hlt => h.not_gt nth_lt_nth_of_lt_card hf hlt hm

中文:
定理 le_of_nth_le_nth_of_lt_card
  结论: (hf : (Set.ofPred p).Finite) {m n : 自然数} (h : nth p m <= nth p n)
  证明: not_lt.1 fun hlt => h.not_gt nth_lt_nth_of_lt_card hf hlt hm

Depends on / 依赖: h.not_gt, not_gt, not_lt, nth_lt_nth_of_lt_card
-/
theorem le_of_nth_le_nth_of_lt_card (hf : (Set.ofPred p).Finite) {m n : Nat} (h : nth p m <= nth p n)
    (hm : m < #hf.toFinset) : m <= n :=
not_lt.1 fun hlt => h.not_gt nth_lt_nth_of_lt_card hf hlt hm

/--
theorem `nth_injOn` / 定理 `nth_injOn`

English:
theorem nth_injOn
  given: (hf : (Set.ofPred p).Finite)
  statement: (Set.Iio #hf.toFinset).InjOn (nth p)
  proof: (nth_strictMonoOn hf).injOn

中文:
定理 nth_injOn
  条件: (hf : (Set.ofPred p).Finite)
  结论: (Set.Iio #hf.toFinset).InjOn (nth p)
  证明: (nth_strictMonoOn hf).injOn

Depends on / 依赖: nth_strictMonoOn
-/
theorem nth_injOn (hf : (Set.ofPred p).Finite) : (Set.Iio #hf.toFinset).InjOn (nth p) :=
  (nth_strictMonoOn hf).injOn

/--
theorem `range_nth_of_finite` / 定理 `range_nth_of_finite`

English:
theorem range_nth_of_finite
  given: (hf : (Set.ofPred p).Finite)
  proof: by
  simpa only [← List.getD_eq_getElem?_getD, ← nth_eq_getD_sort hf, mem_sort,
    Set.Finite.mem_toFinset] using! Set.range_list_getD (hf.toFinset.sort (· <= ·)) 0

@[simp]

中文:
定理 range_nth_of_finite
  条件: (hf : (Set.ofPred p).Finite)
  证明: by
  simpa only [← List.getD_eq_getElem?_getD, ← nth_eq_getD_sort hf, mem_sort,
    Set.Finite.mem_toFinset] using! Set.range_list_getD (hf.toFinset.sort (· <= ·)) 0

@[simp]

Depends on / 依赖: Finite, List.getD_eq_getElem, Set.Finite.mem_toFinset, Set.range_list_getD, _getD, getD_eq_getElem, hf.toFinset.sort, mem_sort, mem_toFinset, nth_eq_getD_sort, range_list_getD, toFinset
-/
theorem range_nth_of_finite (hf : (Set.ofPred p).Finite) :
    Set.range (nth p) = insert 0 (Set.ofPred p) := by
  simpa only [← List.getD_eq_getElem?_getD, ← nth_eq_getD_sort hf, mem_sort,
    Set.Finite.mem_toFinset] using! Set.range_list_getD (hf.toFinset.sort (· <= ·)) 0

@[simp]
/--
theorem `image_nth_Iio_card` / 定理 `image_nth_Iio_card`

English:
theorem image_nth_Iio_card
  given: (hf : (Set.ofPred p).Finite)
  proof: calc
    nth p '' Set.Iio #hf.toFinset = Set.range (hf.toFinset.orderEmbOfFin rfl) := by
      ext x
      simp only [Set.mem_image, Set.mem_range, Fin.exists_iff, ← nth_eq_orderEmbOfFin hf,
        Set.mem_Iio, exists_prop]
    _ = Set.ofPred p := by rw [range_orderEmbOfFin, Set.Finite.coe_toFinset

中文:
定理 image_nth_Iio_card
  条件: (hf : (Set.ofPred p).Finite)
  证明: calc
    nth p '' Set.Iio #hf.toFinset = Set.range (hf.toFinset.orderEmbOfFin rfl) := by
      ext x
      simp only [Set.mem_image, Set.mem_range, Fin.exists_iff, ← nth_eq_orderEmbOfFin hf,
        Set.mem_Iio, exists_prop]
    _ = Set.ofPred p := by rw [range_orderEmbOfFin, Set.Finite.coe_toFinset

Depends on / 依赖: Fin.exists_iff, Finite, Set.Finite.coe_toFinset, Set.Iio, Set.mem_Iio, Set.mem_image, Set.mem_range, Set.ofPred, Set.range, coe_toFinset, exists_iff, exists_prop, hf.toFinset, hf.toFinset.orderEmbOfFin, mem_Iio, mem_image, mem_range, nth_eq_orderEmbOfFin, ofPred, orderEmbOfFin
-/
theorem image_nth_Iio_card (hf : (Set.ofPred p).Finite) :
    nth p '' Set.Iio #hf.toFinset = Set.ofPred p :=
  calc
    nth p '' Set.Iio #hf.toFinset = Set.range (hf.toFinset.orderEmbOfFin rfl) := by
      ext x
      simp only [Set.mem_image, Set.mem_range, Fin.exists_iff, ← nth_eq_orderEmbOfFin hf,
        Set.mem_Iio, exists_prop]
    _ = Set.ofPred p := by rw [range_orderEmbOfFin, Set.Finite.coe_toFinset]

/--
theorem `nth_mem_of_lt_card` / 定理 `nth_mem_of_lt_card`

English:
theorem nth_mem_of_lt_card
  given: {n : Nat} (hf : (Set.ofPred p).Finite) (hlt : n < #hf.toFinset)
  proof: (image_nth_Iio_card hf).subset Set.mem_image_of_mem _ hlt

中文:
定理 nth_mem_of_lt_card
  条件: {n : 自然数} (hf : (Set.ofPred p).Finite) (hlt : n < #hf.toFinset)
  证明: (image_nth_Iio_card hf).subset Set.mem_image_of_mem _ hlt

Depends on / 依赖: Set.mem_image_of_mem, image_nth_Iio_card, mem_image_of_mem, subset
-/
theorem nth_mem_of_lt_card {n : Nat} (hf : (Set.ofPred p).Finite) (hlt : n < #hf.toFinset) :
    p (nth p n) :=
(image_nth_Iio_card hf).subset Set.mem_image_of_mem _ hlt

/--
theorem `exists_lt_card_finite_nth_eq` / 定理 `exists_lt_card_finite_nth_eq`

English:
theorem exists_lt_card_finite_nth_eq
  given: (hf : (Set.ofPred p).Finite) {x} (h : p x)
  proof: by
  rwa [← @Set.mem_ofPred_eq _ _ p, ← image_nth_Iio_card hf] at h

中文:
定理 exists_lt_card_finite_nth_eq
  条件: (hf : (Set.ofPred p).Finite) {x} (h : p x)
  证明: by
  rwa [← @Set.mem_ofPred_eq _ _ p, ← image_nth_Iio_card hf] at h

Depends on / 依赖: Set.mem_ofPred_eq, image_nth_Iio_card, mem_ofPred_eq
-/
theorem exists_lt_card_finite_nth_eq (hf : (Set.ofPred p).Finite) {x} (h : p x) :
    exists n, n < #hf.toFinset ∧ nth p n = x := by
  rwa [← @Set.mem_ofPred_eq _ _ p, ← image_nth_Iio_card hf] at h

/-!
### Lemmas about `Nat.nth` on an infinite set
-/

/--
theorem `nth_apply_eq_orderIsoOfNat` / 定理 `nth_apply_eq_orderIsoOfNat`

English:
theorem nth_apply_eq_orderIsoOfNat
  given: (hf : (Set.ofPred p).Infinite) (n : Nat)
  proof: by rw [nth, dif_neg hf]

中文:
定理 nth_apply_eq_orderIsoOfNat
  条件: (hf : (Set.ofPred p).Infinite) (n : 自然数)
  证明: by rw [nth, dif_neg hf]

Depends on / 依赖: dif_neg
-/
theorem nth_apply_eq_orderIsoOfNat (hf : (Set.ofPred p).Infinite) (n : Nat) :
    nth p n = @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype n := by rw [nth, dif_neg hf]

/--
theorem `nth_eq_orderIsoOfNat` / 定理 `nth_eq_orderIsoOfNat`

English:
theorem nth_eq_orderIsoOfNat
  given: (hf : (Set.ofPred p).Infinite)
  proof: funext nth_apply_eq_orderIsoOfNat hf

中文:
定理 nth_eq_orderIsoOfNat
  条件: (hf : (Set.ofPred p).Infinite)
  证明: funext nth_apply_eq_orderIsoOfNat hf

Depends on / 依赖: nth_apply_eq_orderIsoOfNat
-/
theorem nth_eq_orderIsoOfNat (hf : (Set.ofPred p).Infinite) :
    nth p = (↑) ∘ @Nat.Subtype.orderIsoOfNat (Set.ofPred p) hf.to_subtype :=
funext nth_apply_eq_orderIsoOfNat hf

/--
theorem `nth_strictMono` / 定理 `nth_strictMono`

English:
theorem nth_strictMono
  given: (hf : (Set.ofPred p).Infinite)
  statement: StrictMono (nth p)
  proof: by
  rw [nth_eq_orderIsoOfNat hf]
  exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)

中文:
定理 nth_strictMono
  条件: (hf : (Set.ofPred p).Infinite)
  结论: StrictMono (nth p)
  证明: by
  rw [nth_eq_orderIsoOfNat hf]
  exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)

Depends on / 依赖: OrderIso, OrderIso.strictMono, Subtype, Subtype.strictMono_coe, nth_eq_orderIsoOfNat, strictMono, strictMono_coe
-/
theorem nth_strictMono (hf : (Set.ofPred p).Infinite) : StrictMono (nth p) := by
  rw [nth_eq_orderIsoOfNat hf]
  exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)

/--
theorem `nth_injective` / 定理 `nth_injective`

English:
theorem nth_injective
  given: (hf : (Set.ofPred p).Infinite)
  statement: Function.Injective (nth p)
  proof: (nth_strictMono hf).injective

中文:
定理 nth_injective
  条件: (hf : (Set.ofPred p).Infinite)
  结论: Function.Injective (nth p)
  证明: (nth_strictMono hf).injective

Depends on / 依赖: injective, nth_strictMono
-/
theorem nth_injective (hf : (Set.ofPred p).Infinite) : Function.Injective (nth p) :=
  (nth_strictMono hf).injective

/--
theorem `nth_monotone` / 定理 `nth_monotone`

English:
theorem nth_monotone
  given: (hf : (Set.ofPred p).Infinite)
  statement: Monotone (nth p)
  proof: (nth_strictMono hf).monotone

中文:
定理 nth_monotone
  条件: (hf : (Set.ofPred p).Infinite)
  结论: Monotone (nth p)
  证明: (nth_strictMono hf).monotone

Depends on / 依赖: monotone, nth_strictMono
-/
theorem nth_monotone (hf : (Set.ofPred p).Infinite) : Monotone (nth p) :=
  (nth_strictMono hf).monotone

/--
theorem `nth_lt_nth` / 定理 `nth_lt_nth`

English:
theorem nth_lt_nth
  given: (hf : (Set.ofPred p).Infinite) {k n}
  statement: nth p k < nth p n ↔ k < n
  proof: (nth_strictMono hf).lt_iff_lt

中文:
定理 nth_lt_nth
  条件: (hf : (Set.ofPred p).Infinite) {k n}
  结论: nth p k < nth p n ↔ k < n
  证明: (nth_strictMono hf).lt_iff_lt

Depends on / 依赖: lt_iff_lt, nth_strictMono
-/
theorem nth_lt_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p k < nth p n ↔ k < n :=
  (nth_strictMono hf).lt_iff_lt

/--
theorem `nth_le_nth` / 定理 `nth_le_nth`

English:
theorem nth_le_nth
  given: (hf : (Set.ofPred p).Infinite) {k n}
  statement: nth p k <= nth p n ↔ k <= n
  proof: (nth_strictMono hf).le_iff_le

中文:
定理 nth_le_nth
  条件: (hf : (Set.ofPred p).Infinite) {k n}
  结论: nth p k <= nth p n ↔ k <= n
  证明: (nth_strictMono hf).le_iff_le

Depends on / 依赖: le_iff_le, nth_strictMono
-/
theorem nth_le_nth (hf : (Set.ofPred p).Infinite) {k n} : nth p k <= nth p n ↔ k <= n :=
  (nth_strictMono hf).le_iff_le

/--
theorem `range_nth_of_infinite` / 定理 `range_nth_of_infinite`

English:
theorem range_nth_of_infinite
  given: (hf : (Set.ofPred p).Infinite)
  proof: by
  rw [nth_eq_orderIsoOfNat hf]
  have := hf.to_subtype
  classical exact Nat.Subtype.coe_comp_ofNat_range

中文:
定理 range_nth_of_infinite
  条件: (hf : (Set.ofPred p).Infinite)
  证明: by
  rw [nth_eq_orderIsoOfNat hf]
  have := hf.to_subtype
  classical exact Nat.Subtype.coe_comp_ofNat_range

Depends on / 依赖: Nat.Subtype.coe_comp_ofNat_range, Subtype, classical, coe_comp_ofNat_range, hf.to_subtype, nth_eq_orderIsoOfNat, to_subtype
-/
theorem range_nth_of_infinite (hf : (Set.ofPred p).Infinite) :
    Set.range (nth p) = Set.ofPred p := by
  rw [nth_eq_orderIsoOfNat hf]
  have := hf.to_subtype
  classical exact Nat.Subtype.coe_comp_ofNat_range

/--
theorem `nth_mem_of_infinite` / 定理 `nth_mem_of_infinite`

English:
theorem nth_mem_of_infinite
  given: (hf : (Set.ofPred p).Infinite) (n : Nat)
  statement: p (nth p n)
  proof: Set.range_subset_iff.1 (range_nth_of_infinite hf).le n

中文:
定理 nth_mem_of_infinite
  条件: (hf : (Set.ofPred p).Infinite) (n : 自然数)
  结论: p (nth p n)
  证明: Set.range_subset_iff.1 (range_nth_of_infinite hf).le n

Depends on / 依赖: Set.range_subset_iff, range_nth_of_infinite, range_subset_iff
-/
theorem nth_mem_of_infinite (hf : (Set.ofPred p).Infinite) (n : Nat) : p (nth p n) :=
  Set.range_subset_iff.1 (range_nth_of_infinite hf).le n


/--
theorem `exists_lt_card_nth_eq` / 定理 `exists_lt_card_nth_eq`

English:
theorem exists_lt_card_nth_eq
  given: {x} (h : p x)
  proof: by
  refine (Set.ofPred p).finite_or_infinite.elim (fun hf => ?_) fun hf => ?_
  · rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩
    exact ⟨n, fun _ => hn, hx⟩
  · rw [← @Set.mem_ofPred_eq _ _ p, ← range_nth_of_infinite hf] at h
    rcases h with ⟨n, hx⟩
    exact ⟨n, fun hf' => absurd h

中文:
定理 exists_lt_card_nth_eq
  条件: {x} (h : p x)
  证明: by
  refine (Set.ofPred p).finite_or_infinite.elim (fun hf => ?_) fun hf => ?_
  · rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩
    exact ⟨n, fun _ => hn, hx⟩
  · rw [← @Set.mem_ofPred_eq _ _ p, ← range_nth_of_infinite hf] at h
    rcases h with ⟨n, hx⟩
    exact ⟨n, fun hf' => absurd h

Depends on / 依赖: Set.mem_ofPred_eq, Set.ofPred, absurd, exists_lt_card_finite_nth_eq, finite_or_infinite, finite_or_infinite.elim, mem_ofPred_eq, ofPred, range_nth_of_infinite
-/
theorem exists_lt_card_nth_eq {x} (h : p x) :
    exists n, (forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) ∧ nth p n = x := by
  refine (Set.ofPred p).finite_or_infinite.elim (fun hf => ?_) fun hf => ?_
  · rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩
    exact ⟨n, fun _ => hn, hx⟩
  · rw [← @Set.mem_ofPred_eq _ _ p, ← range_nth_of_infinite hf] at h
    rcases h with ⟨n, hx⟩
    exact ⟨n, fun hf' => absurd hf' hf, hx⟩

/--
theorem `subset_range_nth` / 定理 `subset_range_nth`

English:
theorem subset_range_nth
  statement: Set.ofPred p subseteq Set.range (nth p)
  proof: fun x (hx : p x) =>
  let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx
  ⟨n, hn⟩

中文:
定理 subset_range_nth
  结论: Set.ofPred p subseteq Set.range (nth p)
  证明: fun x (hx : p x) =>
  let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx
  ⟨n, hn⟩
-/
theorem subset_range_nth : Set.ofPred p subseteq Set.range (nth p) := fun x (hx : p x) =>
  let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx
  ⟨n, hn⟩

/--
theorem `range_nth_subset` / 定理 `range_nth_subset`

English:
theorem range_nth_subset
  statement: Set.range (nth p) subseteq insert 0 (Set.ofPred p)
  proof: (Set.ofPred p).finite_or_infinite.elim (fun h => (range_nth_of_finite h).subset) fun h =>
    (range_nth_of_infinite h).trans_subset (Set.subset_insert _ _)

中文:
定理 range_nth_subset
  结论: Set.range (nth p) subseteq insert 0 (Set.ofPred p)
  证明: (Set.ofPred p).finite_or_infinite.elim (fun h => (range_nth_of_finite h).subset) fun h =>
    (range_nth_of_infinite h).trans_subset (Set.subset_insert _ _)

Depends on / 依赖: Set.ofPred, Set.subset_insert, finite_or_infinite, finite_or_infinite.elim, ofPred, range_nth_of_finite, range_nth_of_infinite, subset, subset_insert, trans_subset
-/
theorem range_nth_subset : Set.range (nth p) subseteq insert 0 (Set.ofPred p) :=
  (Set.ofPred p).finite_or_infinite.elim (fun h => (range_nth_of_finite h).subset) fun h =>
    (range_nth_of_infinite h).trans_subset (Set.subset_insert _ _)

/--
theorem `nth_mem` / 定理 `nth_mem`

English:
theorem nth_mem
  given: (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  statement: p (nth p n)
  proof: (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_mem_of_lt_card hf (h hf)) fun h =>
    nth_mem_of_infinite h n

中文:
定理 nth_mem
  条件: (n : 自然数) (h : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  结论: p (nth p n)
  证明: (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_mem_of_lt_card hf (h hf)) fun h =>
    nth_mem_of_infinite h n

Depends on / 依赖: Set.ofPred, finite_or_infinite, finite_or_infinite.elim, nth_mem_of_infinite, nth_mem_of_lt_card, ofPred
-/
theorem nth_mem (n : Nat) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) : p (nth p n) :=
  (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_mem_of_lt_card hf (h hf)) fun h =>
    nth_mem_of_infinite h n

/--
theorem `nth_lt_nth'` / 定理 `nth_lt_nth'`

English:
theorem nth_lt_nth'
  given: {m n : Nat} (hlt : m < n) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  proof: (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_lt_nth_of_lt_card hf hlt (h _)) fun hf =>
    (nth_lt_nth hf).2 hlt

中文:
定理 nth_lt_nth'
  条件: {m n : 自然数} (hlt : m < n) (h : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  证明: (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_lt_nth_of_lt_card hf hlt (h _)) fun hf =>
    (nth_lt_nth hf).2 hlt

Depends on / 依赖: Set.ofPred, finite_or_infinite, finite_or_infinite.elim, nth_lt_nth, nth_lt_nth_of_lt_card, ofPred
-/
theorem nth_lt_nth' {m n : Nat} (hlt : m < n) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    nth p m < nth p n :=
  (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_lt_nth_of_lt_card hf hlt (h _)) fun hf =>
    (nth_lt_nth hf).2 hlt

/--
theorem `nth_le_nth'` / 定理 `nth_le_nth'`

English:
theorem nth_le_nth'
  given: {m n : Nat} (hle : m <= n) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  proof: (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_le_nth_of_lt_card hf hle (h _)) fun hf =>
    (nth_le_nth hf).2 hle

中文:
定理 nth_le_nth'
  条件: {m n : 自然数} (hle : m <= n) (h : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  证明: (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_le_nth_of_lt_card hf hle (h _)) fun hf =>
    (nth_le_nth hf).2 hle

Depends on / 依赖: Set.ofPred, finite_or_infinite, finite_or_infinite.elim, nth_le_nth, nth_le_nth_of_lt_card, ofPred
-/
theorem nth_le_nth' {m n : Nat} (hle : m <= n) (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    nth p m <= nth p n :=
  (Set.ofPred p).finite_or_infinite.elim (fun hf => nth_le_nth_of_lt_card hf hle (h _)) fun hf =>
    (nth_le_nth hf).2 hle

/--
theorem `le_nth` / 定理 `le_nth`

English:
theorem le_nth
  given: {n : Nat} (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  statement: n <= nth p n
  proof: (Set.ofPred p).finite_or_infinite.elim
    (fun hf => ((nth_strictMonoOn hf).mono <| Set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
    fun hf => (nth_strictMono hf).id_le _

中文:
定理 le_nth
  条件: {n : 自然数} (h : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  结论: n <= nth p n
  证明: (Set.ofPred p).finite_or_infinite.elim
    (fun hf => ((nth_strictMonoOn hf).mono <| Set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
    fun hf => (nth_strictMono hf).id_le _

Depends on / 依赖: Iic_id_le, Iic_subset_Iio, Set.Iic_subset_Iio, Set.ofPred, finite_or_infinite, finite_or_infinite.elim, id_le, le_rfl, nth_strictMono, nth_strictMonoOn, ofPred
-/
theorem le_nth {n : Nat} (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) : n <= nth p n :=
  (Set.ofPred p).finite_or_infinite.elim
    (fun hf => ((nth_strictMonoOn hf).mono <| Set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
    fun hf => (nth_strictMono hf).id_le _

/--
theorem `isLeast_nth` / 定理 `isLeast_nth`

English:
theorem isLeast_nth
  given: {n} (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  proof: ⟨⟨nth_mem n h, fun _k hk => nth_lt_nth' hk h⟩, fun _x hx =>
    let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
    (lt_or_ge k n).elim (fun hlt => absurd hkx (hx.2 _ hlt).ne) fun hle => hkx ▸ nth_le_nth' hle hk⟩

中文:
定理 isLeast_nth
  条件: {n} (h : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  证明: ⟨⟨nth_mem n h, fun _k hk => nth_lt_nth' hk h⟩, fun _x hx =>
    let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
    (lt_or_ge k n).elim (fun hlt => absurd hkx (hx.2 _ hlt).ne) fun hle => hkx ▸ nth_le_nth' hle hk⟩

Depends on / 依赖: absurd, exists_lt_card_nth_eq, lt_or_ge, nth_le_nth, nth_lt_nth, nth_mem
-/
theorem isLeast_nth {n} (h : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n) :=
  ⟨⟨nth_mem n h, fun _k hk => nth_lt_nth' hk h⟩, fun _x hx =>
    let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
    (lt_or_ge k n).elim (fun hlt => absurd hkx (hx.2 _ hlt).ne) fun hle => hkx ▸ nth_le_nth' hle hk⟩

/--
theorem `isLeast_nth_of_lt_card` / 定理 `isLeast_nth_of_lt_card`

English:
theorem isLeast_nth_of_lt_card
  given: {n : Nat} (hf : (Set.ofPred p).Finite) (hn : n < #hf.toFinset)
  proof: isLeast_nth fun _ => hn

中文:
定理 isLeast_nth_of_lt_card
  条件: {n : 自然数} (hf : (Set.ofPred p).Finite) (hn : n < #hf.toFinset)
  证明: isLeast_nth fun _ => hn

Depends on / 依赖: isLeast_nth
-/
theorem isLeast_nth_of_lt_card {n : Nat} (hf : (Set.ofPred p).Finite) (hn : n < #hf.toFinset) :
    IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun _ => hn

/--
theorem `isLeast_nth_of_infinite` / 定理 `isLeast_nth_of_infinite`

English:
theorem isLeast_nth_of_infinite
  given: (hf : (Set.ofPred p).Infinite) (n : Nat)
  proof: isLeast_nth fun h => absurd h hf

中文:
定理 isLeast_nth_of_infinite
  条件: (hf : (Set.ofPred p).Infinite) (n : 自然数)
  证明: isLeast_nth fun h => absurd h hf

Depends on / 依赖: absurd, isLeast_nth
-/
theorem isLeast_nth_of_infinite (hf : (Set.ofPred p).Infinite) (n : Nat) :
    IsLeast {i | p i ∧ forall k < n, nth p k < i} (nth p n) :=
  isLeast_nth fun h => absurd h hf

/--
theorem `nth_eq_sInf` / 定理 `nth_eq_sInf`

English:
theorem nth_eq_sInf
  given: (p : Nat -> Prop) (n : Nat)
  statement: nth p n = sInf {x | p x ∧ forall k < n, nth p k < x}
  proof: by
  by_cases! hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset
  · exact (isLeast_nth hn).csInf_eq.symm
  · rcases hn with ⟨hf, hn⟩
    rw [nth_of_card_le _ hn]
    refine ((congr_arg sInf <| Set.eq_empty_of_forall_notMem fun k hk => ?_).trans sInf_empty).symm
    rcases exists_lt_card_nth_

中文:
定理 nth_eq_sInf
  条件: (p : 自然数 -> 命题) (n : 自然数)
  结论: nth p n = sInf {x | p x ∧ 对任意 k < n, nth p k < x}
  证明: by
  by_cases! hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset
  · exact (isLeast_nth hn).csInf_eq.symm
  · rcases hn with ⟨hf, hn⟩
    rw [nth_of_card_le _ hn]
    refine ((congr_arg sInf <| Set.eq_empty_of_forall_notMem fun k hk => ?_).trans sInf_empty).symm
    rcases exists_lt_card_nth_

Depends on / 依赖: Finite, Set.eq_empty_of_forall_notMem, Set.ofPred, congr_arg, csInf_eq, csInf_eq.symm, eq_empty_of_forall_notMem, exists_lt_card_nth_eq, hf.toFinset, isLeast_nth, nth_of_card_le, ofPred, sInf_empty, toFinset, trans_le
-/
theorem nth_eq_sInf (p : Nat -> Prop) (n : Nat) : nth p n = sInf {x | p x ∧ forall k < n, nth p k < x} := by
  by_cases! hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset
  · exact (isLeast_nth hn).csInf_eq.symm
  · rcases hn with ⟨hf, hn⟩
    rw [nth_of_card_le _ hn]
    refine ((congr_arg sInf <| Set.eq_empty_of_forall_notMem fun k hk => ?_).trans sInf_empty).symm
    rcases exists_lt_card_nth_eq hk.1 with ⟨k, hlt, rfl⟩
    exact (hk.2 _ ((hlt hf).trans_le hn)).false

/--
theorem `nth_zero` / 定理 `nth_zero`

English:
theorem nth_zero
  statement: nth p 0 = sInf (Set.ofPred p)
  proof: by rw [nth_eq_sInf]; simp

@[simp]

中文:
定理 nth_zero
  结论: nth p 0 = sInf (Set.ofPred p)
  证明: by rw [nth_eq_sInf]; simp

@[simp]

Depends on / 依赖: nth_eq_sInf
-/
theorem nth_zero : nth p 0 = sInf (Set.ofPred p) := by rw [nth_eq_sInf]; simp

@[simp]
/--
theorem `nth_zero_of_zero` / 定理 `nth_zero_of_zero`

English:
theorem nth_zero_of_zero
  given: (h : p 0)
  statement: nth p 0 = 0
  proof: by simp [nth_zero, h]

中文:
定理 nth_zero_of_zero
  条件: (h : p 0)
  结论: nth p 0 = 0
  证明: by simp [nth_zero, h]

Depends on / 依赖: nth_zero
-/
theorem nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by simp [nth_zero, h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `nth_zero_of_exists` / 定理 `nth_zero_of_exists`

English:
theorem nth_zero_of_exists
  given: [DecidablePred p] (h : exists n, p n)
  statement: nth p 0 = Nat.find h
  proof: by
  rw [nth_zero]; convert! Nat.sInf_def h

中文:
定理 nth_zero_of_exists
  条件: [DecidablePred p] (h : 存在 n, p n)
  结论: nth p 0 = 自然数.find h
  证明: by
  rw [nth_zero]; convert! Nat.sInf_def h

Depends on / 依赖: Nat.sInf_def, convert, nth_zero, sInf_def
-/
theorem nth_zero_of_exists [DecidablePred p] (h : exists n, p n) : nth p 0 = Nat.find h := by
  rw [nth_zero]; convert! Nat.sInf_def h

/--
theorem `nth_eq_zero` / 定理 `nth_eq_zero`

English:
theorem nth_eq_zero
  given: {n}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [or_iff_not_imp_right, not_exists, not_le]
exact fun hn => ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 h ▸ le_nth hn⟩
  · rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩)
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle]

中文:
定理 nth_eq_zero
  条件: {n}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [or_iff_not_imp_right, not_exists, not_le]
exact fun hn => ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 h ▸ le_nth hn⟩
  · rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩)
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle]

Depends on / 依赖: exacts, le_nth, nonpos_iff_eq_zero, not_exists, not_le, nth_mem, nth_of_card_le, nth_zero_of_zero, or_iff_not_imp_right
-/
theorem nth_eq_zero {n} :
    nth p n = 0 ↔ p 0 ∧ n = 0 ∨ exists hf : (Set.ofPred p).Finite, #hf.toFinset <= n := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [or_iff_not_imp_right, not_exists, not_le]
exact fun hn => ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 h ▸ le_nth hn⟩
  · rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩)
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle]

/--
lemma `lt_card_toFinset_of_nth_ne_zero` / 引理 `lt_card_toFinset_of_nth_ne_zero`

English:
lemma lt_card_toFinset_of_nth_ne_zero
  given: {n : Nat} (h : nth p n != 0) (hf : (Set.ofPred p).Finite)
  proof: by
  simp only [ne_eq, nth_eq_zero, not_or, not_exists, not_le] at h
  exact h.2 hf

中文:
引理 lt_card_toFinset_of_nth_ne_zero
  条件: {n : 自然数} (h : nth p n != 0) (hf : (Set.ofPred p).Finite)
  证明: by
  simp only [ne_eq, nth_eq_zero, not_or, not_exists, not_le] at h
  exact h.2 hf

Depends on / 依赖: ne_eq, not_exists, not_le, not_or, nth_eq_zero
-/
lemma lt_card_toFinset_of_nth_ne_zero {n : Nat} (h : nth p n != 0) (hf : (Set.ofPred p).Finite) :
    n < #hf.toFinset := by
  simp only [ne_eq, nth_eq_zero, not_or, not_exists, not_le] at h
  exact h.2 hf

/--
lemma `nth_mem_of_ne_zero` / 引理 `nth_mem_of_ne_zero`

English:
lemma nth_mem_of_ne_zero
  given: {n : Nat} (h : nth p n != 0)
  statement: p (Nat.nth p n)
  proof: nth_mem n (lt_card_toFinset_of_nth_ne_zero h)

中文:
引理 nth_mem_of_ne_zero
  条件: {n : 自然数} (h : nth p n != 0)
  结论: p (自然数.nth p n)
  证明: nth_mem n (lt_card_toFinset_of_nth_ne_zero h)

Depends on / 依赖: lt_card_toFinset_of_nth_ne_zero, nth_mem
-/
lemma nth_mem_of_ne_zero {n : Nat} (h : nth p n != 0) : p (Nat.nth p n) :=
  nth_mem n (lt_card_toFinset_of_nth_ne_zero h)

/--
theorem `nth_eq_zero_mono` / 定理 `nth_eq_zero_mono`

English:
theorem nth_eq_zero_mono
  given: (h₀ : ¬p 0) {a b : Nat} (hab : a <= b) (ha : nth p a = 0)
  statement: nth p b = 0
  proof: by
  simp only [nth_eq_zero, h₀, false_and, false_or] at ha ⊢
  exact ha.imp fun hf hle => hle.trans hab

中文:
定理 nth_eq_zero_mono
  条件: (h₀ : ¬p 0) {a b : 自然数} (hab : a <= b) (ha : nth p a = 0)
  结论: nth p b = 0
  证明: by
  simp only [nth_eq_zero, h₀, false_and, false_or] at ha ⊢
  exact ha.imp fun hf hle => hle.trans hab

Depends on / 依赖: false_and, false_or, ha.imp, hle.trans, nth_eq_zero
-/
theorem nth_eq_zero_mono (h₀ : ¬p 0) {a b : Nat} (hab : a <= b) (ha : nth p a = 0) : nth p b = 0 := by
  simp only [nth_eq_zero, h₀, false_and, false_or] at ha ⊢
  exact ha.imp fun hf hle => hle.trans hab

/--
lemma `nth_ne_zero_anti` / 引理 `nth_ne_zero_anti`

English:
lemma nth_ne_zero_anti
  given: (h₀ : ¬p 0) {a b : Nat} (hab : a <= b) (hb : nth p b != 0)
  statement: nth p a != 0
  proof: mt (nth_eq_zero_mono h₀ hab) hb

中文:
引理 nth_ne_zero_anti
  条件: (h₀ : ¬p 0) {a b : 自然数} (hab : a <= b) (hb : nth p b != 0)
  结论: nth p a != 0
  证明: mt (nth_eq_zero_mono h₀ hab) hb

Depends on / 依赖: nth_eq_zero_mono
-/
lemma nth_ne_zero_anti (h₀ : ¬p 0) {a b : Nat} (hab : a <= b) (hb : nth p b != 0) : nth p a != 0 :=
  mt (nth_eq_zero_mono h₀ hab) hb

/--
theorem `le_nth_of_lt_nth_succ` / 定理 `le_nth_of_lt_nth_succ`

English:
theorem le_nth_of_lt_nth_succ
  given: {k a : Nat} (h : a < nth p (k + 1)) (ha : p a)
  statement: a <= nth p k
  proof: by
  rcases (Set.ofPred p).finite_or_infinite with hf | hf
  · rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩
    rcases lt_or_ge (k + 1) #hf.toFinset with hk | hk
    · rwa [(nth_strictMonoOn hf).lt_iff_lt hn hk, Nat.lt_succ_iff,
        ← (nth_strictMonoOn hf).le_iff_le hn (k.lt_succ_

中文:
定理 le_nth_of_lt_nth_succ
  条件: {k a : 自然数} (h : a < nth p (k + 1)) (ha : p a)
  结论: a <= nth p k
  证明: by
  rcases (Set.ofPred p).finite_or_infinite with hf | hf
  · rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩
    rcases lt_or_ge (k + 1) #hf.toFinset with hk | hk
    · rwa [(nth_strictMonoOn hf).lt_iff_lt hn hk, Nat.lt_succ_iff,
        ← (nth_strictMonoOn hf).le_iff_le hn (k.lt_succ_

Depends on / 依赖: Nat.lt_succ_iff, Set.ofPred, absurd, exists_lt_card_finite_nth_eq, finite_or_infinite, hf.toFinset, k.lt_succ_self.trans, le_iff_le, lt_iff_lt, lt_or_ge, lt_succ_iff, lt_succ_self, not_gt, nth_le_nth, nth_lt_nth, nth_of_card_le, nth_strictMonoOn, ofPred, subset_range_nth, toFinset
-/
theorem le_nth_of_lt_nth_succ {k a : Nat} (h : a < nth p (k + 1)) (ha : p a) : a <= nth p k := by
  rcases (Set.ofPred p).finite_or_infinite with hf | hf
  · rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩
    rcases lt_or_ge (k + 1) #hf.toFinset with hk | hk
    · rwa [(nth_strictMonoOn hf).lt_iff_lt hn hk, Nat.lt_succ_iff,
        ← (nth_strictMonoOn hf).le_iff_le hn (k.lt_succ_self.trans hk)] at h
    · rw [nth_of_card_le _ hk] at h
      exact absurd h (zero_le _).not_gt
  · rcases subset_range_nth ha with ⟨n, rfl⟩
    rwa [nth_lt_nth hf, Nat.lt_succ_iff, ← nth_le_nth hf] at h

/--
lemma `nth_mem_anti` / 引理 `nth_mem_anti`

English:
lemma nth_mem_anti
  given: {a b : Nat} (hab : a <= b) (h : p (nth p b))
  statement: p (nth p a)
  proof: by
  by_cases h' : forall hf : (Set.ofPred p).Finite, a < #hf.toFinset
  · exact nth_mem a h'
  · simp only [not_forall, not_lt] at h'
    have h'b : exists hf : (Set.ofPred p).Finite, #hf.toFinset <= b := by
      rcases h' with ⟨hf, ha⟩
      exact ⟨hf, ha.trans hab⟩
    have ha0 : nth p a = 0 := 

中文:
引理 nth_mem_anti
  条件: {a b : 自然数} (hab : a <= b) (h : p (nth p b))
  结论: p (nth p a)
  证明: by
  by_cases h' : forall hf : (Set.ofPred p).Finite, a < #hf.toFinset
  · exact nth_mem a h'
  · simp only [not_forall, not_lt] at h'
    have h'b : exists hf : (Set.ofPred p).Finite, #hf.toFinset <= b := by
      rcases h' with ⟨hf, ha⟩
      exact ⟨hf, ha.trans hab⟩
    have ha0 : nth p a = 0 := 

Depends on / 依赖: Finite, Set.ofPred, ha.trans, hf.toFinset, not_forall, not_lt, nth_eq_zero, nth_mem, ofPred, toFinset
-/
lemma nth_mem_anti {a b : Nat} (hab : a <= b) (h : p (nth p b)) : p (nth p a) := by
  by_cases h' : forall hf : (Set.ofPred p).Finite, a < #hf.toFinset
  · exact nth_mem a h'
  · simp only [not_forall, not_lt] at h'
    have h'b : exists hf : (Set.ofPred p).Finite, #hf.toFinset <= b := by
      rcases h' with ⟨hf, ha⟩
      exact ⟨hf, ha.trans hab⟩
    have ha0 : nth p a = 0 := by simp [nth_eq_zero, h']
    have hb0 : nth p b = 0 := by simp [nth_eq_zero, h'b]
    rw [ha0]
    rwa [hb0] at h

/--
lemma `nth_le_of_strictMonoOn_of_mapsTo` / 引理 `nth_le_of_strictMonoOn_of_mapsTo`

English:
lemma nth_le_of_strictMonoOn_of_mapsTo
  statement: {p : Nat -> Prop} (f : Nat -> Nat)
  proof: by
  by_cases! hn : (forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card)
  · induction n using Nat.strong_induction_on with | _ n ih =>
    rw [nth_eq_sInf]
    refine csInf_le (by simp) ⟨hmaps hn, fun k hk => ?_⟩
    have : f k < f n := by apply hmono <;> grind
    grind
  · rcases hn with

中文:
引理 nth_le_of_strictMonoOn_of_mapsTo
  结论: {p : 自然数 -> 命题} (f : 自然数 -> 自然数)
  证明: by
  by_cases! hn : (forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card)
  · induction n using Nat.strong_induction_on with | _ n ih =>
    rw [nth_eq_sInf]
    refine csInf_le (by simp) ⟨hmaps hn, fun k hk => ?_⟩
    have : f k < f n := by apply hmono <;> grind
    grind
  · rcases hn with

Depends on / 依赖: Finite, List.getD_eq_default, Nat.strong_induction_on, Nat.zero_le, Set.Finite, Set.ofPred, csInf_le, dif_pos, getD_eq_default, hf.toFinset.card, nth_eq_sInf, ofPred, strong_induction_on, toFinset, zero_le
-/
lemma nth_le_of_strictMonoOn_of_mapsTo {p : Nat -> Prop} (f : Nat -> Nat)
    (hmaps : Set.MapsTo f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmono : StrictMonoOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card })
      {n : Nat} :
    nth p n <= f n := by
  by_cases! hn : (forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card)
  · induction n using Nat.strong_induction_on with | _ n ih =>
    rw [nth_eq_sInf]
    refine csInf_le (by simp) ⟨hmaps hn, fun k hk => ?_⟩
    have : f k < f n := by apply hmono <;> grind
    grind
  · rcases hn with ⟨hf, hn⟩
    rw [nth]; rw [dif_pos hf]; rw [List.getD_eq_default _ _ (by simp [hn])]
    exact Nat.zero_le _

/--
lemma `le_nth_of_monotoneOn_of_surjOn` / 引理 `le_nth_of_monotoneOn_of_surjOn`

English:
lemma le_nth_of_monotoneOn_of_surjOn
  statement: {p : Nat -> Prop} (f : Nat -> Nat)
  proof: by
  induction n with
  | zero =>
    rw [Nat.nth_zero]
    refine le_csInf ⟨_, nth_mem _ hn⟩ fun b hb => ?_
    rcases hsurj hb with ⟨k, hk, rfl⟩
    exact hmono hn hk (Nat.zero_le _)
  | succ n ih =>
    rw [nth_eq_sInf]
    refine le_csInf ?_ ?_
    · use nth p (n + 1), nth_mem _ hn
      exact f

中文:
引理 le_nth_of_monotoneOn_of_surjOn
  结论: {p : 自然数 -> 命题} (f : 自然数 -> 自然数)
  证明: by
  induction n with
  | zero =>
    rw [Nat.nth_zero]
    refine le_csInf ⟨_, nth_mem _ hn⟩ fun b hb => ?_
    rcases hsurj hb with ⟨k, hk, rfl⟩
    exact hmono hn hk (Nat.zero_le _)
  | succ n ih =>
    rw [nth_eq_sInf]
    refine le_csInf ?_ ?_
    · use nth p (n + 1), nth_mem _ hn
      exact f

Depends on / 依赖: Nat.nth_zero, Nat.succ_le_iff, Nat.zero_le, hmono.reflect_lt, le_csInf, nth_eq_sInf, nth_lt_nth, nth_mem, nth_zero, reflect_lt, succ_le_iff, zero_le
-/
lemma le_nth_of_monotoneOn_of_surjOn {p : Nat -> Prop} (f : Nat -> Nat)
    (hsurj : Set.SurjOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmono : MonotoneOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card })
      {n : Nat}
    (hn : forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card) : f n <= nth p n := by
  induction n with
  | zero =>
    rw [Nat.nth_zero]
    refine le_csInf ⟨_, nth_mem _ hn⟩ fun b hb => ?_
    rcases hsurj hb with ⟨k, hk, rfl⟩
    exact hmono hn hk (Nat.zero_le _)
  | succ n ih =>
    rw [nth_eq_sInf]
    refine le_csInf ?_ ?_
    · use nth p (n + 1), nth_mem _ hn
      exact fun k hk => nth_lt_nth' hk hn
    rintro b ⟨hb, h⟩
    rcases hsurj hb with ⟨m, hm, rfl⟩
    apply hmono hn hm
    rw [Nat.succ_le_iff]
    apply hmono.reflect_lt <;> grind

/--
lemma `eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn` / 引理 `eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn`

English:
lemma eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn
  statement: {p : Nat -> Prop} (f : Nat -> Nat)
  proof: fun _ hi => le_antisymm
    (Nat.le_nth_of_monotoneOn_of_surjOn _ hsurj hmono.monotoneOn hi)
    (Nat.nth_le_of_strictMonoOn_of_mapsTo _ hmaps hmono)

中文:
引理 eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn
  结论: {p : 自然数 -> 命题} (f : 自然数 -> 自然数)
  证明: fun _ hi => le_antisymm
    (Nat.le_nth_of_monotoneOn_of_surjOn _ hsurj hmono.monotoneOn hi)
    (Nat.nth_le_of_strictMonoOn_of_mapsTo _ hmaps hmono)

Depends on / 依赖: Nat.le_nth_of_monotoneOn_of_surjOn, Nat.nth_le_of_strictMonoOn_of_mapsTo, hmono.monotoneOn, le_antisymm, le_nth_of_monotoneOn_of_surjOn, monotoneOn, nth_le_of_strictMonoOn_of_mapsTo
-/
lemma eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn {p : Nat -> Prop} (f : Nat -> Nat)
    (hsurj : Set.SurjOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmaps : Set.MapsTo f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }
      (Set.ofPred p))
    (hmono : StrictMonoOn f { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card }) :
    Set.EqOn f (nth p) { n : Nat | forall hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card } :=
  fun _ hi => le_antisymm
    (Nat.le_nth_of_monotoneOn_of_surjOn _ hsurj hmono.monotoneOn hi)
    (Nat.nth_le_of_strictMonoOn_of_mapsTo _ hmaps hmono)

/--
lemma `nth_comp_of_strictMono` / 引理 `nth_comp_of_strictMono`

English:
lemma nth_comp_of_strictMono
  statement: {n : Nat} {f : Nat -> Nat} (hf : StrictMono f)
  proof: by
  have hs {p' : Nat -> Prop} (h0p' : forall k, p' k -> k in Set.range f) :
      f '' {i | p' (f i)} = Set.ofPred p' := by
    ext i
    refine ⟨fun ⟨_, hi, h⟩ => h ▸ hi, fun he => ?_⟩
    rcases h0p' _ he with ⟨t, rfl⟩
    exact ⟨t, he, rfl⟩
  induction n using Nat.case_strong_induction_on
  cas

中文:
引理 nth_comp_of_strictMono
  结论: {n : 自然数} {f : 自然数 -> 自然数} (hf : StrictMono f)
  证明: by
  have hs {p' : Nat -> Prop} (h0p' : forall k, p' k -> k in Set.range f) :
      f '' {i | p' (f i)} = Set.ofPred p' := by
    ext i
    refine ⟨fun ⟨_, hi, h⟩ => h ▸ hi, fun he => ?_⟩
    rcases h0p' _ he with ⟨t, rfl⟩
    exact ⟨t, he, rfl⟩
  induction n using Nat.case_strong_induction_on
  cas

Depends on / 依赖: Nat.case_strong_induction_on, Set.mem_ofPred_eq, Set.ofPred, Set.range, case_strong_induction_on, hf.monotone.map_csInf, map_csInf, mem_ofPred_eq, monotone, nth_eq_sInf, nth_mem, nth_rw, nth_zero, ofPred, repeat, replace, simp_rw
-/
lemma nth_comp_of_strictMono {n : Nat} {f : Nat -> Nat} (hf : StrictMono f)
    (h0 : forall k, p k -> k in Set.range f) (h : forall hfi : (Set.ofPred p).Finite, n < hfi.toFinset.card) :
    f (nth (fun i => p (f i)) n) = nth p n := by
  have hs {p' : Nat -> Prop} (h0p' : forall k, p' k -> k in Set.range f) :
      f '' {i | p' (f i)} = Set.ofPred p' := by
    ext i
    refine ⟨fun ⟨_, hi, h⟩ => h ▸ hi, fun he => ?_⟩
    rcases h0p' _ he with ⟨t, rfl⟩
    exact ⟨t, he, rfl⟩
  induction n using Nat.case_strong_induction_on
  case _ =>
    simp_rw [nth_zero]
    replace h := nth_mem _ h
    rw [← hs h0]; rw [← hf.monotone.map_csInf]
    rcases h0 _ h with ⟨t, ht⟩
    exact ⟨t, Set.mem_ofPred_eq ▸ ht ▸ h⟩
  case _ n ih =>
    repeat nth_rw 1 [nth_eq_sInf]
    have h0' : forall k', (p k' ∧ forall k < n + 1, nth p k < k') -> k' in Set.range f := fun _ h => h0 _ h.1
    rw [← hs h0']; rw [← hf.monotone.map_csInf]
    · convert! rfl using 8 with k m' hm
      nth_rw 2 [← hf.lt_iff_lt]
      convert! Iff.rfl using 2
      exact ih m' (Nat.lt_add_one_iff.mp hm) fun hfi => hm.trans (h hfi)
    · rcases h0 _ (nth_mem _ h) with ⟨t, ht⟩
      exact ⟨t, ht ▸ (nth_mem _ h), fun _ hk => ht ▸ nth_lt_nth' hk h⟩

/--
lemma `nth_add` / 引理 `nth_add`

English:
lemma nth_add
  given: {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n != 0)
  proof: by
  refine nth_comp_of_strictMono (strictMono_id.add_const m) (fun k hk => ?_)
    (fun hf => lt_card_toFinset_of_nth_ne_zero h hf)
  by_contra hn
  simp_rw [id_eq, Set.mem_range, eq_comm] at hn
  exact h0 _ (not_le.mp fun h => hn (le_iff_exists_add'.mp h)) hk

中文:
引理 nth_add
  条件: {m n : 自然数} (h0 : 对任意 k < m, ¬p k) (h : nth p n != 0)
  证明: by
  refine nth_comp_of_strictMono (strictMono_id.add_const m) (fun k hk => ?_)
    (fun hf => lt_card_toFinset_of_nth_ne_zero h hf)
  by_contra hn
  simp_rw [id_eq, Set.mem_range, eq_comm] at hn
  exact h0 _ (not_le.mp fun h => hn (le_iff_exists_add'.mp h)) hk

Depends on / 依赖: Set.mem_range, add_const, eq_comm, id_eq, le_iff_exists_add, lt_card_toFinset_of_nth_ne_zero, mem_range, not_le, not_le.mp, nth_comp_of_strictMono, simp_rw, strictMono_id, strictMono_id.add_const
-/
lemma nth_add {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n != 0) :
    nth (fun i => p (i + m)) n + m = nth p n := by
  refine nth_comp_of_strictMono (strictMono_id.add_const m) (fun k hk => ?_)
    (fun hf => lt_card_toFinset_of_nth_ne_zero h hf)
  by_contra hn
  simp_rw [id_eq, Set.mem_range, eq_comm] at hn
  exact h0 _ (not_le.mp fun h => hn (le_iff_exists_add'.mp h)) hk

/--
lemma `nth_add_eq_sub` / 引理 `nth_add_eq_sub`

English:
lemma nth_add_eq_sub
  given: {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n != 0)
  proof: by
  rw [← nth_add h0 h]; rw [Nat.add_sub_cancel]

中文:
引理 nth_add_eq_sub
  条件: {m n : 自然数} (h0 : 对任意 k < m, ¬p k) (h : nth p n != 0)
  证明: by
  rw [← nth_add h0 h]; rw [Nat.add_sub_cancel]

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, nth_add
-/
lemma nth_add_eq_sub {m n : Nat} (h0 : forall k < m, ¬p k) (h : nth p n != 0) :
    nth (fun i => p (i + m)) n = nth p n - m := by
  rw [← nth_add h0 h]; rw [Nat.add_sub_cancel]

/--
lemma `nth_add_one` / 引理 `nth_add_one`

English:
lemma nth_add_one
  given: {n : Nat} (h0 : ¬p 0) (h : nth p n != 0)
  proof: nth_add (fun _ hk => (lt_one_iff.1 hk ▸ h0)) h

中文:
引理 nth_add_one
  条件: {n : 自然数} (h0 : ¬p 0) (h : nth p n != 0)
  证明: nth_add (fun _ hk => (lt_one_iff.1 hk ▸ h0)) h

Depends on / 依赖: lt_one_iff, nth_add
-/
lemma nth_add_one {n : Nat} (h0 : ¬p 0) (h : nth p n != 0) :
    nth (fun i => p (i + 1)) n + 1 = nth p n :=
  nth_add (fun _ hk => (lt_one_iff.1 hk ▸ h0)) h

/--
lemma `nth_add_one_eq_sub` / 引理 `nth_add_one_eq_sub`

English:
lemma nth_add_one_eq_sub
  given: {n : Nat} (h0 : ¬p 0) (h : nth p n != 0)
  proof: nth_add_eq_sub (fun _ hk => (lt_one_iff.1 hk ▸ h0)) h

中文:
引理 nth_add_one_eq_sub
  条件: {n : 自然数} (h0 : ¬p 0) (h : nth p n != 0)
  证明: nth_add_eq_sub (fun _ hk => (lt_one_iff.1 hk ▸ h0)) h

Depends on / 依赖: lt_one_iff, nth_add_eq_sub
-/
lemma nth_add_one_eq_sub {n : Nat} (h0 : ¬p 0) (h : nth p n != 0) :
    nth (fun i => p (i + 1)) n = nth p n - 1 :=
  nth_add_eq_sub (fun _ hk => (lt_one_iff.1 hk ▸ h0)) h

section Count

variable (p) [DecidablePred p]

@[simp]
/--
theorem `count_nth_zero` / 定理 `count_nth_zero`

English:
theorem count_nth_zero
  statement: count p (nth p 0) = 0
  proof: by
  rw [count_eq_card_filter_range]; rw [card_eq_zero]; rw [filter_eq_empty_iff]; rw [nth_zero]
  exact fun n h₁ h₂ => (mem_range.1 h₁).not_ge (Nat.sInf_le h₂)

中文:
定理 count_nth_zero
  结论: count p (nth p 0) = 0
  证明: by
  rw [count_eq_card_filter_range]; rw [card_eq_zero]; rw [filter_eq_empty_iff]; rw [nth_zero]
  exact fun n h₁ h₂ => (mem_range.1 h₁).not_ge (Nat.sInf_le h₂)

Depends on / 依赖: Nat.sInf_le, card_eq_zero, count_eq_card_filter_range, filter_eq_empty_iff, mem_range, not_ge, nth_zero, sInf_le
-/
theorem count_nth_zero : count p (nth p 0) = 0 := by
  rw [count_eq_card_filter_range]; rw [card_eq_zero]; rw [filter_eq_empty_iff]; rw [nth_zero]
  exact fun n h₁ h₂ => (mem_range.1 h₁).not_ge (Nat.sInf_le h₂)

/--
theorem `filter_range_nth_subset_insert` / 定理 `filter_range_nth_subset_insert`

English:
theorem filter_range_nth_subset_insert
  given: (k : Nat)
  proof: by
  intro a ha
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right fun h => ⟨h, ha.2⟩

中文:
定理 filter_range_nth_subset_insert
  条件: (k : 自然数)
  证明: by
  intro a ha
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right fun h => ⟨h, ha.2⟩

Depends on / 依赖: eq_or_lt, eq_or_lt.imp_right, imp_right, le_nth_of_lt_nth_succ, mem_filter, mem_insert, mem_range
-/
theorem filter_range_nth_subset_insert (k : Nat) :
    {n in range (nth p (k + 1)) | p n} subseteq insert (nth p k) {n in range (nth p k) | p n} := by
  intro a ha
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right fun h => ⟨h, ha.2⟩

variable {p}

/--
theorem `filter_range_nth_eq_insert` / 定理 `filter_range_nth_eq_insert`

English:
theorem filter_range_nth_eq_insert
  statement: {k : Nat}
  proof: by
  refine (filter_range_nth_subset_insert p k).antisymm fun a ha => ?_
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt
  rcases ha with (rfl | ⟨hlt, hpa⟩)
  · exact ⟨this, nth_mem _ fun hf => k.lt_succ_self.trans (hlt hf)⟩


中文:
定理 filter_range_nth_eq_insert
  结论: {k : 自然数}
  证明: by
  refine (filter_range_nth_subset_insert p k).antisymm fun a ha => ?_
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt
  rcases ha with (rfl | ⟨hlt, hpa⟩)
  · exact ⟨this, nth_mem _ fun hf => k.lt_succ_self.trans (hlt hf)⟩


Depends on / 依赖: antisymm, filter_range_nth_subset_insert, hlt.trans, k.lt_succ_self, k.lt_succ_self.trans, lt_succ_self, mem_filter, mem_insert, mem_range, nth_lt_nth, nth_mem
-/
theorem filter_range_nth_eq_insert {k : Nat}
    (hlt : forall hf : (Set.ofPred p).Finite, k + 1 < #hf.toFinset) :
    {n in range (nth p (k + 1)) | p n} = insert (nth p k) {n in range (nth p k) | p n} := by
  refine (filter_range_nth_subset_insert p k).antisymm fun a ha => ?_
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt
  rcases ha with (rfl | ⟨hlt, hpa⟩)
  · exact ⟨this, nth_mem _ fun hf => k.lt_succ_self.trans (hlt hf)⟩
  · exact ⟨hlt.trans this, hpa⟩

/--
theorem `filter_range_nth_eq_insert_of_finite` / 定理 `filter_range_nth_eq_insert_of_finite`

English:
theorem filter_range_nth_eq_insert_of_finite
  statement: (hf : (Set.ofPred p).Finite) {k : Nat}
  proof: filter_range_nth_eq_insert fun _ => hlt

中文:
定理 filter_range_nth_eq_insert_of_finite
  结论: (hf : (Set.ofPred p).Finite) {k : 自然数}
  证明: filter_range_nth_eq_insert fun _ => hlt

Depends on / 依赖: filter_range_nth_eq_insert
-/
theorem filter_range_nth_eq_insert_of_finite (hf : (Set.ofPred p).Finite) {k : Nat}
    (hlt : k + 1 < #hf.toFinset) :
    {n in range (nth p (k + 1)) | p n} = insert (nth p k) {n in range (nth p k) | p n} :=
  filter_range_nth_eq_insert fun _ => hlt

/--
theorem `filter_range_nth_eq_insert_of_infinite` / 定理 `filter_range_nth_eq_insert_of_infinite`

English:
theorem filter_range_nth_eq_insert_of_infinite
  given: (hp : (Set.ofPred p).Infinite) (k : Nat)
  proof: filter_range_nth_eq_insert fun hf => absurd hf hp

中文:
定理 filter_range_nth_eq_insert_of_infinite
  条件: (hp : (Set.ofPred p).Infinite) (k : 自然数)
  证明: filter_range_nth_eq_insert fun hf => absurd hf hp

Depends on / 依赖: absurd, filter_range_nth_eq_insert
-/
theorem filter_range_nth_eq_insert_of_infinite (hp : (Set.ofPred p).Infinite) (k : Nat) :
    {n in range (nth p (k + 1)) | p n} = insert (nth p k) {n in range (nth p k) | p n} :=
  filter_range_nth_eq_insert fun hf => absurd hf hp

/--
theorem `count_nth` / 定理 `count_nth`

English:
theorem count_nth
  given: {n : Nat} (hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  proof: by
  induction n with
  | zero => exact count_nth_zero _
  | succ k ihk =>
    rw [count_eq_card_filter_range]; rw [filter_range_nth_eq_insert hn]; rw [card_insert_of_notMem]; rw [← count_eq_card_filter_range]; rw [ihk fun hf => lt_of_succ_lt (hn hf)]
    simp

中文:
定理 count_nth
  条件: {n : 自然数} (hn : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  证明: by
  induction n with
  | zero => exact count_nth_zero _
  | succ k ihk =>
    rw [count_eq_card_filter_range]; rw [filter_range_nth_eq_insert hn]; rw [card_insert_of_notMem]; rw [← count_eq_card_filter_range]; rw [ihk fun hf => lt_of_succ_lt (hn hf)]
    simp

Depends on / 依赖: card_insert_of_notMem, count_eq_card_filter_range, count_nth_zero, filter_range_nth_eq_insert, lt_of_succ_lt
-/
theorem count_nth {n : Nat} (hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    count p (nth p n) = n := by
  induction n with
  | zero => exact count_nth_zero _
  | succ k ihk =>
    rw [count_eq_card_filter_range]; rw [filter_range_nth_eq_insert hn]; rw [card_insert_of_notMem]; rw [← count_eq_card_filter_range]; rw [ihk fun hf => lt_of_succ_lt (hn hf)]
    simp

/--
theorem `count_nth_of_lt_card_finite` / 定理 `count_nth_of_lt_card_finite`

English:
theorem count_nth_of_lt_card_finite
  given: {n : Nat} (hp : (Set.ofPred p).Finite) (hlt : n < #hp.toFinset)
  proof: count_nth fun _ => hlt

中文:
定理 count_nth_of_lt_card_finite
  条件: {n : 自然数} (hp : (Set.ofPred p).Finite) (hlt : n < #hp.toFinset)
  证明: count_nth fun _ => hlt

Depends on / 依赖: count_nth
-/
theorem count_nth_of_lt_card_finite {n : Nat} (hp : (Set.ofPred p).Finite) (hlt : n < #hp.toFinset) :
    count p (nth p n) = n :=
  count_nth fun _ => hlt

/--
theorem `count_nth_of_infinite` / 定理 `count_nth_of_infinite`

English:
theorem count_nth_of_infinite
  given: (hp : (Set.ofPred p).Infinite) (n : Nat)
  statement: count p (nth p n) = n
  proof: count_nth fun hf => absurd hf hp

中文:
定理 count_nth_of_infinite
  条件: (hp : (Set.ofPred p).Infinite) (n : 自然数)
  结论: count p (nth p n) = n
  证明: count_nth fun hf => absurd hf hp

Depends on / 依赖: absurd, count_nth
-/
theorem count_nth_of_infinite (hp : (Set.ofPred p).Infinite) (n : Nat) : count p (nth p n) = n :=
  count_nth fun hf => absurd hf hp

/--
theorem `surjective_count_of_infinite_setOfPred` / 定理 `surjective_count_of_infinite_setOfPred`

English:
theorem surjective_count_of_infinite_setOfPred
  given: (h : {n | p n}.Infinite)
  proof: fun n => ⟨nth p n, count_nth_of_infinite h n⟩

@[deprecated (since := "2026-07-09")]
alias surjective_count_of_infinite_setOf := surjective_count_of_infinite_setOfPred

中文:
定理 surjective_count_of_infinite_setOfPred
  条件: (h : {n | p n}.Infinite)
  证明: fun n => ⟨nth p n, count_nth_of_infinite h n⟩

@[deprecated (since := "2026-07-09")]
alias surjective_count_of_infinite_setOf := surjective_count_of_infinite_setOfPred

Depends on / 依赖: count_nth_of_infinite
-/
theorem surjective_count_of_infinite_setOfPred (h : {n | p n}.Infinite) :
    Function.Surjective (Nat.count p) :=
  fun n => ⟨nth p n, count_nth_of_infinite h n⟩

@[deprecated (since := "2026-07-09")]
alias surjective_count_of_infinite_setOf := surjective_count_of_infinite_setOfPred

/--
theorem `count_nth_succ` / 定理 `count_nth_succ`

English:
theorem count_nth_succ
  given: {n : Nat} (hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  proof: by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]

中文:
定理 count_nth_succ
  条件: {n : 自然数} (hn : 对任意 hf : (Set.ofPred p).Finite, n < #hf.toFinset)
  证明: by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]

Depends on / 依赖: count_nth, count_succ, if_pos, nth_mem
-/
theorem count_nth_succ {n : Nat} (hn : forall hf : (Set.ofPred p).Finite, n < #hf.toFinset) :
    count p (nth p n + 1) = n + 1 := by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]

/--
lemma `count_nth_succ_of_infinite` / 引理 `count_nth_succ_of_infinite`

English:
lemma count_nth_succ_of_infinite
  given: (hp : (Set.ofPred p).Infinite) (n : Nat)
  proof: by
  rw [count_succ]; rw [count_nth_of_infinite hp]; rw [if_pos (nth_mem_of_infinite hp _)]

@[simp]

中文:
引理 count_nth_succ_of_infinite
  条件: (hp : (Set.ofPred p).Infinite) (n : 自然数)
  证明: by
  rw [count_succ]; rw [count_nth_of_infinite hp]; rw [if_pos (nth_mem_of_infinite hp _)]

@[simp]

Depends on / 依赖: count_nth_of_infinite, count_succ, if_pos, nth_mem_of_infinite
-/
lemma count_nth_succ_of_infinite (hp : (Set.ofPred p).Infinite) (n : Nat) :
    count p (nth p n + 1) = n + 1 := by
  rw [count_succ]; rw [count_nth_of_infinite hp]; rw [if_pos (nth_mem_of_infinite hp _)]

@[simp]
/--
theorem `nth_count` / 定理 `nth_count`

English:
theorem nth_count
  given: {n : Nat} (hpn : p n)
  statement: nth p (count p n) = n
  proof: have : forall hf : (Set.ofPred p).Finite, count p n < #hf.toFinset := fun hf => count_lt_card hf hpn
  count_injective (nth_mem _ this) hpn (count_nth this)

中文:
定理 nth_count
  条件: {n : 自然数} (hpn : p n)
  结论: nth p (count p n) = n
  证明: have : forall hf : (Set.ofPred p).Finite, count p n < #hf.toFinset := fun hf => count_lt_card hf hpn
  count_injective (nth_mem _ this) hpn (count_nth this)

Depends on / 依赖: Finite, Set.ofPred, count_injective, count_lt_card, count_nth, hf.toFinset, nth_mem, ofPred, toFinset
-/
theorem nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n :=
  have : forall hf : (Set.ofPred p).Finite, count p n < #hf.toFinset := fun hf => count_lt_card hf hpn
  count_injective (nth_mem _ this) hpn (count_nth this)

/--
theorem `nth_lt_of_lt_count` / 定理 `nth_lt_of_lt_count`

English:
theorem nth_lt_of_lt_count
  given: {n k : Nat} (h : k < count p n)
  statement: nth p k < n
  proof: by
  refine (count_monotone p).reflect_lt ?_
  rwa [count_nth]
  exact fun hf => h.trans_le (count_le_card hf n)

中文:
定理 nth_lt_of_lt_count
  条件: {n k : 自然数} (h : k < count p n)
  结论: nth p k < n
  证明: by
  refine (count_monotone p).reflect_lt ?_
  rwa [count_nth]
  exact fun hf => h.trans_le (count_le_card hf n)

Depends on / 依赖: count_le_card, count_monotone, count_nth, h.trans_le, reflect_lt, trans_le
-/
theorem nth_lt_of_lt_count {n k : Nat} (h : k < count p n) : nth p k < n := by
  refine (count_monotone p).reflect_lt ?_
  rwa [count_nth]
  exact fun hf => h.trans_le (count_le_card hf n)

/--
theorem `le_nth_of_count_le` / 定理 `le_nth_of_count_le`

English:
theorem le_nth_of_count_le
  given: {n k : Nat} (h : n <= nth p k)
  statement: count p n <= k
  proof: not_lt.1 fun hlt => h.not_gt nth_lt_of_lt_count hlt

中文:
定理 le_nth_of_count_le
  条件: {n k : 自然数} (h : n <= nth p k)
  结论: count p n <= k
  证明: not_lt.1 fun hlt => h.not_gt nth_lt_of_lt_count hlt

Depends on / 依赖: h.not_gt, not_gt, not_lt, nth_lt_of_lt_count
-/
theorem le_nth_of_count_le {n k : Nat} (h : n <= nth p k) : count p n <= k :=
not_lt.1 fun hlt => h.not_gt nth_lt_of_lt_count hlt

/--
theorem `count_eq_zero` / 定理 `count_eq_zero`

English:
theorem count_eq_zero
  given: (h : exists n, p n) {n : Nat}
  statement: count p n = 0 ↔ n <= nth p 0
  proof: by
  rw [nth_zero_of_exists h]; rw [le_find_iff h]; rw [Nat.count_iff_forall_not]

中文:
定理 count_eq_zero
  条件: (h : 存在 n, p n) {n : 自然数}
  结论: count p n = 0 ↔ n <= nth p 0
  证明: by
  rw [nth_zero_of_exists h]; rw [le_find_iff h]; rw [Nat.count_iff_forall_not]
-/
protected theorem count_eq_zero (h : exists n, p n) {n : Nat} : count p n = 0 ↔ n <= nth p 0 := by
  rw [nth_zero_of_exists h]; rw [le_find_iff h]; rw [Nat.count_iff_forall_not]

variable (p) in
/--
theorem `nth_count_eq_sInf` / 定理 `nth_count_eq_sInf`

English:
theorem nth_count_eq_sInf
  given: (n : Nat)
  statement: nth p (count p n) = sInf {i : Nat | p i ∧ n <= i}
  proof: by
  refine (nth_eq_sInf _ _).trans (congr_arg sInf ?_)
  refine Set.ext fun a => and_congr_right fun hpa => ?_
  refine ⟨fun h => not_lt.1 fun ha => ?_, fun hn k hk => lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
  rwa [nth_count hpa

中文:
定理 nth_count_eq_sInf
  条件: (n : 自然数)
  结论: nth p (count p n) = sInf {i : 自然数 | p i ∧ n <= i}
  证明: by
  refine (nth_eq_sInf _ _).trans (congr_arg sInf ?_)
  refine Set.ext fun a => and_congr_right fun hpa => ?_
  refine ⟨fun h => not_lt.1 fun ha => ?_, fun hn k hk => lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
  rwa [nth_count hpa

Depends on / 依赖: Set.ext, and_congr_right, congr_arg, count_strict_mono, lt_of_lt_of_le, lt_self_iff_false, not_lt, nth_count, nth_eq_sInf, nth_lt_of_lt_count
-/
theorem nth_count_eq_sInf (n : Nat) : nth p (count p n) = sInf {i : Nat | p i ∧ n <= i} := by
  refine (nth_eq_sInf _ _).trans (congr_arg sInf ?_)
  refine Set.ext fun a => and_congr_right fun hpa => ?_
  refine ⟨fun h => not_lt.1 fun ha => ?_, fun hn k hk => lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha)
  rwa [nth_count hpa, lt_self_iff_false] at hn

/--
theorem `le_nth_count'` / 定理 `le_nth_count'`

English:
theorem le_nth_count'
  given: {n : Nat} (hpn : exists k, p k ∧ n <= k)
  statement: n <= nth p (count p n)
  proof: (le_csInf hpn fun _ => And.right).trans (nth_count_eq_sInf p n).ge

中文:
定理 le_nth_count'
  条件: {n : 自然数} (hpn : 存在 k, p k ∧ n <= k)
  结论: n <= nth p (count p n)
  证明: (le_csInf hpn fun _ => And.right).trans (nth_count_eq_sInf p n).ge

Depends on / 依赖: And.right, le_csInf, nth_count_eq_sInf
-/
theorem le_nth_count' {n : Nat} (hpn : exists k, p k ∧ n <= k) : n <= nth p (count p n) :=
  (le_csInf hpn fun _ => And.right).trans (nth_count_eq_sInf p n).ge

/--
theorem `le_nth_count` / 定理 `le_nth_count`

English:
theorem le_nth_count
  given: (hp : (Set.ofPred p).Infinite) (n : Nat)
  statement: n <= nth p (count p n)
  proof: let ⟨m, hp, hn⟩ := hp.exists_gt n
  le_nth_count' ⟨m, hp, hn.le⟩

中文:
定理 le_nth_count
  条件: (hp : (Set.ofPred p).Infinite) (n : 自然数)
  结论: n <= nth p (count p n)
  证明: let ⟨m, hp, hn⟩ := hp.exists_gt n
  le_nth_count' ⟨m, hp, hn.le⟩

Depends on / 依赖: exists_gt, hn.le, hp.exists_gt, le_nth_count
-/
theorem le_nth_count (hp : (Set.ofPred p).Infinite) (n : Nat) : n <= nth p (count p n) :=
  let ⟨m, hp, hn⟩ := hp.exists_gt n
  le_nth_count' ⟨m, hp, hn.le⟩

/--
Definition of `giCountNth` / `giCountNth` 的定义

English:
definition giCountNth
  signature: (hp : (Set.ofPred p).Infinite)
  body: GaloisInsertion.monotoneIntro (nth_monotone hp) (count_monotone p) (le_nth_count hp)
    (count_nth_of_infinite hp)

中文:
定义 giCountNth
  签名: (hp : (Set.ofPred p).Infinite)
  定义体: GaloisInsertion.monotoneIntro (nth_monotone hp) (count_monotone p) (le_nth_count hp)
    (count_nth_of_infinite hp)

Depends on / 依赖: GaloisInsertion, GaloisInsertion.monotoneIntro, count_monotone, count_nth_of_infinite, le_nth_count, monotoneIntro, nth_monotone
-/
noncomputable def giCountNth (hp : (Set.ofPred p).Infinite) : GaloisInsertion (count p) (nth p) :=
  GaloisInsertion.monotoneIntro (nth_monotone hp) (count_monotone p) (le_nth_count hp)
    (count_nth_of_infinite hp)

/--
theorem `gc_count_nth` / 定理 `gc_count_nth`

English:
theorem gc_count_nth
  given: (hp : (Set.ofPred p).Infinite)
  statement: GaloisConnection (count p) (nth p)
  proof: (giCountNth hp).gc

中文:
定理 gc_count_nth
  条件: (hp : (Set.ofPred p).Infinite)
  结论: GaloisConnection (count p) (nth p)
  证明: (giCountNth hp).gc

Depends on / 依赖: giCountNth
-/
theorem gc_count_nth (hp : (Set.ofPred p).Infinite) : GaloisConnection (count p) (nth p) :=
  (giCountNth hp).gc

/--
theorem `count_le_iff_le_nth` / 定理 `count_le_iff_le_nth`

English:
theorem count_le_iff_le_nth
  given: (hp : (Set.ofPred p).Infinite) {a b : Nat}
  proof: gc_count_nth hp _ _

中文:
定理 count_le_iff_le_nth
  条件: (hp : (Set.ofPred p).Infinite) {a b : 自然数}
  证明: gc_count_nth hp _ _

Depends on / 依赖: gc_count_nth
-/
theorem count_le_iff_le_nth (hp : (Set.ofPred p).Infinite) {a b : Nat} :
    count p a <= b ↔ a <= nth p b :=
  gc_count_nth hp _ _

/--
theorem `lt_nth_iff_count_lt` / 定理 `lt_nth_iff_count_lt`

English:
theorem lt_nth_iff_count_lt
  given: (hp : (Set.ofPred p).Infinite) {a b : Nat}
  proof: (gc_count_nth hp).lt_iff_lt

中文:
定理 lt_nth_iff_count_lt
  条件: (hp : (Set.ofPred p).Infinite) {a b : 自然数}
  证明: (gc_count_nth hp).lt_iff_lt

Depends on / 依赖: gc_count_nth, lt_iff_lt
-/
theorem lt_nth_iff_count_lt (hp : (Set.ofPred p).Infinite) {a b : Nat} :
    a < count p b ↔ nth p a < b :=
  (gc_count_nth hp).lt_iff_lt

end Count

/--
theorem `nth_of_forall` / 定理 `nth_of_forall`

English:
theorem nth_of_forall
  given: {n : Nat} (hp : forall n' <= n, p n')
  statement: nth p n = n
  proof: by
  classical nth_rw 1 [← count_of_forall (hp · ·.le), nth_count (hp n le_rfl)]

中文:
定理 nth_of_forall
  条件: {n : 自然数} (hp : 对任意 n' <= n, p n')
  结论: nth p n = n
  证明: by
  classical nth_rw 1 [← count_of_forall (hp · ·.le), nth_count (hp n le_rfl)]

Depends on / 依赖: classical, count_of_forall, le_rfl, nth_count, nth_rw
-/
theorem nth_of_forall {n : Nat} (hp : forall n' <= n, p n') : nth p n = n := by
  classical nth_rw 1 [← count_of_forall (hp · ·.le), nth_count (hp n le_rfl)]

/--
theorem `nth_true` / 定理 `nth_true`

English:
theorem nth_true
  given: (n : Nat)
  statement: nth (fun _ => True) n = n
  proof: nth_of_forall fun _ _ => trivial

中文:
定理 nth_true
  条件: (n : 自然数)
  结论: nth (fun _ => True) n = n
  证明: nth_of_forall fun _ _ => trivial
-/
@[simp] theorem nth_true (n : Nat) : nth (fun _ => True) n = n := nth_of_forall fun _ _ => trivial

/--
theorem `nth_of_forall_not` / 定理 `nth_of_forall_not`

English:
theorem nth_of_forall_not
  given: {n : Nat} (hp : forall n' >= n, ¬p n')
  statement: nth p n = 0
  proof: by
  have : Set.ofPred p subseteq Finset.range n := by
    intro n' hn'
    contrapose! hp
    exact ⟨n', by simpa using hp, Set.mem_ofPred.mp hn'⟩
  rw [nth_of_card_le ((finite_toSet _).subset this)]
  · refine (Finset.card_le_card ?_).trans_eq (Finset.card_range n)
    exact Set.Finite.toFinset_su

中文:
定理 nth_of_forall_not
  条件: {n : 自然数} (hp : 对任意 n' >= n, ¬p n')
  结论: nth p n = 0
  证明: by
  have : Set.ofPred p subseteq Finset.range n := by
    intro n' hn'
    contrapose! hp
    exact ⟨n', by simpa using hp, Set.mem_ofPred.mp hn'⟩
  rw [nth_of_card_le ((finite_toSet _).subset this)]
  · refine (Finset.card_le_card ?_).trans_eq (Finset.card_range n)
    exact Set.Finite.toFinset_su

Depends on / 依赖: Finite, Finset, Finset.card_le_card, Finset.card_range, Finset.range, Set.Finite.toFinset_subset.mpr, Set.mem_ofPred.mp, Set.ofPred, card_le_card, card_range, contrapose, finite_toSet, mem_ofPred, nth_of_card_le, ofPred, subset, subseteq, toFinset_subset, trans_eq
-/
theorem nth_of_forall_not {n : Nat} (hp : forall n' >= n, ¬p n') : nth p n = 0 := by
  have : Set.ofPred p subseteq Finset.range n := by
    intro n' hn'
    contrapose! hp
    exact ⟨n', by simpa using hp, Set.mem_ofPred.mp hn'⟩
  rw [nth_of_card_le ((finite_toSet _).subset this)]
  · refine (Finset.card_le_card ?_).trans_eq (Finset.card_range n)
    exact Set.Finite.toFinset_subset.mpr this

/--
theorem `nth_false` / 定理 `nth_false`

English:
theorem nth_false
  given: (n : Nat)
  statement: nth (fun _ => False) n = 0
  proof: nth_of_forall_not fun _ _ => id

中文:
定理 nth_false
  条件: (n : 自然数)
  结论: nth (fun _ => False) n = 0
  证明: nth_of_forall_not fun _ _ => id
-/
@[simp] theorem nth_false (n : Nat) : nth (fun _ => False) n = 0 := nth_of_forall_not fun _ _ => id

end Nat
