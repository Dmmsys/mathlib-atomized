/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Tactic.FinCases

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


variable {ι α β F : Type*}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable {R : ι -> Type*} [Π i, Semiring (R i)] (I J : Π i, Ideal (R i))

section Pi

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: : Ideal (Π i, R i) where
  body: { r | forall i, r i in I i }
  zero_mem' i := (I i).zero_mem
  add_mem' ha hb i := (I i).add_mem (ha i) (hb i)
  smul_mem' a _b hb i := (I i).mul_mem_left (a i) (hb i)

中文:
定义 pi
  签名: : Ideal (Π i, R i) where
  定义体: { r | forall i, r i in I i }
  zero_mem' i := (I i).zero_mem
  add_mem' ha hb i := (I i).add_mem (ha i) (hb i)
  smul_mem' a _b hb i := (I i).mul_mem_left (a i) (hb i)
-/
def pi : Ideal (Π i, R i) where
  carrier := { r | forall i, r i in I i }
  zero_mem' i := (I i).zero_mem
  add_mem' ha hb i := (I i).add_mem (ha i) (hb i)
  smul_mem' a _b hb i := (I i).mul_mem_left (a i) (hb i)

/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: (r : Π i, R i)
  statement: r in pi I ↔ forall i, r i in I i
  proof: Iff.rfl

中文:
定理 mem_pi
  条件: (r : Π i, R i)
  结论: r in pi I ↔ 对任意 i, r i in I i
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_pi (r : Π i, R i) : r in pi I ↔ forall i, r i in I i :=
  Iff.rfl

/--
theorem `pi_span` / 定理 `pi_span`

English:
theorem pi_span
  given: {r : Π i, R i}
  statement: pi (span {r ·}) = span {r}
  proof: by
  ext; simp_rw [mem_pi, mem_span_singleton', funext_iff, Classical.skolem, Pi.mul_def]

中文:
定理 pi_span
  条件: {r : Π i, R i}
  结论: pi (span {r ·}) = span {r}
  证明: by
  ext; simp_rw [mem_pi, mem_span_singleton', funext_iff, Classical.skolem, Pi.mul_def]
-/
@[simp] theorem pi_span {r : Π i, R i} : pi (span {r ·}) = span {r} := by
  ext; simp_rw [mem_pi, mem_span_singleton', funext_iff, Classical.skolem, Pi.mul_def]

instance (priority := low) [forall i, (I i).IsTwoSided] : (pi I).IsTwoSided :=
  ⟨fun _b hb i => mul_mem_right _ _ (hb i)⟩

variable {I J}

/--
theorem `single_mem_pi` / 定理 `single_mem_pi`

English:
theorem single_mem_pi
  given: [DecidableEq ι] {i : ι} {r : R i} (hr : r in I i)
  statement: Pi.single i r in pi I
  proof: by
  intro j
  obtain rfl | ne := eq_or_ne i j
  · simpa
  · simp [ne]

中文:
定理 single_mem_pi
  条件: [DecidableEq ι] {i : ι} {r : R i} (hr : r in I i)
  结论: Pi.single i r in pi I
  证明: by
  intro j
  obtain rfl | ne := eq_or_ne i j
  · simpa
  · simp [ne]

Depends on / 依赖: eq_or_ne
-/
theorem single_mem_pi [DecidableEq ι] {i : ι} {r : R i} (hr : r in I i) : Pi.single i r in pi I := by
  intro j
  obtain rfl | ne := eq_or_ne i j
  · simpa
  · simp [ne]

/--
theorem `pi_le_pi_iff` / 定理 `pi_le_pi_iff`

English:
theorem pi_le_pi_iff
  statement: pi I <= pi J ↔ I <= J where
  proof: by classical simpa using le (single_mem_pi hr) i
  mpr le r hr i := le i (hr i)

中文:
定理 pi_le_pi_iff
  结论: pi I <= pi J ↔ I <= J where
  证明: by classical simpa using le (single_mem_pi hr) i
  mpr le r hr i := le i (hr i)
-/
@[simp] theorem pi_le_pi_iff : pi I <= pi J ↔ I <= J where
  mp le i r hr := by classical simpa using le (single_mem_pi hr) i
  mpr le r hr i := le i (hr i)

end Pi

section Commute

variable {α : Type*} [Semiring α] (I : Ideal α) {a b : α}

/--
theorem `add_pow_mem_of_pow_mem_of_le_of_commute` / 定理 `add_pow_mem_of_pow_mem_of_le_of_commute`

English:
theorem add_pow_mem_of_pow_mem_of_le_of_commute
  statement: {m n k : Nat}
  proof: by
  simp_rw [hab.add_pow, ← Nat.cast_comm]
  apply I.sum_mem
  intro c _
  apply mul_mem_left
  by_cases h : m <= c
  · rw [hab.pow_pow]
    exact I.mul_mem_left _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ (I.pow_mem_of_pow_mem hb ?_)
    lia

中文:
定理 add_pow_mem_of_pow_mem_of_le_of_commute
  结论: {m n k : 自然数}
  证明: by
  simp_rw [hab.add_pow, ← Nat.cast_comm]
  apply I.sum_mem
  intro c _
  apply mul_mem_left
  by_cases h : m <= c
  · rw [hab.pow_pow]
    exact I.mul_mem_left _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ (I.pow_mem_of_pow_mem hb ?_)
    lia

Depends on / 依赖: I.mul_mem_left, I.pow_mem_of_pow_mem, I.sum_mem, Nat.cast_comm, add_pow, cast_comm, hab.add_pow, hab.pow_pow, mul_mem_left, pow_mem_of_pow_mem, pow_pow, simp_rw, sum_mem
-/
theorem add_pow_mem_of_pow_mem_of_le_of_commute {m n k : Nat}
    (ha : a ^ m in I) (hb : b ^ n in I) (hk : m + n <= k + 1)
    (hab : Commute a b) :
    (a + b) ^ k in I := by
  simp_rw [hab.add_pow, ← Nat.cast_comm]
  apply I.sum_mem
  intro c _
  apply mul_mem_left
  by_cases h : m <= c
  · rw [hab.pow_pow]
    exact I.mul_mem_left _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ (I.pow_mem_of_pow_mem hb ?_)
    lia

/--
theorem `add_pow_add_pred_mem_of_pow_mem_of_commute` / 定理 `add_pow_add_pred_mem_of_pow_mem_of_commute`

English:
theorem add_pow_add_pred_mem_of_pow_mem_of_commute
  statement: {m n : Nat}
  proof: I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (by rw [← Nat.sub_le_iff_le_add]) hab

中文:
定理 add_pow_add_pred_mem_of_pow_mem_of_commute
  结论: {m n : 自然数}
  证明: I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (by rw [← Nat.sub_le_iff_le_add]) hab

Depends on / 依赖: I.add_pow_mem_of_pow_mem_of_le_of_commute, Nat.sub_le_iff_le_add, add_pow_mem_of_pow_mem_of_le_of_commute, sub_le_iff_le_add
-/
theorem add_pow_add_pred_mem_of_pow_mem_of_commute {m n : Nat}
    (ha : a ^ m in I) (hb : b ^ n in I) (hab : Commute a b) :
    (a + b) ^ (m + n - 1) in I :=
  I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (by rw [← Nat.sub_le_iff_le_add]) hab

end Commute

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/--
theorem `add_pow_mem_of_pow_mem_of_le` / 定理 `add_pow_mem_of_pow_mem_of_le`

English:
theorem add_pow_mem_of_pow_mem_of_le
  statement: {m n k : Nat}
  proof: I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb hk (Commute.all ..)

中文:
定理 add_pow_mem_of_pow_mem_of_le
  结论: {m n k : 自然数}
  证明: I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb hk (Commute.all ..)

Depends on / 依赖: Commute, Commute.all, I.add_pow_mem_of_pow_mem_of_le_of_commute, add_pow_mem_of_pow_mem_of_le_of_commute
-/
theorem add_pow_mem_of_pow_mem_of_le {m n k : Nat}
    (ha : a ^ m in I) (hb : b ^ n in I) (hk : m + n <= k + 1) :
    (a + b) ^ k in I :=
  I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb hk (Commute.all ..)

/--
theorem `add_pow_add_pred_mem_of_pow_mem` / 定理 `add_pow_add_pred_mem_of_pow_mem`

English:
theorem add_pow_add_pred_mem_of_pow_mem
  statement: {m n : Nat}
  proof: I.add_pow_add_pred_mem_of_pow_mem_of_commute ha hb (Commute.all ..)

中文:
定理 add_pow_add_pred_mem_of_pow_mem
  结论: {m n : 自然数}
  证明: I.add_pow_add_pred_mem_of_pow_mem_of_commute ha hb (Commute.all ..)

Depends on / 依赖: Commute, Commute.all, I.add_pow_add_pred_mem_of_pow_mem_of_commute, add_pow_add_pred_mem_of_pow_mem_of_commute
-/
theorem add_pow_add_pred_mem_of_pow_mem {m n : Nat}
    (ha : a ^ m in I) (hb : b ^ n in I) :
    (a + b) ^ (m + n - 1) in I :=
  I.add_pow_add_pred_mem_of_pow_mem_of_commute ha hb (Commute.all ..)

/--
theorem `pow_multiset_sum_mem_span_pow` / 定理 `pow_multiset_sum_mem_span_pow`

English:
theorem pow_multiset_sum_mem_span_pow
  given: [DecidableEq α] (s : Multiset α) (n : Nat)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s hs => ?_
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine Submodule.sum_mem _ ?_
  intro c _hc
  rw [mem_span_insert]
  by_cases! h 

中文:
定理 pow_multiset_sum_mem_span_pow
  条件: [DecidableEq α] (s : Multiset α) (n : 自然数)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s hs => ?_
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine Submodule.sum_mem _ ?_
  intro c _hc
  rw [mem_span_insert]
  by_cases! h 

Depends on / 依赖: Finset, Finset.coe_insert, Multiset, Multiset.card, Multiset.card_cons, Multiset.induction_on, Multiset.map_cons, Multiset.sum_cons, Multiset.toFinset_cons, Submodule, Submodule.sum_mem, Submodule.zero_mem, add_pow, card_cons, coe_insert, induction_on, map_cons, mem_span_insert, mul_assoc, mul_comm
-/
theorem pow_multiset_sum_mem_span_pow [DecidableEq α] (s : Multiset α) (n : Nat) :
    s.sum ^ (Multiset.card s * n + 1) in
    span ((s.map fun (x : α) => x ^ (n + 1)).toFinset : Set α) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s hs => ?_
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine Submodule.sum_mem _ ?_
  intro c _hc
  rw [mem_span_insert]
  by_cases! h : n + 1 <= c
  · refine ⟨a ^ (c - (n + 1)) * s.sum ^ ((Multiset.card s + 1) * n + 1 - c) *
      ((Multiset.card s + 1) * n + 1).choose c, 0, Submodule.zero_mem _, ?_⟩
    rw [mul_comm _ (a ^ (n + 1))]
    simp_rw [← mul_assoc]
    rw [← pow_add]; rw [add_zero]; rw [add_tsub_cancel_of_le h]
  · use 0
    simp_rw [zero_mul, zero_add]
    refine ⟨_, ?_, rfl⟩
    replace h : c <= n := Nat.lt_succ_iff.mp h
    have : (Multiset.card s + 1) * n + 1 - c = Multiset.card s * n + 1 + (n - c) := by
      rw [add_mul]; rw [one_mul]; rw [add_assoc]; rw [add_comm n 1]; rw [← add_assoc]; rw [add_tsub_assoc_of_le h]
    rw [this]; rw [pow_add]
    simp_rw [mul_assoc, mul_comm (s.sum ^ (Multiset.card s * n + 1)), ← mul_assoc]
    exact mul_mem_left _ _ hs

/--
theorem `sum_pow_mem_span_pow` / 定理 `sum_pow_mem_span_pow`

English:
theorem sum_pow_mem_span_pow
  given: {ι} (s : Finset ι) (f : ι -> α) (n : Nat)
  proof: by
  classical
  simpa only [Multiset.card_map, Multiset.map_map, comp_apply, Multiset.toFinset_map,
    Finset.coe_image, Finset.val_toFinset] using! pow_multiset_sum_mem_span_pow (s.1.map f) n

中文:
定理 sum_pow_mem_span_pow
  条件: {ι} (s : Finset ι) (f : ι -> α) (n : 自然数)
  证明: by
  classical
  simpa only [Multiset.card_map, Multiset.map_map, comp_apply, Multiset.toFinset_map,
    Finset.coe_image, Finset.val_toFinset] using! pow_multiset_sum_mem_span_pow (s.1.map f) n

Depends on / 依赖: Finset, Finset.coe_image, Finset.val_toFinset, Multiset, Multiset.card_map, Multiset.map_map, Multiset.toFinset_map, card_map, classical, coe_image, comp_apply, map_map, pow_multiset_sum_mem_span_pow, toFinset_map, val_toFinset
-/
theorem sum_pow_mem_span_pow {ι} (s : Finset ι) (f : ι -> α) (n : Nat) :
    (∑ i in s, f i) ^ (s.card * n + 1) in span ((fun i => f i ^ (n + 1)) '' s) := by
  classical
  simpa only [Multiset.card_map, Multiset.map_map, comp_apply, Multiset.toFinset_map,
    Finset.coe_image, Finset.val_toFinset] using! pow_multiset_sum_mem_span_pow (s.1.map f) n

/--
theorem `span_pow_eq_top` / 定理 `span_pow_eq_top`

English:
theorem span_pow_eq_top
  given: (s : Set α) (hs : span s = ⊤) (n : Nat)
  proof: by
  rw [eq_top_iff_one]
  rcases n with - | n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one]; rw [span]; rw [Finsupp.mem_span_iff_linearCombination] at hs
  rcases hs with ⟨f, hf⟩
  si

中文:
定理 span_pow_eq_top
  条件: (s : Set α) (hs : span s = ⊤) (n : 自然数)
  证明: by
  rw [eq_top_iff_one]
  rcases n with - | n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one]; rw [span]; rw [Finsupp.mem_span_iff_linearCombination] at hs
  rcases hs with ⟨f, hf⟩
  si

Depends on / 依赖: Finsupp, Finsupp.coe_lsum, Finsupp.linearCombination, Finsupp.mem_span_iff_linearCombination, Finsupp.sum, LinearMap, LinearMap.coe_smulRight, LinearMap.id_coe, Set.image_empty, coe_lsum, coe_smulRight, eq_empty_or_nonempty, eq_top_iff_one, f.support, id_coe, id_eq, image_empty, linearCombination, mem_span_iff_linearCombination, one_pow
-/
theorem span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : Nat) :
    span ((fun (x : α) => x ^ n) '' s) = ⊤ := by
  rw [eq_top_iff_one]
  rcases n with - | n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one]; rw [span]; rw [Finsupp.mem_span_iff_linearCombination] at hs
  rcases hs with ⟨f, hf⟩
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, smul_eq_mul] at hf
  have := sum_pow_mem_span_pow f.support (fun a => f a * a) n
  rw [hf]; rw [one_pow] at this
  refine span_le.mpr ?_ this
  rintro _ hx
  simp_rw [Set.mem_image] at hx
  rcases hx with ⟨x, _, rfl⟩
  have : span ({(x : α) ^ (n + 1)} : Set α) <= span ((fun x : α => x ^ (n + 1)) '' s) := by
    rw [span_le]; rw [Set.singleton_subset_iff]
    exact subset_span ⟨x, x.prop, rfl⟩
  refine this ?_
  rw [mul_pow]; rw [mem_span_singleton]
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩

/--
theorem `span_range_pow_eq_top` / 定理 `span_range_pow_eq_top`

English:
theorem span_range_pow_eq_top
  given: (s : Set α) (hs : span s = ⊤) (n : s -> Nat)
  proof: by
  have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span ((eq_top_iff_one _).mp hs)
  refine top_unique ((span_pow_eq_top _ ((eq_top_iff_one _).mpr mem) <|
    t.attach.sup fun x => n ⟨x, hts x.2⟩).ge.trans <| span_le.mpr ?_)
  rintro _ ⟨x, hxt, rfl⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup

中文:
定理 span_range_pow_eq_top
  条件: (s : Set α) (hs : span s = ⊤) (n : s -> 自然数)
  证明: by
  have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span ((eq_top_iff_one _).mp hs)
  refine top_unique ((span_pow_eq_top _ ((eq_top_iff_one _).mpr mem) <|
    t.attach.sup fun x => n ⟨x, hts x.2⟩).ge.trans <| span_le.mpr ?_)
  rintro _ ⟨x, hxt, rfl⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup

Depends on / 依赖: Finset, Finset.le_sup, Nat.sub_add_cancel, Submodule, Submodule.mem_span_finite_of_mem_span, attach, eq_top_iff_one, ge.trans, le_sup, mem_attach, mem_span_finite_of_mem_span, mul_mem_left, pow_add, simp_rw, span_le, span_le.mpr, span_pow_eq_top, sub_add_cancel, subset_span, t.attach.sup
-/
theorem span_range_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : s -> Nat) :
    span (Set.range fun x => x.1 ^ n x) = ⊤ := by
  have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span ((eq_top_iff_one _).mp hs)
  refine top_unique ((span_pow_eq_top _ ((eq_top_iff_one _).mpr mem) <|
    t.attach.sup fun x => n ⟨x, hts x.2⟩).ge.trans <| span_le.mpr ?_)
  rintro _ ⟨x, hxt, rfl⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup <| t.mem_attach ⟨x]; rw [hxt⟩)]
  simp_rw [pow_add]
  exact mul_mem_left _ _ (subset_span ⟨_, rfl⟩)

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {ι : Type*} {f : ι -> α} {s : Finset ι}
  proof: by
  classical
  rw [Finset.prod_eq_prod_sdiff_singleton_mul hi]
  exact Ideal.mul_mem_left _ _ hfi

中文:
定理 prod_mem
  结论: {ι : 类型} {f : ι -> α} {s : Finset ι}
  证明: by
  classical
  rw [Finset.prod_eq_prod_sdiff_singleton_mul hi]
  exact Ideal.mul_mem_left _ _ hfi

Depends on / 依赖: Finset, Finset.prod_eq_prod_sdiff_singleton_mul, Ideal.mul_mem_left, classical, mul_mem_left, prod_eq_prod_sdiff_singleton_mul
-/
theorem prod_mem {ι : Type*} {f : ι -> α} {s : Finset ι}
    (I : Ideal α) {i : ι} (hi : i in s) (hfi : f i in I) :
    ∏ i in s, f i in I := by
  classical
  rw [Finset.prod_eq_prod_sdiff_singleton_mul hi]
  exact Ideal.mul_mem_left _ _ hfi

/--
lemma `span_single_eq_top` / 引理 `span_single_eq_top`

English:
lemma span_single_eq_top
  statement: {ι : Type*} [DecidableEq ι] [Finite ι] (R : ι -> Type*)
  proof: by
  rw [_root_.eq_top_iff]
  rintro x -
  induction x using Pi.single_induction with
  | zero => simp
  | add f g hf hg => exact Ideal.add_mem _ hf hg
  | single i r =>
      rw [show Pi.single i r = Pi.single i r * Pi.single i 1 by simp [← Pi.single_mul_left]]
      exact Ideal.mul_mem_left _ _ (I

中文:
引理 span_single_eq_top
  结论: {ι : 类型} [DecidableEq ι] [Finite ι] (R : ι -> 类型)
  证明: by
  rw [_root_.eq_top_iff]
  rintro x -
  induction x using Pi.single_induction with
  | zero => simp
  | add f g hf hg => exact Ideal.add_mem _ hf hg
  | single i r =>
      rw [show Pi.single i r = Pi.single i r * Pi.single i 1 by simp [← Pi.single_mul_left]]
      exact Ideal.mul_mem_left _ _ (I

Depends on / 依赖: Ideal.add_mem, Ideal.mul_mem_left, Ideal.subset_span, Pi.single, Pi.single_induction, Pi.single_mul_left, _root_, _root_.eq_top_iff, add_mem, eq_top_iff, mul_mem_left, single, single_induction, single_mul_left, subset_span
-/
lemma span_single_eq_top {ι : Type*} [DecidableEq ι] [Finite ι] (R : ι -> Type*)
    [forall i, Semiring (R i)] : Ideal.span (Set.range fun i => (Pi.single i 1 : Π i, R i)) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  induction x using Pi.single_induction with
  | zero => simp
  | add f g hf hg => exact Ideal.add_mem _ hf hg
  | single i r =>
      rw [show Pi.single i r = Pi.single i r * Pi.single i 1 by simp [← Pi.single_mul_left]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Ideal

end CommSemiring

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

variable (K) in
/--
Definition of `equivFinTwo` / `equivFinTwo` 的定义

English:
definition equivFinTwo
  signature: : Ideal K ≃ Fin 2 where
  body: fun I => if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I => by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i => by fin_cases i <;> simp

中文:
定义 equivFinTwo
  签名: : Ideal K ≃ Fin 2 where
  定义体: fun I => if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I => by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i => by fin_cases i <;> simp
-/
noncomputable def equivFinTwo : Ideal K ≃ Fin 2 where
  toFun := fun I => if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I => by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i => by fin_cases i <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (Ideal K)
  body: let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

中文:
实例 :
  签名: Finite (Ideal K)
  定义体: let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

Depends on / 依赖: Classical, Classical.decEq, equivFinTwo
-/
instance : Finite (Ideal K) := let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

/--
Instance `isSimpleOrder` / 实例 `isSimpleOrder`

English:
instance isSimpleOrder
  signature: : IsSimpleOrder (Ideal K)
  body: ⟨eq_bot_or_top⟩

中文:
实例 isSimpleOrder
  签名: : IsSimpleOrder (Ideal K)
  定义体: ⟨eq_bot_or_top⟩

Depends on / 依赖: eq_bot_or_top, infer_instance, nhds_prod_eq
-/
instance isSimpleOrder : IsSimpleOrder (Ideal K) :=
  ⟨eq_bot_or_top⟩

end Ideal

end DivisionSemiring

-- TODO: consider moving the lemmas below out of the `Ring` namespace since they are
-- about `CommSemiring`s.
namespace Ring

variable {R : Type*} [CommSemiring R]

/--
theorem `exists_not_isUnit_of_not_isField` / 定理 `exists_not_isUnit_of_not_isField`

English:
theorem exists_not_isUnit_of_not_isField
  given: [Nontrivial R] (hf : ¬IsField R)
  proof: by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push Not at this ⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩

中文:
定理 exists_not_isUnit_of_not_isField
  条件: [Nontrivial R] (hf : ¬IsField R)
  证明: by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push Not at this ⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩

Depends on / 依赖: exists_pair_ne, infer_instance, isUnit_iff_exists_inv, mul_comm, nhds_pi, not_unit, simp_rw
-/
theorem exists_not_isUnit_of_not_isField [Nontrivial R] (hf : ¬IsField R) :
    exists (x : R) (_hx : x != (0 : R)), ¬IsUnit x := by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push Not at this ⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩

open Ideal in
/--
theorem `isField_iff_maximal_bot` / 定理 `isField_iff_maximal_bot`

English:
theorem isField_iff_maximal_bot
  given: [Nontrivial R]
  statement: IsField R ↔ (⊥ : Ideal R).IsMaximal
  proof: by
  refine ⟨fun h => let := h.toSemifield; bot_isMaximal, fun hmax => ?_⟩
  by_contra hf
  obtain ⟨x, hx0, hxu⟩ := exists_not_isUnit_of_not_isField hf
exact hx0 span_singleton_eq_bot.mp (hmax.eq_of_le (span_singleton_ne_top hxu) bot_le).symm

中文:
定理 isField_iff_maximal_bot
  条件: [Nontrivial R]
  结论: IsField R ↔ (⊥ : Ideal R).IsMaximal
  证明: by
  refine ⟨fun h => let := h.toSemifield; bot_isMaximal, fun hmax => ?_⟩
  by_contra hf
  obtain ⟨x, hx0, hxu⟩ := exists_not_isUnit_of_not_isField hf
exact hx0 span_singleton_eq_bot.mp (hmax.eq_of_le (span_singleton_ne_top hxu) bot_le).symm

Depends on / 依赖: bot_isMaximal, bot_le, eq_of_le, exists_not_isUnit_of_not_isField, h.toSemifield, hmax.eq_of_le, span_singleton_eq_bot, span_singleton_eq_bot.mp, span_singleton_ne_top, toSemifield
-/
theorem isField_iff_maximal_bot [Nontrivial R] : IsField R ↔ (⊥ : Ideal R).IsMaximal := by
  refine ⟨fun h => let := h.toSemifield; bot_isMaximal, fun hmax => ?_⟩
  by_contra hf
  obtain ⟨x, hx0, hxu⟩ := exists_not_isUnit_of_not_isField hf
exact hx0 span_singleton_eq_bot.mp (hmax.eq_of_le (span_singleton_ne_top hxu) bot_le).symm

/--
theorem `exists_maximal_of_not_isField` / 定理 `exists_maximal_of_not_isField`

English:
theorem exists_maximal_of_not_isField
  given: [Nontrivial R] (h : ¬ IsField R)
  proof: by
  contrapose! h
  simp only [← bot_lt_iff_ne_bot] at h
  refine isField_iff_maximal_bot.mpr ⟨⟨bot_ne_top, Ideal.maximal_of_no_maximal h⟩⟩

中文:
定理 exists_maximal_of_not_isField
  条件: [Nontrivial R] (h : ¬ IsField R)
  证明: by
  contrapose! h
  simp only [← bot_lt_iff_ne_bot] at h
  refine isField_iff_maximal_bot.mpr ⟨⟨bot_ne_top, Ideal.maximal_of_no_maximal h⟩⟩

Depends on / 依赖: Ideal.maximal_of_no_maximal, bot_lt_iff_ne_bot, bot_ne_top, contrapose, isField_iff_maximal_bot, isField_iff_maximal_bot.mpr, maximal_of_no_maximal
-/
theorem exists_maximal_of_not_isField [Nontrivial R] (h : ¬ IsField R) :
    exists p : Ideal R, p != ⊥ ∧ p.IsMaximal := by
  contrapose! h
  simp only [← bot_lt_iff_ne_bot] at h
  refine isField_iff_maximal_bot.mpr ⟨⟨bot_ne_top, Ideal.maximal_of_no_maximal h⟩⟩

/--
theorem `not_isField_of_ne_of_ne` / 定理 `not_isField_of_ne_of_ne`

English:
theorem not_isField_of_ne_of_ne
  given: [Nontrivial R] {I : Ideal R} (h_bot : I != ⊥) (h_top : I != ⊤)
  proof: by
  contrapose h_bot
  exact ((isField_iff_maximal_bot.mp h_bot).eq_of_le h_top bot_le).symm

中文:
定理 not_isField_of_ne_of_ne
  条件: [Nontrivial R] {I : Ideal R} (h_bot : I != ⊥) (h_top : I != ⊤)
  证明: by
  contrapose h_bot
  exact ((isField_iff_maximal_bot.mp h_bot).eq_of_le h_top bot_le).symm

Depends on / 依赖: bot_le, contrapose, eq_of_le, h_bot, h_top, isField_iff_maximal_bot, isField_iff_maximal_bot.mp
-/
theorem not_isField_of_ne_of_ne [Nontrivial R] {I : Ideal R} (h_bot : I != ⊥) (h_top : I != ⊤) :
    ¬ IsField R := by
  contrapose h_bot
  exact ((isField_iff_maximal_bot.mp h_bot).eq_of_le h_top bot_le).symm

/--
theorem `not_isField_iff_exists_ideal_bot_lt_and_lt_top` / 定理 `not_isField_iff_exists_ideal_bot_lt_and_lt_top`

English:
theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top
  given: [Nontrivial R]
  proof: by
  refine ⟨fun h => ?_, fun ⟨I, h_bot, h_top⟩ => not_isField_of_ne_of_ne h_bot.ne' h_top.ne⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, bot_lt_iff_ne_bot.mpr hI, lt_top_iff_ne_top.mpr hIm.ne_top⟩

中文:
定理 not_isField_iff_exists_ideal_bot_lt_and_lt_top
  条件: [Nontrivial R]
  证明: by
  refine ⟨fun h => ?_, fun ⟨I, h_bot, h_top⟩ => not_isField_of_ne_of_ne h_bot.ne' h_top.ne⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, bot_lt_iff_ne_bot.mpr hI, lt_top_iff_ne_top.mpr hIm.ne_top⟩

Depends on / 依赖: bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, exists_maximal_of_not_isField, hIm.ne_top, h_bot, h_bot.ne, h_top, h_top.ne, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, ne_top, not_isField_of_ne_of_ne
-/
theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] :
    ¬IsField R ↔ exists I : Ideal R, ⊥ < I ∧ I < ⊤ := by
  refine ⟨fun h => ?_, fun ⟨I, h_bot, h_top⟩ => not_isField_of_ne_of_ne h_bot.ne' h_top.ne⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, bot_lt_iff_ne_bot.mpr hI, lt_top_iff_ne_top.mpr hIm.ne_top⟩

/--
theorem `not_isField_iff_exists_prime` / 定理 `not_isField_iff_exists_prime`

English:
theorem not_isField_iff_exists_prime
  given: [Nontrivial R]
  proof: by
  refine ⟨fun h => ?_, fun ⟨I, h_bot, h_top⟩ => not_isField_of_ne_of_ne h_bot h_top.ne_top⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, hI, hIm.isPrime⟩

中文:
定理 not_isField_iff_exists_prime
  条件: [Nontrivial R]
  证明: by
  refine ⟨fun h => ?_, fun ⟨I, h_bot, h_top⟩ => not_isField_of_ne_of_ne h_bot h_top.ne_top⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, hI, hIm.isPrime⟩

Depends on / 依赖: exists_maximal_of_not_isField, hIm.isPrime, h_bot, h_top, h_top.ne_top, isPrime, ne_top, not_isField_of_ne_of_ne
-/
theorem not_isField_iff_exists_prime [Nontrivial R] :
    ¬IsField R ↔ exists p : Ideal R, p != ⊥ ∧ p.IsPrime := by
  refine ⟨fun h => ?_, fun ⟨I, h_bot, h_top⟩ => not_isField_of_ne_of_ne h_bot h_top.ne_top⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, hI, hIm.isPrime⟩

/--
theorem `isField_iff_isSimpleOrder_ideal` / 定理 `isField_iff_isSimpleOrder_ideal`

English:
theorem isField_iff_isSimpleOrder_ideal
  statement: IsField R ↔ IsSimpleOrder (Ideal R)
  proof: by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not]; rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  contrapose! +distrib
  simp_rw [not_lt_to

中文:
定理 isField_iff_isSimpleOrder_ideal
  结论: IsField R ↔ IsSimpleOrder (Ideal R)
  证明: by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not]; rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  contrapose! +distrib
  simp_rw [not_lt_to

Depends on / 依赖: Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top, contrapose, distrib, false_of_nontrivial_of_subsingleton, not_bot_lt_iff, not_iff_not, not_isField_iff_exists_ideal_bot_lt_and_lt_top, not_isField_of_subsingleton, not_lt_top_iff, simp_rw, subsingleton_or_nontrivial
-/
theorem isField_iff_isSimpleOrder_ideal : IsField R ↔ IsSimpleOrder (Ideal R) := by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not]; rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  contrapose! +distrib
  simp_rw [not_lt_top_iff, not_bot_lt_iff]
  exact ⟨fun h => ⟨h⟩, fun h => h.2⟩

/--
theorem `ne_bot_of_isMaximal_of_not_isField` / 定理 `ne_bot_of_isMaximal_of_not_isField`

English:
theorem ne_bot_of_isMaximal_of_not_isField
  statement: [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
  proof: by
  rintro rfl
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact hIbot.ne (max.eq_of_le hItop.ne bot_le)

中文:
定理 ne_bot_of_isMaximal_of_not_isField
  结论: [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
  证明: by
  rintro rfl
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact hIbot.ne (max.eq_of_le hItop.ne bot_le)

Depends on / 依赖: bot_le, eq_of_le, hIbot.ne, hItop.ne, max.eq_of_le, not_field, not_isField_iff_exists_ideal_bot_lt_and_lt_top, not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
-/
theorem ne_bot_of_isMaximal_of_not_isField [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
    (not_field : ¬IsField R) : M != ⊥ := by
  rintro rfl
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact hIbot.ne (max.eq_of_le hItop.ne bot_le)

end Ring

namespace Ideal

variable {R : Type*} [CommSemiring R] [Nontrivial R]

/--
theorem `bot_lt_of_maximal` / 定理 `bot_lt_of_maximal`

English:
theorem bot_lt_of_maximal
  given: (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R)
  statement: ⊥ < M
  proof: (Ring.ne_bot_of_isMaximal_of_not_isField hm non_field).bot_lt

中文:
定理 bot_lt_of_maximal
  条件: (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R)
  结论: ⊥ < M
  证明: (Ring.ne_bot_of_isMaximal_of_not_isField hm non_field).bot_lt

Depends on / 依赖: Ring.ne_bot_of_isMaximal_of_not_isField, bot_lt, ne_bot_of_isMaximal_of_not_isField, non_field
-/
theorem bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R) : ⊥ < M :=
  (Ring.ne_bot_of_isMaximal_of_not_isField hm non_field).bot_lt

end Ideal
