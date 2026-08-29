/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Interaction of big operators with indicator functions
-/

public section

namespace Finset

variable {ι κ α β : Type*} [CommMonoid β]

open Set

/-- Consider a product of `g i (f i)` over a finset. Suppose `g` is a function such as
`n ↦ (· ^ n)`, which maps a second argument of `1` to `1`. Then if `f` is replaced by the
corresponding multiplicative indicator function, the finset may be replaced by a possibly larger
finset without changing the value of the product. -/
@[to_additive /-- Consider a sum of `g i (f i)` over a finset. Suppose `g` is a function such as
`n ↦ (n • ·)`, which maps a second argument of `0` to `0` (or a weighted sum of `f i * h i` or
`f i • h i`, where `f` gives the weights that are multiplied by some other function `h`). Then if
`f` is replaced by the corresponding indicator function, the finset may be replaced by a possibly
larger finset without changing the value of the sum. -/]
/--
lemma `prod_mulIndicator_subset_of_eq_one` / 引理 `prod_mulIndicator_subset_of_eq_one`

English:
lemma prod_mulIndicator_subset_of_eq_one
  statement: [One α] (f : ι -> α) (g : ι -> α -> β) {s t : Finset ι}
  proof: by
  calc
    _ = ∏ i in s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn => by simp [hn, hg]]
_ = _ := prod_congr rfl fun i hi => congr_arg _ mulIndicator_of_mem hi f

中文:
引理 prod_mulIndicator_subset_of_eq_one
  结论: [幺 α] (f : ι -> α) (g : ι -> α -> β) {s t : 有限集 ι}
  证明: by
  calc
    _ = ∏ i in s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn => by simp [hn, hg]]
_ = _ := prod_congr rfl fun i hi => congr_arg _ mulIndicator_of_mem hi f

Depends on / 依赖: congr_arg, mulIndicator, mulIndicator_of_mem, prod_congr, prod_subset
-/
lemma prod_mulIndicator_subset_of_eq_one [One α] (f : ι -> α) (g : ι -> α -> β) {s t : Finset ι}
    (h : s subseteq t) (hg : forall a, g a 1 = 1) :
    ∏ i in t, g i (mulIndicator ↑s f i) = ∏ i in s, g i (f i) := by
  calc
    _ = ∏ i in s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn => by simp [hn, hg]]
_ = _ := prod_congr rfl fun i hi => congr_arg _ mulIndicator_of_mem hi f

/-- Taking the product of an indicator function over a possibly larger finset is the same as
taking the original function over the original finset. -/
@[to_additive /-- Summing an indicator function over a possibly larger `Finset` is the same as
summing the original function over the original finset. -/]
/--
lemma `prod_mulIndicator_subset` / 引理 `prod_mulIndicator_subset`

English:
lemma prod_mulIndicator_subset
  given: (f : ι -> β) {s t : Finset ι} (h : s subseteq t)
  proof: prod_mulIndicator_subset_of_eq_one _ (fun _ => id) h fun _ => rfl

@[to_additive]

中文:
引理 prod_mulIndicator_subset
  条件: (f : ι -> β) {s t : 有限集 ι} (h : s subseteq t)
  证明: prod_mulIndicator_subset_of_eq_one _ (fun _ => id) h fun _ => rfl

@[to_additive]

Depends on / 依赖: prod_mulIndicator_subset_of_eq_one
-/
lemma prod_mulIndicator_subset (f : ι -> β) {s t : Finset ι} (h : s subseteq t) :
    ∏ i in t, mulIndicator (↑s) f i = ∏ i in s, f i :=
  prod_mulIndicator_subset_of_eq_one _ (fun _ => id) h fun _ => rfl

@[to_additive]
/--
lemma `prod_mulIndicator_eq_prod_filter` / 引理 `prod_mulIndicator_eq_prod_filter`

English:
lemma prod_mulIndicator_eq_prod_filter
  statement: (s : Finset ι) (f : ι -> κ -> β) (t : ι -> Set κ) (g : ι -> κ)
  proof: by
refine (prod_filter_mul_prod_filter_not s (fun i => g i in t i) _).symm.trans
     Eq.trans (congr_arg₂ (· * ·) ?_ ?_) (mul_one _)
  · exact prod_congr rfl fun x hx => mulIndicator_of_mem (mem_filter.1 hx).2 _
  · exact prod_eq_one fun x hx => mulIndicator_of_notMem (mem_filter.1 hx).2 _

@[to_additive]

中文:
引理 prod_mulIndicator_eq_prod_filter
  结论: (s : 有限集 ι) (f : ι -> κ -> β) (t : ι -> 集合 κ) (g : ι -> κ)
  证明: by
refine (prod_filter_mul_prod_filter_not s (fun i => g i in t i) _).symm.trans
     Eq.trans (congr_arg₂ (· * ·) ?_ ?_) (mul_one _)
  · exact prod_congr rfl fun x hx => mulIndicator_of_mem (mem_filter.1 hx).2 _
  · exact prod_eq_one fun x hx => mulIndicator_of_notMem (mem_filter.1 hx).2 _

@[to_additive]

Depends on / 依赖: Eq.trans, mem_filter, mulIndicator_of_mem, mulIndicator_of_notMem, mul_one, prod_congr, prod_eq_one, prod_filter_mul_prod_filter_not, symm.trans
-/
lemma prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι -> κ -> β) (t : ι -> Set κ) (g : ι -> κ)
    [DecidablePred fun i => g i in t i] :
    ∏ i in s, mulIndicator (t i) (f i) (g i) = ∏ i in s with g i in t i, f i (g i) := by
refine (prod_filter_mul_prod_filter_not s (fun i => g i in t i) _).symm.trans
     Eq.trans (congr_arg₂ (· * ·) ?_ ?_) (mul_one _)
  · exact prod_congr rfl fun x hx => mulIndicator_of_mem (mem_filter.1 hx).2 _
  · exact prod_eq_one fun x hx => mulIndicator_of_notMem (mem_filter.1 hx).2 _

@[to_additive]
/--
lemma `prod_mulIndicator_eq_prod_inter` / 引理 `prod_mulIndicator_eq_prod_inter`

English:
lemma prod_mulIndicator_eq_prod_inter
  given: [DecidableEq ι] (s t : Finset ι) (f : ι -> β)
  proof: by
  rw [← filter_mem_eq_inter]; rw [prod_mulIndicator_eq_prod_filter]; rfl

@[to_additive]

中文:
引理 prod_mulIndicator_eq_prod_inter
  条件: [DecidableEq ι] (s t : 有限集 ι) (f : ι -> β)
  证明: by
  rw [← filter_mem_eq_inter]; rw [prod_mulIndicator_eq_prod_filter]; rfl

@[to_additive]

Depends on / 依赖: filter_mem_eq_inter, prod_mulIndicator_eq_prod_filter
-/
lemma prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι -> β) :
    ∏ i in s, (t : Set ι).mulIndicator f i = ∏ i in s inter t, f i := by
  rw [← filter_mem_eq_inter]; rw [prod_mulIndicator_eq_prod_filter]; rfl

@[to_additive]
/--
lemma `mulIndicator_prod` / 引理 `mulIndicator_prod`

English:
lemma mulIndicator_prod
  given: (s : Finset ι) (t : Set κ) (f : ι -> κ -> β)
  proof: map_prod (mulIndicatorHom _ _) _ _

@[to_additive]

中文:
引理 mulIndicator_prod
  条件: (s : 有限集 ι) (t : 集合 κ) (f : ι -> κ -> β)
  证明: map_prod (mulIndicatorHom _ _) _ _

@[to_additive]

Depends on / 依赖: map_prod, mulIndicatorHom
-/
lemma mulIndicator_prod (s : Finset ι) (t : Set κ) (f : ι -> κ -> β) :
    mulIndicator t (∏ i in s, f i) = ∏ i in s, mulIndicator t (f i) :=
  map_prod (mulIndicatorHom _ _) _ _

@[to_additive]
/--
lemma `mulIndicator_biUnion` / 引理 `mulIndicator_biUnion`

English:
lemma mulIndicator_biUnion
  statement: (s : Finset ι) (t : ι -> Set κ) {f : κ -> β}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    ext j
    rw [coe_cons]; rw [Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 hi)] at hs
    classical
    rw [prod_cons]; rw [cons_eq_insert]; rw [set_biUnion_insert]; rw [mulIndicator_union_of_notMem_inter]; rw [ih hs.1]
    exact (Set.disjoint_iff.mp (Set.disjoint_iUnion₂_right.mpr hs.2) ·)

@[to_additive]

中文:
引理 mulIndicator_biUnion
  结论: (s : 有限集 ι) (t : ι -> 集合 κ) {f : κ -> β}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    ext j
    rw [coe_cons]; rw [Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 hi)] at hs
    classical
    rw [prod_cons]; rw [cons_eq_insert]; rw [set_biUnion_insert]; rw [mulIndicator_union_of_notMem_inter]; rw [ih hs.1]
    exact (Set.disjoint_iff.mp (Set.disjoint_iUnion₂_right.mpr hs.2) ·)

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.mem_coe.not, Set.disjoint_iUnion, Set.disjoint_iff.mp, Set.pairwiseDisjoint_insert_of_notMem, _right.mpr, classical, coe_cons, cons_eq_insert, cons_induction, disjoint_iff, mem_coe, mulIndicator_union_of_notMem_inter, pairwiseDisjoint_insert_of_notMem, prod_cons, set_biUnion_insert
-/
lemma mulIndicator_biUnion (s : Finset ι) (t : ι -> Set κ) {f : κ -> β}
    (hs : (s : Set ι).PairwiseDisjoint t) :
    mulIndicator (⋃ i in s, t i) f = fun a => ∏ i in s, mulIndicator (t i) f a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    ext j
    rw [coe_cons]; rw [Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 hi)] at hs
    classical
    rw [prod_cons]; rw [cons_eq_insert]; rw [set_biUnion_insert]; rw [mulIndicator_union_of_notMem_inter]; rw [ih hs.1]
    exact (Set.disjoint_iff.mp (Set.disjoint_iUnion₂_right.mpr hs.2) ·)

@[to_additive]
/--
lemma `mulIndicator_biUnion_apply` / 引理 `mulIndicator_biUnion_apply`

English:
lemma mulIndicator_biUnion_apply
  statement: (s : Finset ι) (t : ι -> Set κ) {f : κ -> β}
  proof: by
  rw [mulIndicator_biUnion s t h]

中文:
引理 mulIndicator_biUnion_apply
  结论: (s : 有限集 ι) (t : ι -> 集合 κ) {f : κ -> β}
  证明: by
  rw [mulIndicator_biUnion s t h]

Depends on / 依赖: mulIndicator_biUnion
-/
lemma mulIndicator_biUnion_apply (s : Finset ι) (t : ι -> Set κ) {f : κ -> β}
    (h : (s : Set ι).PairwiseDisjoint t) (x : κ) :
    mulIndicator (⋃ i in s, t i) f x = ∏ i in s, mulIndicator (t i) f x := by
  rw [mulIndicator_biUnion s t h]

end Finset
