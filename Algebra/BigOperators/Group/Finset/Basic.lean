/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sum

/-!
# Big operators

In this file we prove theorems about products and sums indexed by a `Finset`.
-/

public section

assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction IsOrderedMonoid
assert_not_exists Finset.preimage Finset.sigma Fintype.piFinset
assert_not_exists Finset.piecewise Set.indicator MonoidHom.coeFn Function.support IsSquare

open Fin Function

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

namespace Finset

section CommMonoid
variable [CommMonoid M] {f g : ι -> M}

@[to_additive]
/--
lemma `prod_eq_fold` / 引理 `prod_eq_fold`

English:
lemma prod_eq_fold
  given: (s : Finset ι) (f : ι -> M)
  statement: ∏ i in s, f i = s.fold (β := M) (· * ·) 1 f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 prod_eq_fold
  条件: (s : Finset ι) (f : ι -> M)
  结论: ∏ i in s, f i = s.fold (β := M) (· * ·) 1 f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma prod_eq_fold (s : Finset ι) (f : ι -> M) : ∏ i in s, f i = s.fold (β := M) (· * ·) 1 f := rfl

@[to_additive (attr := simp)]
/--
theorem `prod_cons` / 定理 `prod_cons`

English:
theorem prod_cons
  given: (h : a ∉ s)
  statement: ∏ x in cons a s h, f x = f a * ∏ x in s, f x
  proof: fold_cons h

中文:
定理 prod_cons
  条件: (h : a ∉ s)
  结论: ∏ x in cons a s h, f x = f a * ∏ x in s, f x
  证明: fold_cons h

Depends on / 依赖: fold_cons
-/
theorem prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a * ∏ x in s, f x :=
  fold_cons h

/-- Variant of `prod_cons` not applied to a function. -/
@[to_additive (attr := grind =)]
/--
theorem `prod_cons'` / 定理 `prod_cons'`

English:
theorem prod_cons'
  given: (h : a ∉ s)
  proof: by
  funext f
  rw [Finset.prod_cons h]

@[to_additive (attr := simp)]

中文:
定理 prod_cons'
  条件: (h : a ∉ s)
  证明: by
  funext f
  rw [Finset.prod_cons h]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_cons, prod_cons
-/
theorem prod_cons' (h : a ∉ s) :
    Finset.prod (cons a s h) = fun (f : ι -> M) => f a * ∏ x in s, f x := by
  funext f
  rw [Finset.prod_cons h]

@[to_additive (attr := simp)]
/--
theorem `prod_insert` / 定理 `prod_insert`

English:
theorem prod_insert
  given: [DecidableEq ι]
  statement: a ∉ s -> ∏ x in insert a s, f x = f a * ∏ x in s, f x
  proof: fold_insert

中文:
定理 prod_insert
  条件: [DecidableEq ι]
  结论: a ∉ s -> ∏ x in insert a s, f x = f a * ∏ x in s, f x
  证明: fold_insert

Depends on / 依赖: fold_insert
-/
theorem prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert a s, f x = f a * ∏ x in s, f x :=
  fold_insert

/-- Variant of `prod_insert` not applied to a function. -/
@[to_additive (attr := grind =)]
/--
theorem `prod_insert'` / 定理 `prod_insert'`

English:
theorem prod_insert'
  given: [DecidableEq ι] (h : a ∉ s)
  proof: by
  funext f
  rw [Finset.prod_insert h]

中文:
定理 prod_insert'
  条件: [DecidableEq ι] (h : a ∉ s)
  证明: by
  funext f
  rw [Finset.prod_insert h]

Depends on / 依赖: Finset, Finset.prod_insert, prod_insert
-/
theorem prod_insert' [DecidableEq ι] (h : a ∉ s) :
    Finset.prod (insert a s) = fun (f : ι -> M) => f a * ∏ x in s, f x := by
  funext f
  rw [Finset.prod_insert h]

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`. -/
@[to_additive (attr := simp) /-- The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`. -/]
/--
theorem `prod_insert_of_eq_one_if_notMem` / 定理 `prod_insert_of_eq_one_if_notMem`

English:
theorem prod_insert_of_eq_one_if_notMem
  given: [DecidableEq ι] (h : a ∉ s -> f a = 1)
  proof: by
  by_cases a in s <;> grind

中文:
定理 prod_insert_of_eq_one_if_notMem
  条件: [DecidableEq ι] (h : a ∉ s -> f a = 1)
  证明: by
  by_cases a in s <;> grind
-/
theorem prod_insert_of_eq_one_if_notMem [DecidableEq ι] (h : a ∉ s -> f a = 1) :
    ∏ x in insert a s, f x = ∏ x in s, f x := by
  by_cases a in s <;> grind

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `f a = 1`. -/
@[to_additive /-- The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`. -/]
/--
theorem `prod_insert_one` / 定理 `prod_insert_one`

English:
theorem prod_insert_one
  given: [DecidableEq ι] (h : f a = 1)
  statement: ∏ x in insert a s, f x = ∏ x in s, f x
  proof: by
  simp [h]

@[to_additive (attr := simp)]

中文:
定理 prod_insert_one
  条件: [DecidableEq ι] (h : f a = 1)
  结论: ∏ x in insert a s, f x = ∏ x in s, f x
  证明: by
  simp [h]

@[to_additive (attr := simp)]
-/
theorem prod_insert_one [DecidableEq ι] (h : f a = 1) : ∏ x in insert a s, f x = ∏ x in s, f x := by
  simp [h]

@[to_additive (attr := simp)]
/--
theorem `prod_singleton` / 定理 `prod_singleton`

English:
theorem prod_singleton
  given: (f : ι -> M) (a : ι)
  statement: ∏ x in singleton a, f x = f a
  proof: Eq.trans fold_singleton mul_one _

中文:
定理 prod_singleton
  条件: (f : ι -> M) (a : ι)
  结论: ∏ x in singleton a, f x = f a
  证明: Eq.trans fold_singleton mul_one _

Depends on / 依赖: Eq.trans, fold_singleton, mul_one
-/
theorem prod_singleton (f : ι -> M) (a : ι) : ∏ x in singleton a, f x = f a :=
Eq.trans fold_singleton mul_one _

/-- Variant of `prod_singleton` not applied to a function. -/
@[to_additive (attr := grind =)]
/--
theorem `prod_singleton'` / 定理 `prod_singleton'`

English:
theorem prod_singleton'
  given: (a : ι)
  proof: by
  funext f
  simp

@[to_additive]

中文:
定理 prod_singleton'
  条件: (a : ι)
  证明: by
  funext f
  simp

@[to_additive]
-/
theorem prod_singleton' (a : ι) :
    Finset.prod (singleton a) = fun (f : ι -> M) => f a := by
  funext f
  simp

@[to_additive]
/--
theorem `prod_pair` / 定理 `prod_pair`

English:
theorem prod_pair
  given: [DecidableEq ι] {a b : ι} (h : a != b)
  proof: by
  rw [prod_insert (notMem_singleton.2 h)]; rw [prod_singleton]

中文:
定理 prod_pair
  条件: [DecidableEq ι] {a b : ι} (h : a != b)
  证明: by
  rw [prod_insert (notMem_singleton.2 h)]; rw [prod_singleton]

Depends on / 依赖: notMem_singleton, prod_insert, prod_singleton
-/
theorem prod_pair [DecidableEq ι] {a b : ι} (h : a != b) :
    (∏ x in ({a, b} : Finset ι), f x) = f a * f b := by
  rw [prod_insert (notMem_singleton.2 h)]; rw [prod_singleton]

/-- If a function is injective on a finset, products over the original finset or its image coincide.
See also `prod_image_of_pairwise_eq_one` for a version with weaker assumptions. -/
@[to_additive (attr := simp) /-- If a function is injective on a finset, sums over the original
finset or its image coincide.
See also `sum_image_of_pairwise_eq_zero` for a version with weaker assumptions. -/]
/--
theorem `prod_image` / 定理 `prod_image`

English:
theorem prod_image
  given: [DecidableEq ι] {s : Finset κ} {g : κ -> ι}
  proof: fold_image

@[to_additive]

中文:
定理 prod_image
  条件: [DecidableEq ι] {s : Finset κ} {g : κ -> ι}
  证明: fold_image

@[to_additive]

Depends on / 依赖: fold_image
-/
theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι} :
    Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x) :=
  fold_image

@[to_additive]
/--
lemma `prod_attach` / 引理 `prod_attach`

English:
lemma prod_attach
  given: (s : Finset ι) (f : ι -> M)
  statement: ∏ x in s.attach, f x = ∏ x in s, f x
  proof: by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[to_additive (attr := congr)]

中文:
引理 prod_attach
  条件: (s : Finset ι) (f : ι -> M)
  结论: ∏ x in s.attach, f x = ∏ x in s, f x
  证明: by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[to_additive (attr := congr)]

Depends on / 依赖: Subtype, Subtype.coe_injective.injOn, attach_image_val, classical, coe_injective, prod_image
-/
lemma prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.attach, f x = ∏ x in s, f x := by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[to_additive (attr := congr)]
/--
theorem `prod_congr` / 定理 `prod_congr`

English:
theorem prod_congr
  given: (h : s₁ = s₂)
  statement: (forall x in s₂, f x = g x) -> s₁.prod f = s₂.prod g
  proof: by
  rw [h]; exact fold_congr

@[to_additive]

中文:
定理 prod_congr
  条件: (h : s₁ = s₂)
  结论: (对任意 x in s₂, f x = g x) -> s₁.prod f = s₂.prod g
  证明: by
  rw [h]; exact fold_congr

@[to_additive]

Depends on / 依赖: fold_congr
-/
theorem prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x) -> s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr

@[to_additive]
/--
theorem `prod_eq_one` / 定理 `prod_eq_one`

English:
theorem prod_eq_one
  given: (h : forall x in s, f x = 1)
  statement: ∏ x in s, f x = 1
  proof: calc
  ∏ x in s, f x = ∏ _x in s, 1 := prod_congr rfl h
  _ = 1 := prod_const_one

中文:
定理 prod_eq_one
  条件: (h : 对任意 x in s, f x = 1)
  结论: ∏ x in s, f x = 1
  证明: calc
  ∏ x in s, f x = ∏ _x in s, 1 := prod_congr rfl h
  _ = 1 := prod_const_one
-/
theorem prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s, f x = 1 := calc
  ∏ x in s, f x = ∏ _x in s, 1 := prod_congr rfl h
  _ = 1 := prod_const_one

/-- In a monoid whose only unit is `1`, a product is equal to `1` iff all factors are `1`. -/
@[to_additive (attr := simp)
/-- In an additive monoid whose only unit is `0`, a sum is equal to `0` iff all terms are `0`. -/]
/--
lemma `prod_eq_one_iff` / 引理 `prod_eq_one_iff`

English:
lemma prod_eq_one_iff
  given: [Subsingleton Mˣ]
  statement: ∏ i in s, f i = 1 ↔ forall i in s, f i = 1
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

@[to_additive]

中文:
引理 prod_eq_one_iff
  条件: [Subsingleton Mˣ]
  结论: ∏ i in s, f i = 1 ↔ 对任意 i in s, f i = 1
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma prod_eq_one_iff [Subsingleton Mˣ] : ∏ i in s, f i = 1 ↔ forall i in s, f i = 1 := by
  induction s using Finset.cons_induction <;> simp [*]

@[to_additive]
/--
theorem `prod_disjUnion` / 定理 `prod_disjUnion`

English:
theorem prod_disjUnion
  given: (h)
  proof: by
  refine Eq.trans ?_ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]

中文:
定理 prod_disjUnion
  条件: (h)
  证明: by
  refine Eq.trans ?_ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]

Depends on / 依赖: Eq.trans, fold_disjUnion, one_mul
-/
theorem prod_disjUnion (h) :
    ∏ x in s₁.disjUnion s₂ h, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x := by
  refine Eq.trans ?_ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]
/--
theorem `prod_disjiUnion` / 定理 `prod_disjiUnion`

English:
theorem prod_disjiUnion
  given: (s : Finset κ) (t : κ -> Finset ι) (h)
  proof: by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]

中文:
定理 prod_disjiUnion
  条件: (s : Finset κ) (t : κ -> Finset ι) (h)
  证明: by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]

Depends on / 依赖: Eq.trans, Finset, Finset.disjUnion, Finset.fold, Finset.prod, Multiset, Multiset.fold, Multiset.prod, disjUnion, fold_disjiUnion, prod_const_one, prod_const_one.symm
-/
theorem prod_disjiUnion (s : Finset κ) (t : κ -> Finset ι) (h) :
    ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x := by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]
/--
theorem `prod_union_inter` / 定理 `prod_union_inter`

English:
theorem prod_union_inter
  given: [DecidableEq ι]
  proof: fold_union_inter

@[to_additive]

中文:
定理 prod_union_inter
  条件: [DecidableEq ι]
  证明: fold_union_inter

@[to_additive]

Depends on / 依赖: fold_union_inter
-/
theorem prod_union_inter [DecidableEq ι] :
    (∏ x in s₁ union s₂, f x) * ∏ x in s₁ inter s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x :=
  fold_union_inter

@[to_additive]
/--
theorem `prod_union` / 定理 `prod_union`

English:
theorem prod_union
  given: [DecidableEq ι] (h : Disjoint s₁ s₂)
  proof: by
  rw [← prod_union_inter]; rw [disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]

中文:
定理 prod_union
  条件: [DecidableEq ι] (h : Disjoint s₁ s₂)
  证明: by
  rw [← prod_union_inter]; rw [disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]

Depends on / 依赖: disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mp, mul_one, prod_union_inter
-/
theorem prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) :
    ∏ x in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x := by
  rw [← prod_union_inter]; rw [disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]
/--
theorem `prod_filter_mul_prod_filter_not` / 定理 `prod_filter_mul_prod_filter_not`

English:
theorem prod_filter_mul_prod_filter_not
  proof: by
  have := Classical.decEq ι
  rw [← prod_union (disjoint_filter_filter_not s s p)]; rw [filter_union_filter_not_eq]

@[to_additive]

中文:
定理 prod_filter_mul_prod_filter_not
  证明: by
  have := Classical.decEq ι
  rw [← prod_union (disjoint_filter_filter_not s s p)]; rw [filter_union_filter_not_eq]

@[to_additive]

Depends on / 依赖: Classical, Classical.decEq, disjoint_filter_filter_not, filter_union_filter_not_eq, prod_union
-/
theorem prod_filter_mul_prod_filter_not
    (s : Finset ι) (p : ι -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] (f : ι -> M) :
    (∏ x in s with p x, f x) * ∏ x in s with ¬p x, f x = ∏ x in s, f x := by
  have := Classical.decEq ι
  rw [← prod_union (disjoint_filter_filter_not s s p)]; rw [filter_union_filter_not_eq]

@[to_additive]
/--
lemma `prod_filter_not_mul_prod_filter` / 引理 `prod_filter_not_mul_prod_filter`

English:
lemma prod_filter_not_mul_prod_filter
  statement: (s : Finset ι) (p : ι -> Prop) [DecidablePred p]
  proof: by
  rw [mul_comm]; rw [prod_filter_mul_prod_filter_not]

中文:
引理 prod_filter_not_mul_prod_filter
  结论: (s : Finset ι) (p : ι -> 命题) [DecidablePred p]
  证明: by
  rw [mul_comm]; rw [prod_filter_mul_prod_filter_not]

Depends on / 依赖: mul_comm, prod_filter_mul_prod_filter_not
-/
lemma prod_filter_not_mul_prod_filter (s : Finset ι) (p : ι -> Prop) [DecidablePred p]
    [forall x, Decidable (¬p x)] (f : ι -> M) :
    (∏ x in s with ¬p x, f x) * ∏ x in s with p x, f x = ∏ x in s, f x := by
  rw [mul_comm]; rw [prod_filter_mul_prod_filter_not]

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive]
/--
theorem `prod_filter_xor` / 定理 `prod_filter_xor`

English:
theorem prod_filter_xor
  given: (p q : ι -> Prop) [DecidablePred p] [DecidablePred q]
  proof: by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor]

@[to_additive]

中文:
定理 prod_filter_xor
  条件: (p q : ι -> 命题) [DecidablePred p] [DecidablePred q]
  证明: by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor]

@[to_additive]

Depends on / 依赖: classical, disjoint_filter_and_not_filter, filter_or, prod_union
-/
theorem prod_filter_xor (p q : ι -> Prop) [DecidablePred p] [DecidablePred q] :
    (∏ x in s with (Xor (p x) (q x)), f x) =
      (∏ x in s with (p x ∧ ¬ q x), f x) * (∏ x in s with (q x ∧ ¬ p x), f x) := by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor]

@[to_additive]
/--
theorem `_root_.IsCompl.prod_mul_prod` / 定理 `_root_.IsCompl.prod_mul_prod`

English:
theorem _root_.IsCompl.prod_mul_prod
  given: [Fintype ι] {s t : Finset ι} (h : IsCompl s t) (f : ι -> M)
  proof: (Finset.prod_disjUnion h.disjoint).symm.trans by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

中文:
定理 _root_.IsCompl.prod_mul_prod
  条件: [Fintype ι] {s t : Finset ι} (h : IsCompl s t) (f : ι -> M)
  证明: (Finset.prod_disjUnion h.disjoint).symm.trans by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

Depends on / 依赖: Finset, Finset.disjUnion_eq_union, Finset.prod_disjUnion, Finset.sup_eq_union, classical, disjUnion_eq_union, disjoint, h.disjoint, h.sup_eq_top, prod_disjUnion, sup_eq_top, sup_eq_union, symm.trans
-/
theorem _root_.IsCompl.prod_mul_prod [Fintype ι] {s t : Finset ι} (h : IsCompl s t) (f : ι -> M) :
    (∏ i in s, f i) * ∏ i in t, f i = ∏ i, f i :=
(Finset.prod_disjUnion h.disjoint).symm.trans by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive /-- Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. -/]
/--
lemma `prod_mul_prod_compl` / 引理 `prod_mul_prod_compl`

English:
lemma prod_mul_prod_compl
  given: [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M)
  proof: IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]

中文:
引理 prod_mul_prod_compl
  条件: [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M)
  证明: IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]

Depends on / 依赖: IsCompl, IsCompl.prod_mul_prod, isCompl_compl, prod_mul_prod
-/
lemma prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M) :
    (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
/--
lemma `prod_compl_mul_prod` / 引理 `prod_compl_mul_prod`

English:
lemma prod_compl_mul_prod
  given: [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M)
  proof: (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]

中文:
引理 prod_compl_mul_prod
  条件: [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M)
  证明: (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]

Depends on / 依赖: isCompl_compl, prod_mul_prod, symm.prod_mul_prod
-/
lemma prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M) :
    (∏ i in sᶜ, f i) * ∏ i in s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
/--
theorem `prod_sdiff` / 定理 `prod_sdiff`

English:
theorem prod_sdiff
  given: [DecidableEq ι] (h : s₁ subseteq s₂)
  proof: by
  rw [← prod_union sdiff_disjoint]; rw [sdiff_union_of_subset h]

@[to_additive]

中文:
定理 prod_sdiff
  条件: [DecidableEq ι] (h : s₁ subseteq s₂)
  证明: by
  rw [← prod_union sdiff_disjoint]; rw [sdiff_union_of_subset h]

@[to_additive]

Depends on / 依赖: prod_union, sdiff_disjoint, sdiff_union_of_subset
-/
theorem prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) :
    (∏ x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x := by
  rw [← prod_union sdiff_disjoint]; rw [sdiff_union_of_subset h]

@[to_additive]
/--
theorem `prod_subset_one_on_sdiff` / 定理 `prod_subset_one_on_sdiff`

English:
theorem prod_subset_one_on_sdiff
  statement: [DecidableEq ι] (h : s₁ subseteq s₂) (hg : forall x in s₂ \ s₁, g x = 1)
  proof: by
  rw [← prod_sdiff h]; rw [prod_eq_one hg]; rw [one_mul]
  exact prod_congr rfl hfg

@[to_additive]

中文:
定理 prod_subset_one_on_sdiff
  结论: [DecidableEq ι] (h : s₁ subseteq s₂) (hg : 对任意 x in s₂ \ s₁, g x = 1)
  证明: by
  rw [← prod_sdiff h]; rw [prod_eq_one hg]; rw [one_mul]
  exact prod_congr rfl hfg

@[to_additive]

Depends on / 依赖: one_mul, prod_congr, prod_eq_one, prod_sdiff
-/
theorem prod_subset_one_on_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) (hg : forall x in s₂ \ s₁, g x = 1)
    (hfg : forall x in s₁, f x = g x) : ∏ i in s₁, f i = ∏ i in s₂, g i := by
  rw [← prod_sdiff h]; rw [prod_eq_one hg]; rw [one_mul]
  exact prod_congr rfl hfg

@[to_additive]
/--
theorem `prod_subset` / 定理 `prod_subset`

English:
theorem prod_subset
  given: (h : s₁ subseteq s₂) (hf : forall x in s₂, x ∉ s₁ -> f x = 1)
  proof: haveI := Classical.decEq ι
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]

中文:
定理 prod_subset
  条件: (h : s₁ subseteq s₂) (hf : 对任意 x in s₂, x ∉ s₁ -> f x = 1)
  证明: haveI := Classical.decEq ι
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Classical, Classical.decEq, isScalarTower_mid, prod_subset_one_on_sdiff
-/
theorem prod_subset (h : s₁ subseteq s₂) (hf : forall x in s₂, x ∉ s₁ -> f x = 1) :
    ∏ x in s₁, f x = ∏ x in s₂, f x :=
  haveI := Classical.decEq ι
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]
/--
theorem `prod_disjSum` / 定理 `prod_disjSum`

English:
theorem prod_disjSum
  given: (s : Finset ι) (t : Finset κ) (f : ι oplus κ -> M)
  proof: by
  rw [← map_inl_disjUnion_map_inr]; rw [prod_disjUnion]; rw [prod_map]; rw [prod_map]
  rfl

@[to_additive]

中文:
定理 prod_disjSum
  条件: (s : Finset ι) (t : Finset κ) (f : ι oplus κ -> M)
  证明: by
  rw [← map_inl_disjUnion_map_inr]; rw [prod_disjUnion]; rw [prod_map]; rw [prod_map]
  rfl

@[to_additive]

Depends on / 依赖: IsScalarTower, isScalarTower_right, map_inl_disjUnion_map_inr, prod_disjUnion, prod_map
-/
theorem prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι oplus κ -> M) :
    ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr]; rw [prod_disjUnion]; rw [prod_map]; rw [prod_map]
  rfl

@[to_additive]
/--
lemma `prod_sum_eq_prod_toLeft_mul_prod_toRight` / 引理 `prod_sum_eq_prod_toLeft_mul_prod_toRight`

English:
lemma prod_sum_eq_prod_toLeft_mul_prod_toRight
  given: (s : Finset (ι oplus κ)) (f : ι oplus κ -> M)
  proof: by
  rw [← Finset.toLeft_disjSum_toRight (u := s)]; rw [Finset.prod_disjSum]; rw [Finset.toLeft_disjSum]; rw [Finset.toRight_disjSum]

@[to_additive]

中文:
引理 prod_sum_eq_prod_toLeft_mul_prod_toRight
  条件: (s : Finset (ι oplus κ)) (f : ι oplus κ -> M)
  证明: by
  rw [← Finset.toLeft_disjSum_toRight (u := s)]; rw [Finset.prod_disjSum]; rw [Finset.toLeft_disjSum]; rw [Finset.toRight_disjSum]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_disjSum, Finset.toLeft_disjSum, Finset.toLeft_disjSum_toRight, Finset.toRight_disjSum, prod_disjSum, toLeft_disjSum, toLeft_disjSum_toRight, toRight_disjSum
-/
lemma prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι oplus κ)) (f : ι oplus κ -> M) :
    ∏ x in s, f x = (∏ x in s.toLeft, f (Sum.inl x)) * ∏ x in s.toRight, f (Sum.inr x) := by
  rw [← Finset.toLeft_disjSum_toRight (u := s)]; rw [Finset.prod_disjSum]; rw [Finset.toLeft_disjSum]; rw [Finset.toRight_disjSum]

@[to_additive]
/--
theorem `prod_sumElim` / 定理 `prod_sumElim`

English:
theorem prod_sumElim
  given: (s : Finset ι) (t : Finset κ) (f : ι -> M) (g : κ -> M)
  proof: by simp

中文:
定理 prod_sumElim
  条件: (s : Finset ι) (t : Finset κ) (f : ι -> M) (g : κ -> M)
  证明: by simp
-/
theorem prod_sumElim (s : Finset ι) (t : Finset κ) (f : ι -> M) (g : κ -> M) :
    ∏ x in s.disjSum t, Sum.elim f g x = (∏ x in s, f x) * ∏ x in t, g x := by simp

/-- Given a finite family of pairwise disjoint finsets, the product over their union is the product
of the products over the sets.
See also `prod_biUnion_of_pairwise_eq_one` for a version with weaker assumptions. -/
@[to_additive /-- Given a finite family of pairwise disjoint finsets, the sum over their union is
the sum of the sums over the sets.
See also `sum_biUnion_of_pairwise_eq_zero` for a version with weaker assumptions. -/]
/--
theorem `prod_biUnion` / 定理 `prod_biUnion`

English:
theorem prod_biUnion
  statement: [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι}
  proof: by
  rw [← disjiUnion_eq_biUnion _ _ hs]; rw [prod_disjiUnion]

中文:
定理 prod_biUnion
  结论: [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι}
  证明: by
  rw [← disjiUnion_eq_biUnion _ _ hs]; rw [prod_disjiUnion]

Depends on / 依赖: disjiUnion_eq_biUnion, prod_disjiUnion
-/
theorem prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x in s.biUnion t, f x = ∏ x in s, ∏ i in t x, f i := by
  rw [← disjiUnion_eq_biUnion _ _ hs]; rw [prod_disjiUnion]

section bij
variable {s : Finset ι} {t : Finset κ} {f : ι -> M} {g : κ -> M}

@[to_additive]
/--
lemma `prod_of_injOn` / 引理 `prod_of_injOn`

English:
lemma prod_of_injOn
  statement: (e : ι -> κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
  proof: by
  classical
exact (prod_nbij e (fun a => mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans
prod_subset (image_subset_iff.2 hest) by simpa using h'

中文:
引理 prod_of_injOn
  结论: (e : ι -> κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
  证明: by
  classical
exact (prod_nbij e (fun a => mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans
prod_subset (image_subset_iff.2 hest) by simpa using h'

Depends on / 依赖: Set.surjOn_image, classical, image_subset_iff, mem_image_of_mem, prod_nbij, prod_subset, surjOn_image
-/
lemma prod_of_injOn (e : ι -> κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
    (h' : forall i in t, i ∉ e '' s -> g i = 1) (h : forall i in s, f i = g (e i)) :
    ∏ i in s, f i = ∏ j in t, g j := by
  classical
exact (prod_nbij e (fun a => mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans
prod_subset (image_subset_iff.2 hest) by simpa using h'

variable [DecidableEq κ]

@[to_additive]
/--
lemma `prod_fiberwise_eq_prod_filter` / 引理 `prod_fiberwise_eq_prod_filter`

English:
lemma prod_fiberwise_eq_prod_filter
  given: (s : Finset ι) (t : Finset κ) (g : ι -> κ) (f : ι -> M)
  proof: by
  rw [← prod_disjiUnion]; rw [disjiUnion_filter_eq]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]

中文:
引理 prod_fiberwise_eq_prod_filter
  条件: (s : Finset ι) (t : Finset κ) (g : ι -> κ) (f : ι -> M)
  证明: by
  rw [← prod_disjiUnion]; rw [disjiUnion_filter_eq]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]

Depends on / 依赖: adaptation_note, copied, disjiUnion_filter_eq, disjoint_left, mem_filter, pairwiseDisjoint_fibers, private, prod_disjiUnion, simp_rw
-/
lemma prod_fiberwise_eq_prod_filter (s : Finset ι) (t : Finset κ) (g : ι -> κ) (f : ι -> M) :
    ∏ j in t, ∏ i in s with g i = j, f i = ∏ i in s with g i in t, f i := by
  rw [← prod_disjiUnion]; rw [disjiUnion_filter_eq]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]
/--
lemma `prod_fiberwise_eq_prod_filter'` / 引理 `prod_fiberwise_eq_prod_filter'`

English:
lemma prod_fiberwise_eq_prod_filter'
  given: (s : Finset ι) (t : Finset κ) (g : ι -> κ) (f : κ -> M)
  proof: by
  calc
    _ = ∏ j in t, ∏ i in s with g i = j, f (g i) :=
        prod_congr rfl fun j _ => prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
    _ = _ := prod_fiberwise_eq_prod_filter _ _ _ _

@[to_additive]

中文:
引理 prod_fiberwise_eq_prod_filter'
  条件: (s : Finset ι) (t : Finset κ) (g : ι -> κ) (f : κ -> M)
  证明: by
  calc
    _ = ∏ j in t, ∏ i in s with g i = j, f (g i) :=
        prod_congr rfl fun j _ => prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
    _ = _ := prod_fiberwise_eq_prod_filter _ _ _ _

@[to_additive]

Depends on / 依赖: mem_filter, prod_congr, prod_fiberwise_eq_prod_filter
-/
lemma prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι -> κ) (f : κ -> M) :
    ∏ j in t, ∏ i in s with g i = j, f j = ∏ i in s with g i in t, f (g i) := by
  calc
    _ = ∏ j in t, ∏ i in s with g i = j, f (g i) :=
        prod_congr rfl fun j _ => prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
    _ = _ := prod_fiberwise_eq_prod_filter _ _ _ _

@[to_additive]
/--
lemma `prod_fiberwise_of_maps_to` / 引理 `prod_fiberwise_of_maps_to`

English:
lemma prod_fiberwise_of_maps_to
  given: {g : ι -> κ} (h : forall i in s, g i in t) (f : ι -> M)
  proof: by
  rw [← prod_disjiUnion]; rw [disjiUnion_filter_eq_of_maps_to h]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]

中文:
引理 prod_fiberwise_of_maps_to
  条件: {g : ι -> κ} (h : 对任意 i in s, g i in t) (f : ι -> M)
  证明: by
  rw [← prod_disjiUnion]; rw [disjiUnion_filter_eq_of_maps_to h]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]

Depends on / 依赖: adaptation_note, copied, disjiUnion_filter_eq_of_maps_to, disjoint_left, mem_filter, pairwiseDisjoint_fibers, private, prod_disjiUnion, simp_rw
-/
lemma prod_fiberwise_of_maps_to {g : ι -> κ} (h : forall i in s, g i in t) (f : ι -> M) :
    ∏ j in t, ∏ i in s with g i = j, f i = ∏ i in s, f i := by
  rw [← prod_disjiUnion]; rw [disjiUnion_filter_eq_of_maps_to h]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]
/--
lemma `prod_fiberwise_of_maps_to'` / 引理 `prod_fiberwise_of_maps_to'`

English:
lemma prod_fiberwise_of_maps_to'
  given: {g : ι -> κ} (h : forall i in s, g i in t) (f : κ -> M)
  proof: by
  calc
    _ = ∏ j in t, ∏ i in s with g i = j, f (g i) :=
        prod_congr rfl fun y _ => prod_congr rfl fun x hx => by rw [(mem_filter.1 hx).2]
    _ = _ := prod_fiberwise_of_maps_to h _

中文:
引理 prod_fiberwise_of_maps_to'
  条件: {g : ι -> κ} (h : 对任意 i in s, g i in t) (f : κ -> M)
  证明: by
  calc
    _ = ∏ j in t, ∏ i in s with g i = j, f (g i) :=
        prod_congr rfl fun y _ => prod_congr rfl fun x hx => by rw [(mem_filter.1 hx).2]
    _ = _ := prod_fiberwise_of_maps_to h _

Depends on / 依赖: mem_filter, prod_congr, prod_fiberwise_of_maps_to
-/
lemma prod_fiberwise_of_maps_to' {g : ι -> κ} (h : forall i in s, g i in t) (f : κ -> M) :
    ∏ j in t, ∏ i in s with g i = j, f j = ∏ i in s, f (g i) := by
  calc
    _ = ∏ j in t, ∏ i in s with g i = j, f (g i) :=
        prod_congr rfl fun y _ => prod_congr rfl fun x hx => by rw [(mem_filter.1 hx).2]
    _ = _ := prod_fiberwise_of_maps_to h _

variable [Fintype κ]

@[to_additive]
/--
lemma `prod_fiberwise` / 引理 `prod_fiberwise`

English:
lemma prod_fiberwise
  given: (s : Finset ι) (g : ι -> κ) (f : ι -> M)
  proof: prod_fiberwise_of_maps_to (fun _ _ => mem_univ _) _

@[to_additive]

中文:
引理 prod_fiberwise
  条件: (s : Finset ι) (g : ι -> κ) (f : ι -> M)
  证明: prod_fiberwise_of_maps_to (fun _ _ => mem_univ _) _

@[to_additive]

Depends on / 依赖: mem_univ, prod_fiberwise_of_maps_to
-/
lemma prod_fiberwise (s : Finset ι) (g : ι -> κ) (f : ι -> M) :
    ∏ j, ∏ i in s with g i = j, f i = ∏ i in s, f i :=
  prod_fiberwise_of_maps_to (fun _ _ => mem_univ _) _

@[to_additive]
/--
lemma `prod_fiberwise'` / 引理 `prod_fiberwise'`

English:
lemma prod_fiberwise'
  given: (s : Finset ι) (g : ι -> κ) (f : κ -> M)
  proof: prod_fiberwise_of_maps_to' (fun _ _ => mem_univ _) _

中文:
引理 prod_fiberwise'
  条件: (s : Finset ι) (g : ι -> κ) (f : κ -> M)
  证明: prod_fiberwise_of_maps_to' (fun _ _ => mem_univ _) _

Depends on / 依赖: mem_univ, prod_fiberwise_of_maps_to
-/
lemma prod_fiberwise' (s : Finset ι) (g : ι -> κ) (f : κ -> M) :
    ∏ j, ∏ i in s with g i = j, f j = ∏ i in s, f (g i) :=
  prod_fiberwise_of_maps_to' (fun _ _ => mem_univ _) _

end bij

@[to_additive (attr := simp)]
/--
lemma `prod_diag` / 引理 `prod_diag`

English:
lemma prod_diag
  given: (s : Finset ι) (f : ι × ι -> M)
  proof: by
  simp [diag]

@[to_additive]

中文:
引理 prod_diag
  条件: (s : Finset ι) (f : ι × ι -> M)
  证明: by
  simp [diag]

@[to_additive]
-/
lemma prod_diag (s : Finset ι) (f : ι × ι -> M) :
    ∏ i in s.diag, f i = ∏ i in s, f (i, i) := by
  simp [diag]

@[to_additive]
/--
theorem `prod_image'` / 定理 `prod_image'`

English:
theorem prod_image'
  statement: [DecidableEq ι] {s : Finset κ} {g : κ -> ι} (h : κ -> M)
  proof: calc
    ∏ a in s.image g, f a = ∏ a in s.image g, ∏ j in s with g j = a, h j :=
      (prod_congr rfl) fun _a hx =>
        let ⟨i, his, hi⟩ := mem_image.1 hx
        hi ▸ eq i his
    _ = ∏ i in s, h i := prod_fiberwise_of_maps_to (fun _ => mem_image_of_mem g) _

@[to_additive]

中文:
定理 prod_image'
  结论: [DecidableEq ι] {s : Finset κ} {g : κ -> ι} (h : κ -> M)
  证明: calc
    ∏ a in s.image g, f a = ∏ a in s.image g, ∏ j in s with g j = a, h j :=
      (prod_congr rfl) fun _a hx =>
        let ⟨i, his, hi⟩ := mem_image.1 hx
        hi ▸ eq i his
    _ = ∏ i in s, h i := prod_fiberwise_of_maps_to (fun _ => mem_image_of_mem g) _

@[to_additive]

Depends on / 依赖: mem_image, mem_image_of_mem, prod_congr, prod_fiberwise_of_maps_to, s.image
-/
theorem prod_image' [DecidableEq ι] {s : Finset κ} {g : κ -> ι} (h : κ -> M)
    (eq : forall i in s, f (g i) = ∏ j in s with g j = g i, h j) :
    ∏ a in s.image g, f a = ∏ i in s, h i :=
  calc
    ∏ a in s.image g, f a = ∏ a in s.image g, ∏ j in s with g j = a, h j :=
      (prod_congr rfl) fun _a hx =>
        let ⟨i, his, hi⟩ := mem_image.1 hx
        hi ▸ eq i his
    _ = ∏ i in s, h i := prod_fiberwise_of_maps_to (fun _ => mem_image_of_mem g) _

@[to_additive]
/--
theorem `prod_mul_distrib` / 定理 `prod_mul_distrib`

English:
theorem prod_mul_distrib
  statement: ∏ x in s, f x * g x = (∏ x in s, f x) * ∏ x in s, g x
  proof: Eq.trans (by rw [one_mul]; rfl) fold_op_distrib

@[to_additive]

中文:
定理 prod_mul_distrib
  结论: ∏ x in s, f x * g x = (∏ x in s, f x) * ∏ x in s, g x
  证明: Eq.trans (by rw [one_mul]; rfl) fold_op_distrib

@[to_additive]

Depends on / 依赖: Eq.trans, fold_op_distrib, one_mul
-/
theorem prod_mul_distrib : ∏ x in s, f x * g x = (∏ x in s, f x) * ∏ x in s, g x :=
  Eq.trans (by rw [one_mul]; rfl) fold_op_distrib

@[to_additive]
/--
lemma `prod_mul_prod_comm` / 引理 `prod_mul_prod_comm`

English:
lemma prod_mul_prod_comm
  given: (f g h i : ι -> M)
  proof: by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]

中文:
引理 prod_mul_prod_comm
  条件: (f g h i : ι -> M)
  证明: by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]

Depends on / 依赖: mul_mul_mul_comm, prod_mul_distrib, simp_rw
-/
lemma prod_mul_prod_comm (f g h i : ι -> M) :
    (∏ a in s, f a * g a) * ∏ a in s, h a * i a = (∏ a in s, f a * h a) * ∏ a in s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
/--
theorem `prod_filter_of_ne` / 定理 `prod_filter_of_ne`

English:
theorem prod_filter_of_ne
  given: {p : ι -> Prop} [DecidablePred p] (hp : forall x in s, f x != 1 -> p x)
  proof: (prod_subset (filter_subset _ _)) fun x => by
    rw [not_imp_comm]; rw [mem_filter]
    exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

中文:
定理 prod_filter_of_ne
  条件: {p : ι -> 命题} [DecidablePred p] (hp : 对任意 x in s, f x != 1 -> p x)
  证明: (prod_subset (filter_subset _ _)) fun x => by
    rw [not_imp_comm]; rw [mem_filter]
    exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

Depends on / 依赖: filter_subset, mem_filter, not_imp_comm, prod_subset
-/
theorem prod_filter_of_ne {p : ι -> Prop} [DecidablePred p] (hp : forall x in s, f x != 1 -> p x) :
    ∏ x in s with p x, f x = ∏ x in s, f x :=
  (prod_subset (filter_subset _ _)) fun x => by
    rw [not_imp_comm]; rw [mem_filter]
    exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

-- If we use `[DecidableEq M]` here, some rewrites fail because they find a wrong `Decidable`
-- instance first; `{∀ x, Decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
/--
theorem `prod_filter_ne_one` / 定理 `prod_filter_ne_one`

English:
theorem prod_filter_ne_one
  given: (s : Finset ι) [forall x, Decidable (f x != 1)]
  proof: prod_filter_of_ne fun _ _ => id

@[to_additive]

中文:
定理 prod_filter_ne_one
  条件: (s : Finset ι) [对任意 x, Decidable (f x != 1)]
  证明: prod_filter_of_ne fun _ _ => id

@[to_additive]

Depends on / 依赖: prod_filter_of_ne
-/
theorem prod_filter_ne_one (s : Finset ι) [forall x, Decidable (f x != 1)] :
    ∏ x in s with f x != 1, f x = ∏ x in s, f x :=
  prod_filter_of_ne fun _ _ => id

@[to_additive]
/--
theorem `prod_filter` / 定理 `prod_filter`

English:
theorem prod_filter
  given: (p : ι -> Prop) [DecidablePred p] (f : ι -> M)
  proof: calc
    ∏ a in s with p a, f a = ∏ a in s with p a, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a in s, if p a then f a else 1 := by
      { refine prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter]; rw [no

中文:
定理 prod_filter
  条件: (p : ι -> 命题) [DecidablePred p] (f : ι -> M)
  证明: calc
    ∏ a in s with p a, f a = ∏ a in s with p a, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a in s, if p a then f a else 1 := by
      { refine prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter]; rw [no

Depends on / 依赖: filter_subset, if_neg, if_pos, mem_filter, not_and, prod_congr, prod_subset
-/
theorem prod_filter (p : ι -> Prop) [DecidablePred p] (f : ι -> M) :
    ∏ a in s with p a, f a = ∏ a in s, if p a then f a else 1 :=
  calc
    ∏ a in s with p a, f a = ∏ a in s with p a, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a in s, if p a then f a else 1 := by
      { refine prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter]; rw [not_and] at h
        exact if_neg (by simpa using h hs) }

@[to_additive]
/--
theorem `prod_eq_single_of_mem` / 定理 `prod_eq_single_of_mem`

English:
theorem prod_eq_single_of_mem
  statement: {s : Finset ι} {f : ι -> M} (a : ι) (h : a in s)
  proof: by
  calc
    ∏ x in s, f x = ∏ x in {a}, f x := by
      { refine (prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]

中文:
定理 prod_eq_single_of_mem
  结论: {s : Finset ι} {f : ι -> M} (a : ι) (h : a in s)
  证明: by
  calc
    ∏ x in s, f x = ∏ x in {a}, f x := by
      { refine (prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]

Depends on / 依赖: mem_singleton, prod_singleton, prod_subset
-/
theorem prod_eq_single_of_mem {s : Finset ι} {f : ι -> M} (a : ι) (h : a in s)
    (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s, f x = f a := by
  calc
    ∏ x in s, f x = ∏ x in {a}, f x := by
      { refine (prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]
/--
theorem `prod_eq_single` / 定理 `prod_eq_single`

English:
theorem prod_eq_single
  statement: {s : Finset ι} {f : ι -> M} (a : ι) (h₀ : forall b in s, b != a -> f b = 1)
  proof: haveI := Classical.decEq ι
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
(prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans
      prod_const_one.trans (h₁ this).symm

@[to_additive (attr := simp)]

中文:
定理 prod_eq_single
  结论: {s : Finset ι} {f : ι -> M} (a : ι) (h₀ : 对任意 b in s, b != a -> f b = 1)
  证明: haveI := Classical.decEq ι
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
(prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans
      prod_const_one.trans (h₁ this).symm

@[to_additive (attr := simp)]

Depends on / 依赖: Classical, Classical.decEq, prod_congr, prod_const_one, prod_const_one.trans, prod_eq_single_of_mem
-/
theorem prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι) (h₀ : forall b in s, b != a -> f b = 1)
    (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f x = f a :=
  haveI := Classical.decEq ι
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
(prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans
      prod_const_one.trans (h₁ this).symm

@[to_additive (attr := simp)]
/--
lemma `prod_ite_mem_eq` / 引理 `prod_ite_mem_eq`

English:
lemma prod_ite_mem_eq
  given: [Fintype ι] (s : Finset ι) (f : ι -> M) [DecidablePred (· in s)]
  proof: by
  rw [← Finset.prod_filter]; congr; grind

@[to_additive]

中文:
引理 prod_ite_mem_eq
  条件: [Fintype ι] (s : Finset ι) (f : ι -> M) [DecidablePred (· in s)]
  证明: by
  rw [← Finset.prod_filter]; congr; grind

@[to_additive]

Depends on / 依赖: CommRing, Finset, Finset.prod_filter, Subring, Subring.center, center, prod_filter
-/
lemma prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : ι -> M) [DecidablePred (· in s)] :
    (∏ i, if i in s then f i else 1) = ∏ i in s, f i := by
  rw [← Finset.prod_filter]; congr; grind

@[to_additive]
/--
lemma `prod_eq_ite` / 引理 `prod_eq_ite`

English:
lemma prod_eq_ite
  statement: [DecidableEq ι] {s : Finset ι} {f : ι -> M} (a : ι)
  proof: by
  by_cases h : a in s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : forall b in s, f b = 1 := by grind
    simp +contextual [h₀]

@[to_additive]

中文:
引理 prod_eq_ite
  结论: [DecidableEq ι] {s : Finset ι} {f : ι -> M} (a : ι)
  证明: by
  by_cases h : a in s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : forall b in s, f b = 1 := by grind
    simp +contextual [h₀]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_single_of_mem, contextual, prod_eq_single_of_mem, replace
-/
lemma prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι -> M} (a : ι)
    (h₀ : forall b in s, b != a -> f b = 1) :
    ∏ x in s, f x = if a in s then f a else 1 := by
  by_cases h : a in s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : forall b in s, f b = 1 := by grind
    simp +contextual [h₀]

@[to_additive]
/--
lemma `prod_union_eq_left` / 引理 `prod_union_eq_left`

English:
lemma prod_union_eq_left
  given: [DecidableEq ι] (hs : forall a in s₂, a ∉ s₁ -> f a = 1)
  proof: Eq.symm
    prod_subset subset_union_left fun _a ha ha' => hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]

中文:
引理 prod_union_eq_left
  条件: [DecidableEq ι] (hs : 对任意 a in s₂, a ∉ s₁ -> f a = 1)
  证明: Eq.symm
    prod_subset subset_union_left fun _a ha ha' => hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]

Depends on / 依赖: Eq.symm, mem_union, prod_subset, resolve_left, subset_union_left
-/
lemma prod_union_eq_left [DecidableEq ι] (hs : forall a in s₂, a ∉ s₁ -> f a = 1) :
    ∏ a in s₁ union s₂, f a = ∏ a in s₁, f a :=
Eq.symm
    prod_subset subset_union_left fun _a ha ha' => hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]
/--
lemma `prod_union_eq_right` / 引理 `prod_union_eq_right`

English:
lemma prod_union_eq_right
  given: [DecidableEq ι] (hs : forall a in s₁, a ∉ s₂ -> f a = 1)
  proof: by rw [union_comm, prod_union_eq_left hs]

中文:
引理 prod_union_eq_right
  条件: [DecidableEq ι] (hs : 对任意 a in s₁, a ∉ s₂ -> f a = 1)
  证明: by rw [union_comm, prod_union_eq_left hs]

Depends on / 依赖: prod_union_eq_left, union_comm
-/
lemma prod_union_eq_right [DecidableEq ι] (hs : forall a in s₁, a ∉ s₂ -> f a = 1) :
    ∏ a in s₁ union s₂, f a = ∏ a in s₂, f a := by rw [union_comm, prod_union_eq_left hs]

/-- The products of two functions `f g : ι → M` over finite sets `s₁ s₂ : Finset ι`
are equal if the functions agree on `s₁ ∩ s₂`, `f = 1` and `g = 1` on the respective
set differences. -/
@[to_additive /-- The sum of two functions `f g : ι → M` over finite sets `s₁ s₂ : Finset ι`
are equal if the functions agree on `s₁ ∩ s₂`, `f = 0` and `g = 0` on the respective
set differences. -/]
/--
lemma `prod_congr_of_eq_on_inter` / 引理 `prod_congr_of_eq_on_inter`

English:
lemma prod_congr_of_eq_on_inter
  statement: {ι M : Type*} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M]
  proof: by
  classical
  conv_lhs => rw [← sdiff_union_inter s₁ s₂, prod_union_eq_right (by simp_all)]
  conv_rhs => rw [← sdiff_union_inter s₂ s₁, prod_union_eq_right (by simp_all), inter_comm]
  exact prod_congr rfl (by simpa)

@[to_additive]

中文:
引理 prod_congr_of_eq_on_inter
  结论: {ι M : 类型} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M]
  证明: by
  classical
  conv_lhs => rw [← sdiff_union_inter s₁ s₂, prod_union_eq_right (by simp_all)]
  conv_rhs => rw [← sdiff_union_inter s₂ s₁, prod_union_eq_right (by simp_all), inter_comm]
  exact prod_congr rfl (by simpa)

@[to_additive]

Depends on / 依赖: classical, conv_lhs, conv_rhs, inter_comm, prod_congr, prod_union_eq_right, sdiff_union_inter
-/
lemma prod_congr_of_eq_on_inter {ι M : Type*} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M]
    (h₁ : forall a in s₁, a ∉ s₂ -> f a = 1) (h₂ : forall a in s₂, a ∉ s₁ -> g a = 1)
    (h : forall a in s₁, a in s₂ -> f a = g a) :
    ∏ a in s₁, f a = ∏ a in s₂, g a := by
  classical
  conv_lhs => rw [← sdiff_union_inter s₁ s₂, prod_union_eq_right (by simp_all)]
  conv_rhs => rw [← sdiff_union_inter s₂ s₁, prod_union_eq_right (by simp_all), inter_comm]
  exact prod_congr rfl (by simpa)

@[to_additive]
/--
theorem `prod_eq_mul_of_mem` / 定理 `prod_eq_mul_of_mem`

English:
theorem prod_eq_mul_of_mem
  statement: {s : Finset ι} {f : ι -> M} (a b : ι) (ha : a in s) (hb : b in s)
  proof: by
  have := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' subseteq s := by grind
  have hf : forall c in s, c ∉ s' -> f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]

中文:
定理 prod_eq_mul_of_mem
  结论: {s : Finset ι} {f : ι -> M} (a b : ι) (ha : a in s) (hb : b in s)
  证明: by
  have := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' subseteq s := by grind
  have hf : forall c in s, c ∉ s' -> f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.prod_pair, Finset.prod_subset, prod_pair, prod_subset, subseteq
-/
theorem prod_eq_mul_of_mem {s : Finset ι} {f : ι -> M} (a b : ι) (ha : a in s) (hb : b in s)
    (hn : a != b) (h₀ : forall c in s, c != a ∧ c != b -> f c = 1) : ∏ x in s, f x = f a * f b := by
  have := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' subseteq s := by grind
  have hf : forall c in s, c ∉ s' -> f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
/--
theorem `prod_eq_mul` / 定理 `prod_eq_mul`

English:
theorem prod_eq_mul
  statement: {s : Finset ι} {f : ι -> M} (a b : ι) (hn : a != b)
  proof: by
  have := Classical.decEq ι; by_cases h₁ : a in s <;> by_cases h₂ : b in s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single

中文:
定理 prod_eq_mul
  结论: {s : Finset ι} {f : ι -> M} (a b : ι) (hn : a != b)
  证明: by
  have := Classical.decEq ι; by_cases h₁ : a in s <;> by_cases h₂ : b in s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single

Depends on / 依赖: Classical, Classical.decEq, _root_, _root_.trans, mul_one, ne_of_mem_of_not_mem, one_mul, prod_congr, prod_eq_mul_of_mem, prod_eq_single_of_mem
-/
theorem prod_eq_mul {s : Finset ι} {f : ι -> M} (a b : ι) (hn : a != b)
    (h₀ : forall c in s, c != a ∧ c != b -> f c = 1) (ha : a ∉ s -> f a = 1) (hb : b ∉ s -> f b = 1) :
    ∏ x in s, f x = f a * f b := by
  have := Classical.decEq ι; by_cases h₁ : a in s <;> by_cases h₂ : b in s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      _root_.trans
        (prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one

/-- A product over `s.subtype p` equals one over `{x ∈ s | p x}`. -/
@[to_additive (attr := simp)
/-- A sum over `s.subtype p` equals one over `{x ∈ s | p x}`. -/]
/--
theorem `prod_subtype_eq_prod_filter` / 定理 `prod_subtype_eq_prod_filter`

English:
theorem prod_subtype_eq_prod_filter
  given: (f : ι -> M) {p : ι -> Prop} [DecidablePred p]
  proof: by
  have := prod_map (s.subtype p) (Function.Embedding.subtype _) f
  simp_all

中文:
定理 prod_subtype_eq_prod_filter
  条件: (f : ι -> M) {p : ι -> 命题} [DecidablePred p]
  证明: by
  have := prod_map (s.subtype p) (Function.Embedding.subtype _) f
  simp_all

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, prod_map, s.subtype, subtype
-/
theorem prod_subtype_eq_prod_filter (f : ι -> M) {p : ι -> Prop} [DecidablePred p] :
    ∏ x in s.subtype p, f x = ∏ x in s with p x, f x := by
  have := prod_map (s.subtype p) (Function.Embedding.subtype _) f
  simp_all

/-- If all elements of a `Finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive /-- If all elements of a `Finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`. -/]
/--
theorem `prod_subtype_of_mem` / 定理 `prod_subtype_of_mem`

English:
theorem prod_subtype_of_mem
  given: (f : ι -> M) {p : ι -> Prop} [DecidablePred p] (h : forall x in s, p x)
  proof: by
  rw [prod_subtype_eq_prod_filter]; rw [filter_true_of_mem]
  simpa using h

中文:
定理 prod_subtype_of_mem
  条件: (f : ι -> M) {p : ι -> 命题} [DecidablePred p] (h : 对任意 x in s, p x)
  证明: by
  rw [prod_subtype_eq_prod_filter]; rw [filter_true_of_mem]
  simpa using h

Depends on / 依赖: filter_true_of_mem, prod_subtype_eq_prod_filter
-/
theorem prod_subtype_of_mem (f : ι -> M) {p : ι -> Prop} [DecidablePred p] (h : forall x in s, p x) :
    ∏ x in s.subtype p, f x = ∏ x in s, f x := by
  rw [prod_subtype_eq_prod_filter]; rw [filter_true_of_mem]
  simpa using h

/-- A product of a function over a `Finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `Finset`. -/
@[to_additive /-- A sum of a function over a `Finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `Finset`. -/]
/--
theorem `prod_subtype_map_embedding` / 定理 `prod_subtype_map_embedding`

English:
theorem prod_subtype_map_embedding
  statement: {p : ι -> Prop} {s : Finset { x // p x }} {f : { x // p x } -> M}
  proof: by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

中文:
定理 prod_subtype_map_embedding
  结论: {p : ι -> 命题} {s : Finset { x // p x }} {f : { x // p x } -> M}
  证明: by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_map, prod_congr, prod_map
-/
theorem prod_subtype_map_embedding {p : ι -> Prop} {s : Finset { x // p x }} {f : { x // p x } -> M}
    {g : ι -> M} (h : forall x : { x // p x }, x in s -> g x = f x) :
    (∏ x in s.map (Function.Embedding.subtype _), g x) = ∏ x in s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
/--
theorem `prod_coe_sort` / 定理 `prod_coe_sort`

English:
theorem prod_coe_sort
  statement: ∏ i : s, f i = ∏ i in s, f i
  proof: prod_attach _ _

@[to_additive]

中文:
定理 prod_coe_sort
  结论: ∏ i : s, f i = ∏ i in s, f i
  证明: prod_attach _ _

@[to_additive]

Depends on / 依赖: prod_attach
-/
theorem prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i := prod_attach _ _

@[to_additive]
/--
theorem `prod_finset_coe` / 定理 `prod_finset_coe`

English:
theorem prod_finset_coe
  given: (f : ι -> M) (s : Finset ι)
  statement: (∏ i : (s : Set ι), f i) = ∏ i in s, f i
  proof: prod_coe_sort s f

中文:
定理 prod_finset_coe
  条件: (f : ι -> M) (s : Finset ι)
  结论: (∏ i : (s : Set ι), f i) = ∏ i in s, f i
  证明: prod_coe_sort s f

Depends on / 依赖: prod_coe_sort
-/
theorem prod_finset_coe (f : ι -> M) (s : Finset ι) : (∏ i : (s : Set ι), f i) = ∏ i in s, f i :=
  prod_coe_sort s f

variable {f s}

@[to_additive]
/--
theorem `prod_subtype` / 定理 `prod_subtype`

English:
theorem prod_subtype
  statement: {p : ι -> Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : forall x, x in s ↔ p x)
  proof: by
  obtain rfl : p = (· in s) := by simp [h]
  rw [← prod_coe_sort]
  congr!

@[to_additive]

中文:
定理 prod_subtype
  结论: {p : ι -> 命题} {F : Fintype (Subtype p)} (s : Finset ι) (h : 对任意 x, x in s ↔ p x)
  证明: by
  obtain rfl : p = (· in s) := by simp [h]
  rw [← prod_coe_sort]
  congr!

@[to_additive]

Depends on / 依赖: prod_coe_sort
-/
theorem prod_subtype {p : ι -> Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : forall x, x in s ↔ p x)
    (f : ι -> M) : ∏ a in s, f a = ∏ a : Subtype p, f a := by
  obtain rfl : p = (· in s) := by simp [h]
  rw [← prod_coe_sort]
  congr!

@[to_additive]
/--
theorem `prod_set_coe` / 定理 `prod_set_coe`

English:
theorem prod_set_coe
  given: (s : Set ι) [Fintype s]
  statement: (∏ i : s, f i) = ∏ i in s.toFinset, f i
  proof: (Finset.prod_subtype s.toFinset (fun _ => Set.mem_toFinset) f).symm

中文:
定理 prod_set_coe
  条件: (s : Set ι) [Fintype s]
  结论: (∏ i : s, f i) = ∏ i in s.toFinset, f i
  证明: (Finset.prod_subtype s.toFinset (fun _ => Set.mem_toFinset) f).symm

Depends on / 依赖: Finset, Finset.prod_subtype, Set.mem_toFinset, mem_toFinset, prod_subtype, s.toFinset, toFinset
-/
theorem prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i in s.toFinset, f i :=
  (Finset.prod_subtype s.toFinset (fun _ => Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive /-- The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`. -/]
/--
theorem `prod_congr_set` / 定理 `prod_congr_set`

English:
theorem prod_congr_set
  statement: [Fintype ι] (s : Set ι) [DecidablePred (· in s)] (f : ι -> M) (g : s -> M)
  proof: by
  rw [← prod_subset s.toFinset.subset_univ (by simpa)]; rw [prod_subtype (p := (· in s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

@[to_additive]

中文:
定理 prod_congr_set
  结论: [Fintype ι] (s : Set ι) [DecidablePred (· in s)] (f : ι -> M) (g : s -> M)
  证明: by
  rw [← prod_subset s.toFinset.subset_univ (by simpa)]; rw [prod_subtype (p := (· in s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

@[to_additive]

Depends on / 依赖: prod_subset, prod_subtype, s.toFinset.subset_univ, subset_univ, toFinset
-/
theorem prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· in s)] (f : ι -> M) (g : s -> M)
    (w : forall x (hx : x in s), f x = g ⟨x, hx⟩) (w' : forall x ∉ s, f x = 1) : ∏ i, f i = ∏ i, g i := by
  rw [← prod_subset s.toFinset.subset_univ (by simpa)]; rw [prod_subtype (p := (· in s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

@[to_additive]
/--
theorem `prod_extend_by_one` / 定理 `prod_extend_by_one`

English:
theorem prod_extend_by_one
  given: [DecidableEq ι] (s : Finset ι) (f : ι -> M)
  proof: (prod_congr rfl) fun _i hi => if_pos hi

中文:
定理 prod_extend_by_one
  条件: [DecidableEq ι] (s : Finset ι) (f : ι -> M)
  证明: (prod_congr rfl) fun _i hi => if_pos hi

Depends on / 依赖: if_pos, prod_congr
-/
theorem prod_extend_by_one [DecidableEq ι] (s : Finset ι) (f : ι -> M) :
    ∏ i in s, (if i in s then f i else 1) = ∏ i in s, f i :=
  (prod_congr rfl) fun _i hi => if_pos hi

/-- Also see `Finset.prod_ite_mem_eq` -/
@[to_additive /-- Also see `Finset.sum_ite_mem_eq` -/]
/--
theorem `prod_eq_prod_extend` / 定理 `prod_eq_prod_extend`

English:
theorem prod_eq_prod_extend
  given: (f : s -> M)
  statement: ∏ x, f x = ∏ x in s, Subtype.val.extend f 1 x
  proof: by
  rw [univ_eq_attach]; rw [← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

@[to_additive]

中文:
定理 prod_eq_prod_extend
  条件: (f : s -> M)
  结论: ∏ x, f x = ∏ x in s, Subtype.val.extend f 1 x
  证明: by
  rw [univ_eq_attach]; rw [← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_attach, Subtype, Subtype.val_injective.extend_apply, extend_apply, prod_attach, univ_eq_attach, val_injective
-/
theorem prod_eq_prod_extend (f : s -> M) : ∏ x, f x = ∏ x in s, Subtype.val.extend f 1 x := by
  rw [univ_eq_attach]; rw [← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

@[to_additive]
/--
theorem `prod_bij_ne_one` / 定理 `prod_bij_ne_one`

English:
theorem prod_bij_ne_one
  statement: {s : Finset ι} {t : Finset κ} {f : ι -> M} {g : κ -> M}
  proof: by
  classical
  calc
    ∏ x in s, f x = ∏ x in s with f x != 1, f x := by rw [prod_filter_ne_one]
    _ = ∏ x in t with g x != 1, g x :=
      prod_bij (fun a ha => i a (mem_filter.mp ha).1 <| by simpa using (mem_filter.mp ha).2)
        ?_ ?_ ?_ ?_
    _ = ∏ x in t, g x := prod_filter_ne_one _
  

中文:
定理 prod_bij_ne_one
  结论: {s : Finset ι} {t : Finset κ} {f : ι -> M} {g : κ -> M}
  证明: by
  classical
  calc
    ∏ x in s, f x = ∏ x in s with f x != 1, f x := by rw [prod_filter_ne_one]
    _ = ∏ x in t with g x != 1, g x :=
      prod_bij (fun a ha => i a (mem_filter.mp ha).1 <| by simpa using (mem_filter.mp ha).2)
        ?_ ?_ ?_ ?_
    _ = ∏ x in t, g x := prod_filter_ne_one _
  

Depends on / 依赖: classical, i_surj, mem_filter, mem_filter.mp, mem_filter.mpr, prod_bij, prod_filter_ne_one, solve_by_elim
-/
theorem prod_bij_ne_one {s : Finset ι} {t : Finset κ} {f : ι -> M} {g : κ -> M}
    (i : forall a in s, f a != 1 -> κ) (hi : forall a h₁ h₂, i a h₁ h₂ in t)
    (i_inj : forall a₁ h₁₁ h₁₂ a₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ -> a₁ = a₂)
    (i_surj : forall b in t, g b != 1 -> exists a h₁ h₂, i a h₁ h₂ = b) (h : forall a h₁ h₂, f a = g (i a h₁ h₂)) :
    ∏ x in s, f x = ∏ x in t, g x := by
  classical
  calc
    ∏ x in s, f x = ∏ x in s with f x != 1, f x := by rw [prod_filter_ne_one]
    _ = ∏ x in t with g x != 1, g x :=
      prod_bij (fun a ha => i a (mem_filter.mp ha).1 <| by simpa using (mem_filter.mp ha).2)
        ?_ ?_ ?_ ?_
    _ = ∏ x in t, g x := prod_filter_ne_one _
  · grind
  · solve_by_elim
  · intro b hb
    refine (mem_filter.mp hb).elim fun h₁ h₂ => ?_
    obtain ⟨a, ha₁, ha₂, eq⟩ := i_surj b h₁ fun H => by rw [H] at h₂; simp at h₂
    exact ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩
  · solve_by_elim

@[to_additive]
/--
theorem `exists_ne_one_of_prod_ne_one` / 定理 `exists_ne_one_of_prod_ne_one`

English:
theorem exists_ne_one_of_prod_ne_one
  given: (h : ∏ x in s, f x != 1)
  statement: exists a in s, f a != 1
  proof: by
  contrapose! h
  exact prod_eq_one h

@[to_additive]

中文:
定理 exists_ne_one_of_prod_ne_one
  条件: (h : ∏ x in s, f x != 1)
  结论: 存在 a in s, f a != 1
  证明: by
  contrapose! h
  exact prod_eq_one h

@[to_additive]

Depends on / 依赖: contrapose, prod_eq_one
-/
theorem exists_ne_one_of_prod_ne_one (h : ∏ x in s, f x != 1) : exists a in s, f a != 1 := by
  contrapose! h
  exact prod_eq_one h

@[to_additive]
/--
theorem `prod_range_succ_comm` / 定理 `prod_range_succ_comm`

English:
theorem prod_range_succ_comm
  given: (f : Nat -> M) (n : Nat)
  proof: by
  rw [range_add_one]; rw [prod_insert notMem_range_self]

@[to_additive]

中文:
定理 prod_range_succ_comm
  条件: (f : 自然数 -> M) (n : 自然数)
  证明: by
  rw [range_add_one]; rw [prod_insert notMem_range_self]

@[to_additive]

Depends on / 依赖: notMem_range_self, prod_insert, range_add_one
-/
theorem prod_range_succ_comm (f : Nat -> M) (n : Nat) :
    (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x := by
  rw [range_add_one]; rw [prod_insert notMem_range_self]

@[to_additive]
/--
theorem `prod_range_succ` / 定理 `prod_range_succ`

English:
theorem prod_range_succ
  given: (f : Nat -> M) (n : Nat)
  proof: by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]

中文:
定理 prod_range_succ
  条件: (f : 自然数 -> M) (n : 自然数)
  证明: by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]

Depends on / 依赖: mul_comm, prod_range_succ_comm
-/
theorem prod_range_succ (f : Nat -> M) (n : Nat) :
    (∏ x in range (n + 1), f x) = (∏ x in range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
/--
theorem `prod_range_succ'` / 定理 `prod_range_succ'`

English:
theorem prod_range_succ'
  given: (f : Nat -> M)

中文:
定理 prod_range_succ'
  条件: (f : 自然数 -> M)
-/
theorem prod_range_succ' (f : Nat -> M) :
    forall n : Nat, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]

@[to_additive]
/--
theorem `eventually_constant_prod` / 定理 `eventually_constant_prod`

English:
theorem eventually_constant_prod
  given: {u : Nat -> M} {N : Nat} (hu : forall n >= N, u n = 1) {n : Nat} (hn : N <= n)
  proof: by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, prod_range_succ, hm, hu]

@[to_additive]

中文:
定理 eventually_constant_prod
  条件: {u : 自然数 -> M} {N : 自然数} (hu : 对任意 n >= N, u n = 1) {n : 自然数} (hn : N <= n)
  证明: by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, prod_range_succ, hm, hu]

@[to_additive]

Depends on / 依赖: Nat.exists_eq_add_of_le, add_assoc, exists_eq_add_of_le, prod_range_succ
-/
theorem eventually_constant_prod {u : Nat -> M} {N : Nat} (hu : forall n >= N, u n = 1) {n : Nat} (hn : N <= n) :
    (∏ k in range n, u k) = ∏ k in range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, prod_range_succ, hm, hu]

@[to_additive]
/--
theorem `prod_range_add` / 定理 `prod_range_add`

English:
theorem prod_range_add
  given: (f : Nat -> M) (n m : Nat)
  proof: by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive sum_range_one]

中文:
定理 prod_range_add
  条件: (f : 自然数 -> M) (n m : 自然数)
  证明: by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive sum_range_one]

Depends on / 依赖: Nat.add_succ, add_succ, mul_assoc, prod_range_succ
-/
theorem prod_range_add (f : Nat -> M) (n m : Nat) :
    (∏ x in range (n + m), f x) = (∏ x in range n, f x) * ∏ x in range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive sum_range_one]
/--
theorem `prod_range_one` / 定理 `prod_range_one`

English:
theorem prod_range_one
  given: (f : Nat -> M)
  statement: ∏ k in range 1, f k = f 0
  proof: by
  rw [range_one]; rw [prod_singleton]

中文:
定理 prod_range_one
  条件: (f : 自然数 -> M)
  结论: ∏ k in range 1, f k = f 0
  证明: by
  rw [range_one]; rw [prod_singleton]

Depends on / 依赖: prod_singleton, range_one
-/
theorem prod_range_one (f : Nat -> M) : ∏ k in range 1, f k = f 0 := by
  rw [range_one]; rw [prod_singleton]

open List

@[to_additive]
/--
theorem `prod_list_map_count` / 定理 `prod_list_map_count`

English:
theorem prod_list_map_count
  given: [DecidableEq ι] (l : List ι) (f : ι -> M)
  proof: by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a in s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (notMem_erase _ _),
      pr

中文:
定理 prod_list_map_count
  条件: [DecidableEq ι] (l : List ι) (f : ι -> M)
  证明: by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a in s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (notMem_erase _ _),
      pr

Depends on / 依赖: List.map, List.prod_cons, count_, count_cons_of_ne, count_cons_self, count_nil, insert_eq_of_mem, insert_erase, map_nil, mul_assoc, ne_of_mem_erase, notMem_erase, pow_succ, pow_zero, prod_congr, prod_cons, prod_const_one, prod_insert, prod_nil, s.toFinset
-/
theorem prod_list_map_count [DecidableEq ι] (l : List ι) (f : ι -> M) :
    (l.map f).prod = ∏ m in l.toFinset, f m ^ l.count m := by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a in s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (notMem_erase _ _),
      prod_insert (notMem_erase _ _), ← mul_assoc, count_cons_self, pow_succ']
    congr 1
    refine prod_congr rfl fun x hx => ?_
    rw [count_cons_of_ne (ne_of_mem_erase hx).symm]
  rw [prod_insert has]; rw [count_cons_self]; rw [count_eq_zero_of_not_mem (mt mem_toFinset.2 has)]; rw [pow_one]
  grind [Finset.prod_congr]

@[to_additive]
/--
theorem `prod_list_count` / 定理 `prod_list_count`

English:
theorem prod_list_count
  given: [DecidableEq M] (s : List M)
  proof: by simpa using prod_list_map_count s id

@[to_additive]

中文:
定理 prod_list_count
  条件: [DecidableEq M] (s : List M)
  证明: by simpa using prod_list_map_count s id

@[to_additive]

Depends on / 依赖: prod_list_map_count
-/
theorem prod_list_count [DecidableEq M] (s : List M) :
    s.prod = ∏ m in s.toFinset, m ^ s.count m := by simpa using prod_list_map_count s id

@[to_additive]
/--
theorem `prod_list_count_of_subset` / 定理 `prod_list_count_of_subset`

English:
theorem prod_list_count_of_subset
  statement: [DecidableEq M] (m : List M) (s : Finset M)
  proof: by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx]; rw [pow_zero]

中文:
定理 prod_list_count_of_subset
  结论: [DecidableEq M] (m : List M) (s : Finset M)
  证明: by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx]; rw [pow_zero]

Depends on / 依赖: count_eq_zero_of_not_mem, mem_toFinset, pow_zero, prod_list_count, prod_subset
-/
theorem prod_list_count_of_subset [DecidableEq M] (m : List M) (s : Finset M)
    (hs : m.toFinset subseteq s) : m.prod = ∏ i in s, i ^ m.count i := by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx]; rw [pow_zero]

open Multiset

@[to_additive]
/--
theorem `prod_multiset_map_count` / 定理 `prod_multiset_map_count`

English:
theorem prod_multiset_map_count
  statement: [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
  proof: by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]

中文:
定理 prod_multiset_map_count
  结论: [DecidableEq ι] (s : Multiset ι) {M : 类型} [CommMonoid M]
  证明: by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]

Depends on / 依赖: Quot.induction_on, induction_on, prod_list_map_count
-/
theorem prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
    (f : ι -> M) : (s.map f).prod = ∏ m in s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]
/--
theorem `prod_multiset_count` / 定理 `prod_multiset_count`

English:
theorem prod_multiset_count
  given: [DecidableEq M] (s : Multiset M)
  proof: by
  convert! prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]

中文:
定理 prod_multiset_count
  条件: [DecidableEq M] (s : Multiset M)
  证明: by
  convert! prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]

Depends on / 依赖: Multiset, Multiset.map_id, convert, map_id, prod_multiset_map_count
-/
theorem prod_multiset_count [DecidableEq M] (s : Multiset M) :
    s.prod = ∏ m in s.toFinset, m ^ s.count m := by
  convert! prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
/--
theorem `prod_multiset_count_of_subset` / 定理 `prod_multiset_count_of_subset`

English:
theorem prod_multiset_count_of_subset
  statement: [DecidableEq M] (m : Multiset M) (s : Finset M)
  proof: by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

中文:
定理 prod_multiset_count_of_subset
  结论: [DecidableEq M] (m : Multiset M) (s : Finset M)
  证明: by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

Depends on / 依赖: Quot.induction_on, coe_count, induction_on, prod_coe, prod_list_count_of_subset, quot_mk_to_coe, revert
-/
theorem prod_multiset_count_of_subset [DecidableEq M] (m : Multiset M) (s : Finset M)
    (hs : m.toFinset subseteq s) : m.prod = ∏ i in s, i ^ m.count i := by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms up to `n`.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive /-- For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we
can verify that it's equal to a different function just by checking differences of adjacent terms
up to `n`.

This is a discrete analogue of the fundamental theorem of calculus. -/]
/--
theorem `prod_range_induction` / 定理 `prod_range_induction`

English:
theorem prod_range_induction
  statement: (f s : Nat -> M) (base : s 0 = 1)
  proof: by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ]; rw [step _ (Nat.lt_succ_self _)]; rw [hk]
    exact fun _ hl => step _ (Nat.lt_succ_of_lt hl)

@[to_additive (attr := simp)]

中文:
定理 prod_range_induction
  结论: (f s : 自然数 -> M) (base : s 0 = 1)
  证明: by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ]; rw [step _ (Nat.lt_succ_self _)]; rw [hk]
    exact fun _ hl => step _ (Nat.lt_succ_of_lt hl)

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_range_succ, Finset.prod_range_zero, Nat.lt_succ_of_lt, Nat.lt_succ_self, lt_succ_of_lt, lt_succ_self, prod_range_succ, prod_range_zero
-/
theorem prod_range_induction (f s : Nat -> M) (base : s 0 = 1)
    (n : Nat) (step : forall k < n, s (k + 1) = s k * f k) :
    ∏ k in Finset.range n, f k = s n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ]; rw [step _ (Nat.lt_succ_self _)]; rw [hk]
    exact fun _ hl => step _ (Nat.lt_succ_of_lt hl)

@[to_additive (attr := simp)]
/--
theorem `prod_const` / 定理 `prod_const`

English:
theorem prod_const
  given: (b : M)
  statement: ∏ _x in s, b = b ^ #s
  proof: (congr_arg _ <| s.val.map_const b).trans Multiset.prod_replicate #s b

@[to_additive sum_eq_card_nsmul]

中文:
定理 prod_const
  条件: (b : M)
  结论: ∏ _x in s, b = b ^ #s
  证明: (congr_arg _ <| s.val.map_const b).trans Multiset.prod_replicate #s b

@[to_additive sum_eq_card_nsmul]

Depends on / 依赖: Multiset, Multiset.prod_replicate, congr_arg, map_const, prod_replicate, s.val.map_const
-/
theorem prod_const (b : M) : ∏ _x in s, b = b ^ #s :=
(congr_arg _ <| s.val.map_const b).trans Multiset.prod_replicate #s b

@[to_additive sum_eq_card_nsmul]
/--
theorem `prod_eq_pow_card` / 定理 `prod_eq_pow_card`

English:
theorem prod_eq_pow_card
  given: {b : M} (hf : forall a in s, f a = b)
  statement: ∏ a in s, f a = b ^ #s
  proof: (prod_congr rfl hf).trans prod_const _

@[to_additive card_nsmul_add_sum]

中文:
定理 prod_eq_pow_card
  条件: {b : M} (hf : 对任意 a in s, f a = b)
  结论: ∏ a in s, f a = b ^ #s
  证明: (prod_congr rfl hf).trans prod_const _

@[to_additive card_nsmul_add_sum]

Depends on / 依赖: prod_congr, prod_const
-/
theorem prod_eq_pow_card {b : M} (hf : forall a in s, f a = b) : ∏ a in s, f a = b ^ #s :=
(prod_congr rfl hf).trans prod_const _

@[to_additive card_nsmul_add_sum]
/--
theorem `pow_card_mul_prod` / 定理 `pow_card_mul_prod`

English:
theorem pow_card_mul_prod
  given: {b : M}
  statement: b ^ #s * ∏ a in s, f a = ∏ a in s, b * f a
  proof: (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive sum_add_card_nsmul]

中文:
定理 pow_card_mul_prod
  条件: {b : M}
  结论: b ^ #s * ∏ a in s, f a = ∏ a in s, b * f a
  证明: (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive sum_add_card_nsmul]

Depends on / 依赖: Finset, Finset.prod_const, prod_const, prod_mul_distrib, prod_mul_distrib.symm
-/
theorem pow_card_mul_prod {b : M} : b ^ #s * ∏ a in s, f a = ∏ a in s, b * f a :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive sum_add_card_nsmul]
/--
theorem `prod_mul_pow_card` / 定理 `prod_mul_pow_card`

English:
theorem prod_mul_pow_card
  given: {b : M}
  statement: (∏ a in s, f a) * b ^ #s = ∏ a in s, f a * b
  proof: (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive]

中文:
定理 prod_mul_pow_card
  条件: {b : M}
  结论: (∏ a in s, f a) * b ^ #s = ∏ a in s, f a * b
  证明: (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_const, prod_const, prod_mul_distrib, prod_mul_distrib.symm
-/
theorem prod_mul_pow_card {b : M} : (∏ a in s, f a) * b ^ #s = ∏ a in s, f a * b :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive]
/--
theorem `pow_eq_prod_const` / 定理 `pow_eq_prod_const`

English:
theorem pow_eq_prod_const
  given: (b : M)
  statement: forall n, b ^ n = ∏ _k in range n, b
  proof: by simp

@[to_additive sum_nsmul_assoc]

中文:
定理 pow_eq_prod_const
  条件: (b : M)
  结论: 对任意 n, b ^ n = ∏ _k in range n, b
  证明: by simp

@[to_additive sum_nsmul_assoc]
-/
theorem pow_eq_prod_const (b : M) : forall n, b ^ n = ∏ _k in range n, b := by simp

@[to_additive sum_nsmul_assoc]
/--
lemma `prod_pow_eq_pow_sum` / 引理 `prod_pow_eq_pow_sum`

English:
lemma prod_pow_eq_pow_sum
  given: (s : Finset ι) (f : ι -> Nat) (a : M)
  proof: cons_induction (by simp) (fun _ _ _ _ => by simp [prod_cons, sum_cons, pow_add, *]) s

@[to_additive]

中文:
引理 prod_pow_eq_pow_sum
  条件: (s : Finset ι) (f : ι -> 自然数) (a : M)
  证明: cons_induction (by simp) (fun _ _ _ _ => by simp [prod_cons, sum_cons, pow_add, *]) s

@[to_additive]

Depends on / 依赖: cons_induction, pow_add, prod_cons, sum_cons
-/
lemma prod_pow_eq_pow_sum (s : Finset ι) (f : ι -> Nat) (a : M) :
    ∏ i in s, a ^ f i = a ^ ∑ i in s, f i :=
  cons_induction (by simp) (fun _ _ _ _ => by simp [prod_cons, sum_cons, pow_add, *]) s

@[to_additive]
/--
theorem `prod_flip` / 定理 `prod_flip`

English:
theorem prod_flip
  given: {n : Nat} (f : Nat -> M)
  proof: by
  induction n with
  | zero => rw [prod_range_one, prod_range_one]
  | succ n ih =>
    rw [prod_range_succ']; rw [prod_range_succ _ (Nat.succ n)]
    simp [← ih]

中文:
定理 prod_flip
  条件: {n : 自然数} (f : 自然数 -> M)
  证明: by
  induction n with
  | zero => rw [prod_range_one, prod_range_one]
  | succ n ih =>
    rw [prod_range_succ']; rw [prod_range_succ _ (Nat.succ n)]
    simp [← ih]

Depends on / 依赖: Nat.succ, prod_range_one, prod_range_succ
-/
theorem prod_flip {n : Nat} (f : Nat -> M) :
    (∏ r in range (n + 1), f (n - r)) = ∏ k in range (n + 1), f k := by
  induction n with
  | zero => rw [prod_range_one, prod_range_one]
  | succ n ih =>
    rw [prod_range_succ']; rw [prod_range_succ _ (Nat.succ n)]
    simp [← ih]

/-- The difference with `Finset.prod_ninvolution` is that the involution is allowed to use
membership of the domain of the product, rather than being a non-dependent function. -/
@[to_additive /-- The difference with `Finset.sum_ninvolution` is that the involution is allowed to
use membership of the domain of the sum, rather than being a non-dependent function. -/]
/--
lemma `prod_involution` / 引理 `prod_involution`

English:
lemma prod_involution
  statement: (g : forall a in s, ι) (hg₁ : forall a ha, f a * f (g a ha) = 1)
  proof: by
  classical
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have : {x, g x hx} subseteq s := by simp [insert_subset_iff, hx, g_mem]
  suffices h : ∏ x in s \ {x, g x hx}, f x = 1 by
    rw [← prod_sdiff this]; rw [h]; rw [

中文:
引理 prod_involution
  结论: (g : 对任意 a in s, ι) (hg₁ : 对任意 a ha, f a * f (g a ha) = 1)
  证明: by
  classical
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have : {x, g x hx} subseteq s := by simp [insert_subset_iff, hx, g_mem]
  suffices h : ∏ x in s \ {x, g x hx}, f x = 1 by
    rw [← prod_sdiff this]; rw [h]; rw [

Depends on / 依赖: Finset, Finset.strongInduction, classical, eq_empty_or_nonempty, eq_or_ne, g_mem, insert_subset_iff, one_mul, prod_sdiff, s.eq_empty_or_nonempty, sdiff_subset, strongInduction, subseteq
-/
lemma prod_involution (g : forall a in s, ι) (hg₁ : forall a ha, f a * f (g a ha) = 1)
    (hg₃ : forall a ha, f a != 1 -> g a ha != a)
    (g_mem : forall a ha, g a ha in s) (hg₄ : forall a ha, g (g a ha) (g_mem a ha) = a) :
    ∏ x in s, f x = 1 := by
  classical
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have : {x, g x hx} subseteq s := by simp [insert_subset_iff, hx, g_mem]
  suffices h : ∏ x in s \ {x, g x hx}, f x = 1 by
    rw [← prod_sdiff this]; rw [h]; rw [one_mul]
    cases eq_or_ne (g x hx) x with
    | inl hx' => simpa [hx'] using hg₃ x hx
    | inr hx' => grind
  suffices h₃ : forall a (ha : a in s \ {x, g x hx}), g a (sdiff_subset ha) in s \ {x, g x hx} from
    ih (s \ {x, g x hx}) (ssubset_iff.2 ⟨x, by simp [insert_subset_iff, hx]⟩) _
      (by simp [hg₁]) (fun _ _ => hg₃ _ _) h₃ (fun _ _ => hg₄ _ _)
  grind

/-- The difference with `Finset.prod_involution` is that the involution is a non-dependent function,
rather than being allowed to use membership of the domain of the product. -/
@[to_additive /-- The difference with `Finset.sum_involution` is that the involution is a
non-dependent function, rather than being allowed to use membership of the domain of the sum. -/]
/--
lemma `prod_ninvolution` / 引理 `prod_ninvolution`

English:
lemma prod_ninvolution
  statement: (g : ι -> ι) (hg₁ : forall a, f a * f (g a) = 1) (hg₂ : forall a, f a != 1 -> g a != a)
  proof: prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

中文:
引理 prod_ninvolution
  结论: (g : ι -> ι) (hg₁ : 对任意 a, f a * f (g a) = 1) (hg₂ : 对任意 a, f a != 1 -> g a != a)
  证明: prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

Depends on / 依赖: g_mem, prod_involution
-/
lemma prod_ninvolution (g : ι -> ι) (hg₁ : forall a, f a * f (g a) = 1) (hg₂ : forall a, f a != 1 -> g a != a)
    (g_mem : forall a, g a in s) (hg₃ : forall a, g (g a) = a) : ∏ x in s, f x = 1 :=
  prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `Finset.prod_image`. -/
@[to_additive /-- The sum of the composition of functions `f` and `g`, is the sum over
`b ∈ s.image g` of `f b` times of the cardinality of the fibre of `b`. See also
`Finset.sum_image`. -/]
/--
theorem `prod_comp` / 定理 `prod_comp`

English:
theorem prod_comp
  given: [DecidableEq κ] (f : κ -> M) (g : ι -> κ)
  proof: by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ => mem_image_of_mem _]

中文:
定理 prod_comp
  条件: [DecidableEq κ] (f : κ -> M) (g : ι -> κ)
  证明: by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ => mem_image_of_mem _]

Depends on / 依赖: mem_image_of_mem, prod_const, prod_fiberwise_of_maps_to, simp_rw
-/
theorem prod_comp [DecidableEq κ] (f : κ -> M) (g : ι -> κ) :
    ∏ a in s, f (g a) = ∏ b in s.image g, f b ^ #{a in s | g a = b} := by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ => mem_image_of_mem _]

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive /-- A sum can be partitioned into a sum of sums, each equivalent under a setoid. -/]
/--
theorem `prod_partition` / 定理 `prod_partition`

English:
theorem prod_partition
  given: (R : Setoid ι) [DecidableRel R.r]
  proof: by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

中文:
定理 prod_partition
  条件: (R : Setoid ι) [DecidableRel R.r]
  证明: by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

Depends on / 依赖: Finset, Finset.prod_image, prod_image
-/
theorem prod_partition (R : Setoid ι) [DecidableRel R.r] :
    ∏ x in s, f x = ∏ xbar in s.image (Quotient.mk _), ∏ y in s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive /-- If we can partition a sum into subsets that cancel out, then the whole sum
cancels. -/]
/--
theorem `prod_cancels_of_partition_cancels` / 定理 `prod_cancels_of_partition_cancels`

English:
theorem prod_cancels_of_partition_cancels
  statement: (R : Setoid ι) [DecidableRel R]
  proof: by
  rw [prod_partition R]; rw [← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

中文:
定理 prod_cancels_of_partition_cancels
  结论: (R : Setoid ι) [DecidableRel R]
  证明: by
  rw [prod_partition R]; rw [← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

Depends on / 依赖: Finset, Finset.prod_eq_one, Quotient, Quotient.eq, mem_image, mem_image.mp, prod_eq_one, prod_partition, x_in_s, xbar_in_s
-/
theorem prod_cancels_of_partition_cancels (R : Setoid ι) [DecidableRel R]
    (h : forall x in s, ∏ a in s with R a x, f a = 1) : ∏ x in s, f x = 1 := by
  rw [prod_partition R]; rw [← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

/-- If a product of a `Finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq /-- If a sum of a `Finset` of size at most 1 has a given
value, so do the terms in that sum. -/]
/--
theorem `eq_of_card_le_one_of_prod_eq` / 定理 `eq_of_card_le_one_of_prod_eq`

English:
theorem eq_of_card_le_one_of_prod_eq
  statement: {s : Finset ι} (hc : #s <= 1) {f : ι -> M} {b : M}
  proof: by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    grind

中文:
定理 eq_of_card_le_one_of_prod_eq
  结论: {s : Finset ι} (hc : #s <= 1) {f : ι -> M} {b : M}
  证明: by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    grind

Depends on / 依赖: False.elim, Nat.one_le_of_lt, Nat.pos_of_ne_zero, card_eq_one, card_ne_zero_of_mem, le_antisymm, one_le_of_lt, pos_of_ne_zero
-/
theorem eq_of_card_le_one_of_prod_eq {s : Finset ι} (hc : #s <= 1) {f : ι -> M} {b : M}
    (h : ∏ x in s, f x = b) : forall x in s, f x = b := by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    grind

/-- Taking a product over `s : Finset ι` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `Multiset.prod_map_erase` for the `Multiset` version. -/
@[to_additive /-- Taking a sum over `s : Finset ι` is the same as adding the value on a single
element `f a` to the sum over `s.erase a`.

See `Multiset.sum_map_erase` for the `Multiset` version. -/]
/--
theorem `mul_prod_erase` / 定理 `mul_prod_erase`

English:
theorem mul_prod_erase
  given: [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a in s)
  proof: by
  rw [← prod_insert (notMem_erase a s)]; rw [insert_erase h]

中文:
定理 mul_prod_erase
  条件: [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a in s)
  证明: by
  rw [← prod_insert (notMem_erase a s)]; rw [insert_erase h]

Depends on / 依赖: RingHom, RingHom.toAlgebra, Subalgebra, Subalgebra.inclusion, inclusion, inf_le_left, insert_erase, notMem_erase, prod_insert, toAlgebra, toRingHom
-/
theorem mul_prod_erase [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a in s) :
    (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x := by
  rw [← prod_insert (notMem_erase a s)]; rw [insert_erase h]

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive /-- A variant of `Finset.add_sum_erase` with the addition swapped. -/]
/--
theorem `prod_erase_mul` / 定理 `prod_erase_mul`

English:
theorem prod_erase_mul
  given: [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a in s)
  proof: by rw [mul_comm, mul_prod_erase s f h]

中文:
定理 prod_erase_mul
  条件: [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a in s)
  证明: by rw [mul_comm, mul_prod_erase s f h]

Depends on / 依赖: RingHom, RingHom.toAlgebra, Subalgebra, Subalgebra.inclusion, inclusion, inf_le_right, mul_comm, mul_prod_erase, toAlgebra, toRingHom
-/
theorem prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a in s) :
    (∏ x in s.erase a, f x) * f a = ∏ x in s, f x := by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `Finset`. -/
@[to_additive /-- If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `Finset`. -/]
/--
theorem `prod_erase` / 定理 `prod_erase`

English:
theorem prod_erase
  given: [DecidableEq ι] (s : Finset ι) {f : ι -> M} {a : ι} (h : f a = 1)
  proof: by
  rw [← sdiff_singleton_eq_erase]
  refine prod_subset sdiff_subset fun x hx hnx => ?_
  grind

@[to_additive]

中文:
定理 prod_erase
  条件: [DecidableEq ι] (s : Finset ι) {f : ι -> M} {a : ι} (h : f a = 1)
  证明: by
  rw [← sdiff_singleton_eq_erase]
  refine prod_subset sdiff_subset fun x hx hnx => ?_
  grind

@[to_additive]

Depends on / 依赖: prod_subset, sdiff_singleton_eq_erase, sdiff_subset
-/
theorem prod_erase [DecidableEq ι] (s : Finset ι) {f : ι -> M} {a : ι} (h : f a = 1) :
    ∏ x in s.erase a, f x = ∏ x in s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine prod_subset sdiff_subset fun x hx hnx => ?_
  grind

@[to_additive]
/--
theorem `prod_erase_lt_of_one_lt` / 定理 `prod_erase_lt_of_one_lt`

English:
theorem prod_erase_lt_of_one_lt
  statement: {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
  proof: by
  conv in ∏ m in s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

中文:
定理 prod_erase_lt_of_one_lt
  结论: {κ : 类型} [DecidableEq ι] [CommMonoid κ] [LT κ]
  证明: by
  conv in ∏ m in s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

Depends on / 依赖: Finset, Finset.insert_erase, Finset.notMem_erase, Finset.prod_insert, insert_erase, lt_mul_of_one_lt_left, notMem_erase, prod_insert
-/
theorem prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
    [MulLeftStrictMono κ] {s : Finset ι} {d : ι} (hd : d in s) {f : ι -> κ}
    (hdf : 1 < f d) : ∏ m in s.erase d, f m < ∏ m in s, f m := by
  conv in ∏ m in s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `Finset`. -/
@[to_additive /-- If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `Finset`. -/]
/--
theorem `eq_one_of_prod_eq_one` / 定理 `eq_one_of_prod_eq_one`

English:
theorem eq_one_of_prod_eq_one
  statement: {s : Finset ι} {f : ι -> M} {a : ι} (hp : ∏ x in s, f x = 1)
  proof: by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (notMem_singleton.1 ha)]; rw [prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive]

中文:
定理 eq_one_of_prod_eq_one
  结论: {s : Finset ι} {f : ι -> M} {a : ι} (hp : ∏ x in s, f x = 1)
  证明: by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (notMem_singleton.1 ha)]; rw [prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive]

Depends on / 依赖: classical, notMem_singleton, prod_singleton, prod_subset, singleton_subset_iff
-/
theorem eq_one_of_prod_eq_one {s : Finset ι} {f : ι -> M} {a : ι} (hp : ∏ x in s, f x = 1)
    (h1 : forall x in s, x != a -> f x = 1) : forall x in s, f x = 1 := by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (notMem_singleton.1 ha)]; rw [prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive]
/--
lemma `prod_mul_eq_prod_mul_of_exists` / 引理 `prod_mul_eq_prod_mul_of_exists`

English:
lemma prod_mul_eq_prod_mul_of_exists
  statement: {s : Finset ι} {f : ι -> M} {b₁ b₂ : M}
  proof: by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm b₁]; rw [h]; rw [← mul_assoc]; rw [mul_comm _ (f a)]

@[to_additive]

中文:
引理 prod_mul_eq_prod_mul_of_exists
  结论: {s : Finset ι} {f : ι -> M} {b₁ b₂ : M}
  证明: by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm b₁]; rw [h]; rw [← mul_assoc]; rw [mul_comm _ (f a)]

@[to_additive]

Depends on / 依赖: classical, false_and, insert_erase, mem_erase, mul_assoc, mul_comm, ne_eq, not_false_eq_true, not_true_eq_false, prod_insert
-/
lemma prod_mul_eq_prod_mul_of_exists {s : Finset ι} {f : ι -> M} {b₁ b₂ : M}
    (a : ι) (ha : a in s) (h : f a * b₁ = f a * b₂) :
    (∏ a in s, f a) * b₁ = (∏ a in s, f a) * b₂ := by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm b₁]; rw [h]; rw [← mul_assoc]; rw [mul_comm _ (f a)]

@[to_additive]
/--
theorem `prod_biUnion_of_pairwise_eq_one` / 定理 `prod_biUnion_of_pairwise_eq_one`

English:
theorem prod_biUnion_of_pairwise_eq_one
  statement: [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι}
  proof: by
  classical
  let t' k := (t k).filter (fun i => f i != 1)
  have : s.biUnion t' = (s.biUnion t).filter (fun i => f i != 1) := by grind
  rw [← prod_filter_ne_one]; rw [← this]; rw [prod_biUnion]
  swap
  · intro i hi j hj hij a hai haj k hk
    have hki : k in t' i := hai hk
    have hkj : k in 

中文:
定理 prod_biUnion_of_pairwise_eq_one
  结论: [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι}
  证明: by
  classical
  let t' k := (t k).filter (fun i => f i != 1)
  have : s.biUnion t' = (s.biUnion t).filter (fun i => f i != 1) := by grind
  rw [← prod_filter_ne_one]; rw [← this]; rw [prod_biUnion]
  swap
  · intro i hi j hj hij a hai haj k hk
    have hki : k in t' i := hai hk
    have hkj : k in 

Depends on / 依赖: Finset, Finset.prod_congr, biUnion, classical, filter, mem_filter, ne_eq, prod_biUnion, prod_congr, prod_filter_ne_one, s.biUnion
-/
theorem prod_biUnion_of_pairwise_eq_one [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι}
    (hs : (s : Set κ).Pairwise fun i j => forall k in t i inter t j, f k = 1) :
    ∏ x in s.biUnion t, f x = ∏ x in s, ∏ i in t x, f i := by
  classical
  let t' k := (t k).filter (fun i => f i != 1)
  have : s.biUnion t' = (s.biUnion t).filter (fun i => f i != 1) := by grind
  rw [← prod_filter_ne_one]; rw [← this]; rw [prod_biUnion]
  swap
  · intro i hi j hj hij a hai haj k hk
    have hki : k in t' i := hai hk
    have hkj : k in t' j := haj hk
    simp only [ne_eq, mem_filter, t'] at hki hkj
    exact (hki.2 (hs hi hj hij k (by grind))).elim
  exact Finset.prod_congr rfl (fun i hi => prod_filter_ne_one (t i))

@[to_additive]
/--
lemma `prod_filter_of_pairwise_eq_one` / 引理 `prod_filter_of_pairwise_eq_one`

English:
lemma prod_filter_of_pairwise_eq_one
  statement: [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {n : κ} {I : Finset κ}
  proof: by
  classical
  have h j (hj : j in {i in I | f i = f n}.erase n) : g (f j) = 1 := by
    simp only [mem_erase, mem_filter] at hj
    exact hf hj.2.1 hn hj.1 hj.2.2
  rw [← mul_one (g (f n))]; rw [← prod_eq_one h]; rw [← mul_prod_erase {i in I | f i = f n} (fun i => g (f i)) mem_filter.mpr ⟨hn]; rw

中文:
引理 prod_filter_of_pairwise_eq_one
  结论: [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {n : κ} {I : Finset κ}
  证明: by
  classical
  have h j (hj : j in {i in I | f i = f n}.erase n) : g (f j) = 1 := by
    simp only [mem_erase, mem_filter] at hj
    exact hf hj.2.1 hn hj.1 hj.2.2
  rw [← mul_one (g (f n))]; rw [← prod_eq_one h]; rw [← mul_prod_erase {i in I | f i = f n} (fun i => g (f i)) mem_filter.mpr ⟨hn]; rw

Depends on / 依赖: classical, mem_erase, mem_filter, mem_filter.mpr, mul_one, mul_prod_erase, prod_eq_one
-/
lemma prod_filter_of_pairwise_eq_one [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {n : κ} {I : Finset κ}
    (hn : n in I) (hf : (I : Set κ).Pairwise fun i j => f i = f j -> g (f i) = 1) :
    ∏ j in I with f j = f n, g (f j) = g (f n) := by
  classical
  have h j (hj : j in {i in I | f i = f n}.erase n) : g (f j) = 1 := by
    simp only [mem_erase, mem_filter] at hj
    exact hf hj.2.1 hn hj.1 hj.2.2
  rw [← mul_one (g (f n))]; rw [← prod_eq_one h]; rw [← mul_prod_erase {i in I | f i = f n} (fun i => g (f i)) mem_filter.mpr ⟨hn]; rw [by rfl⟩]

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 1`.
The conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
/-- A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 0`.
The conclusion is the same as in `sum_image`. -/]
/--
lemma `prod_image_of_pairwise_eq_one` / 引理 `prod_image_of_pairwise_eq_one`

English:
lemma prod_image_of_pairwise_eq_one
  statement: [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {I : Finset κ}
  proof: by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm

中文:
引理 prod_image_of_pairwise_eq_one
  结论: [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {I : Finset κ}
  证明: by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm

Depends on / 依赖: prod_filter_of_pairwise_eq_one, prod_image
-/
lemma prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {I : Finset κ}
    (hf : (I : Set κ).Pairwise fun i j => f i = f j -> g (f i) = 1) :
    ∏ s in I.image f, g s = ∏ i in I, g (f i) := by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 1`. The
conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
/-- A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 0`. The
conclusion is the same as in `sum_image`. -/]
/--
lemma `prod_image_of_disjoint` / 引理 `prod_image_of_disjoint`

English:
lemma prod_image_of_disjoint
  statement: [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ -> ι} {g : ι -> M}
  proof: by
refine prod_image_of_pairwise_eq_one hf_disj.imp fun i j hdisj hfij => ?_
  rw [Function.onFun]; rw [← hfij]; rw [disjoint_self] at hdisj
  rw [hdisj]; rw [hg_bot]

@[to_additive]

中文:
引理 prod_image_of_disjoint
  结论: [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ -> ι} {g : ι -> M}
  证明: by
refine prod_image_of_pairwise_eq_one hf_disj.imp fun i j hdisj hfij => ?_
  rw [Function.onFun]; rw [← hfij]; rw [disjoint_self] at hdisj
  rw [hdisj]; rw [hg_bot]

@[to_additive]

Depends on / 依赖: Function, Function.onFun, disjoint_self, hf_disj, hf_disj.imp, hg_bot, prod_image_of_pairwise_eq_one
-/
lemma prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ -> ι} {g : ι -> M}
    (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).PairwiseDisjoint f) :
    ∏ s in I.image f, g s = ∏ i in I, g (f i) := by
refine prod_image_of_pairwise_eq_one hf_disj.imp fun i j hdisj hfij => ?_
  rw [Function.onFun]; rw [← hfij]; rw [disjoint_self] at hdisj
  rw [hdisj]; rw [hg_bot]

@[to_additive]
/--
theorem `prod_unique_nonempty` / 定理 `prod_unique_nonempty`

English:
theorem prod_unique_nonempty
  given: [Unique ι] (s : Finset ι) (f : ι -> M) (h : s.Nonempty)
  proof: by
  rw [h.eq_singleton_default]; rw [Finset.prod_singleton]

中文:
定理 prod_unique_nonempty
  条件: [Unique ι] (s : Finset ι) (f : ι -> M) (h : s.Nonempty)
  证明: by
  rw [h.eq_singleton_default]; rw [Finset.prod_singleton]

Depends on / 依赖: Finset, Finset.prod_singleton, eq_singleton_default, h.eq_singleton_default, prod_singleton
-/
theorem prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι -> M) (h : s.Nonempty) :
    ∏ x in s, f x = f default := by
  rw [h.eq_singleton_default]; rw [Finset.prod_singleton]

/--
lemma `prod_dvd_prod_of_dvd` / 引理 `prod_dvd_prod_of_dvd`

English:
lemma prod_dvd_prod_of_dvd
  given: (f g : ι -> M) (h : forall i in s, f i ∣ g i)
  proof: Multiset.prod_dvd_prod_of_dvd _ _ h

@[to_additive]

中文:
引理 prod_dvd_prod_of_dvd
  条件: (f g : ι -> M) (h : 对任意 i in s, f i ∣ g i)
  证明: Multiset.prod_dvd_prod_of_dvd _ _ h

@[to_additive]

Depends on / 依赖: Multiset, Multiset.prod_dvd_prod_of_dvd, prod_dvd_prod_of_dvd
-/
lemma prod_dvd_prod_of_dvd (f g : ι -> M) (h : forall i in s, f i ∣ g i) :
    ∏ i in s, f i ∣ ∏ i in s, g i :=
  Multiset.prod_dvd_prod_of_dvd _ _ h

@[to_additive]
/--
theorem `prod_map_equiv` / 定理 `prod_map_equiv`

English:
theorem prod_map_equiv
  given: (e : ι ≃ κ)
  statement: (s.map e).prod (f ∘ e.symm) = s.prod f
  proof: by simp

@[to_additive]

中文:
定理 prod_map_equiv
  条件: (e : ι ≃ κ)
  结论: (s.map e).prod (f ∘ e.symm) = s.prod f
  证明: by simp

@[to_additive]
-/
theorem prod_map_equiv (e : ι ≃ κ) : (s.map e).prod (f ∘ e.symm) = s.prod f := by simp

@[to_additive]
/--
theorem `prod_comp_equiv` / 定理 `prod_comp_equiv`

English:
theorem prod_comp_equiv
  given: {f : κ -> M} (e : ι ≃ κ)
  statement: s.prod (f ∘ e) = (s.map e).prod f
  proof: by simp

中文:
定理 prod_comp_equiv
  条件: {f : κ -> M} (e : ι ≃ κ)
  结论: s.prod (f ∘ e) = (s.map e).prod f
  证明: by simp
-/
theorem prod_comp_equiv {f : κ -> M} (e : ι ≃ κ) : s.prod (f ∘ e) = (s.map e).prod f := by simp

end CommMonoid

section CancelCommMonoid
variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι -> M}

@[to_additive]
/--
lemma `prod_sdiff_eq_prod_sdiff_iff` / 引理 `prod_sdiff_eq_prod_sdiff_iff`

English:
lemma prod_sdiff_eq_prod_sdiff_iff
  proof: eq_comm.trans eq_iff_eq_of_mul_eq_mul by
    rw [← prod_union disjoint_sdiff_self_left]; rw [← prod_union disjoint_sdiff_self_left]; rw [sdiff_union_self_eq_union]; rw [sdiff_union_self_eq_union]; rw [union_comm]

@[to_additive]

中文:
引理 prod_sdiff_eq_prod_sdiff_iff
  证明: eq_comm.trans eq_iff_eq_of_mul_eq_mul by
    rw [← prod_union disjoint_sdiff_self_left]; rw [← prod_union disjoint_sdiff_self_left]; rw [sdiff_union_self_eq_union]; rw [sdiff_union_self_eq_union]; rw [union_comm]

@[to_additive]

Depends on / 依赖: disjoint_sdiff_self_left, eq_comm, eq_comm.trans, eq_iff_eq_of_mul_eq_mul, prod_union, sdiff_union_self_eq_union, union_comm
-/
lemma prod_sdiff_eq_prod_sdiff_iff :
    ∏ i in s \ t, f i = ∏ i in t \ s, f i ↔ ∏ i in s, f i = ∏ i in t, f i :=
eq_comm.trans eq_iff_eq_of_mul_eq_mul by
    rw [← prod_union disjoint_sdiff_self_left]; rw [← prod_union disjoint_sdiff_self_left]; rw [sdiff_union_self_eq_union]; rw [sdiff_union_self_eq_union]; rw [union_comm]

@[to_additive]
/--
lemma `prod_sdiff_ne_prod_sdiff_iff` / 引理 `prod_sdiff_ne_prod_sdiff_iff`

English:
lemma prod_sdiff_ne_prod_sdiff_iff
  proof: prod_sdiff_eq_prod_sdiff_iff.not

中文:
引理 prod_sdiff_ne_prod_sdiff_iff
  证明: prod_sdiff_eq_prod_sdiff_iff.not

Depends on / 依赖: prod_sdiff_eq_prod_sdiff_iff, prod_sdiff_eq_prod_sdiff_iff.not
-/
lemma prod_sdiff_ne_prod_sdiff_iff :
    ∏ i in s \ t, f i != ∏ i in t \ s, f i ↔ ∏ i in s, f i != ∏ i in t, f i :=
  prod_sdiff_eq_prod_sdiff_iff.not

end CancelCommMonoid

section CommGroup
variable [CommGroup G] [DecidableEq ι] {f : ι -> G}

@[to_additive]
/--
lemma `prod_insert_div` / 引理 `prod_insert_div`

English:
lemma prod_insert_div
  given: (ha : a ∉ s) (f : ι -> G)
  proof: by simp [ha]

@[to_additive (attr := simp)]

中文:
引理 prod_insert_div
  条件: (ha : a ∉ s) (f : ι -> G)
  证明: by simp [ha]

@[to_additive (attr := simp)]
-/
lemma prod_insert_div (ha : a ∉ s) (f : ι -> G) :
    (∏ x in insert a s, f x) / f a = ∏ x in s, f x := by simp [ha]

@[to_additive (attr := simp)]
/--
theorem `prod_erase_eq_div` / 定理 `prod_erase_eq_div`

English:
theorem prod_erase_eq_div
  given: {a : ι} (h : a in s)
  statement: ∏ x in s.erase a, f x = (∏ x in s, f x) / f a
  proof: by
  rw [eq_div_iff_mul_eq']; rw [prod_erase_mul _ _ h]

中文:
定理 prod_erase_eq_div
  条件: {a : ι} (h : a in s)
  结论: ∏ x in s.erase a, f x = (∏ x in s, f x) / f a
  证明: by
  rw [eq_div_iff_mul_eq']; rw [prod_erase_mul _ _ h]

Depends on / 依赖: eq_div_iff_mul_eq, prod_erase_mul
-/
theorem prod_erase_eq_div {a : ι} (h : a in s) : ∏ x in s.erase a, f x = (∏ x in s, f x) / f a := by
  rw [eq_div_iff_mul_eq']; rw [prod_erase_mul _ _ h]

/-- A telescoping product along `{0, ..., n - 1}` of a commutative-group-valued function reduces to
the ratio of the last and first factors. -/
@[to_additive /-- A telescoping sum along `{0, ..., n - 1}` of a function valued in a commutative
additive group reduces to the difference of the last and first terms. -/]
/--
lemma `prod_range_div` / 引理 `prod_range_div`

English:
lemma prod_range_div
  given: (f : Nat -> G) (n : Nat)
  statement: (∏ i in range n, f (i + 1) / f i) = f n / f 0
  proof: by
  apply prod_range_induction <;> simp

中文:
引理 prod_range_div
  条件: (f : 自然数 -> G) (n : 自然数)
  结论: (∏ i in range n, f (i + 1) / f i) = f n / f 0
  证明: by
  apply prod_range_induction <;> simp

Depends on / 依赖: prod_range_induction
-/
lemma prod_range_div (f : Nat -> G) (n : Nat) : (∏ i in range n, f (i + 1) / f i) = f n / f 0 := by
  apply prod_range_induction <;> simp

/-- A reversed telescoping product along `{0, ..., n - 1}` of a commutative-group-valued function
reduces to the ratio of the first and last factors. -/
@[to_additive /-- A reversed telescoping sum along `{0, ..., n - 1}` of a function valued in a
commutative additive group reduces to the difference of the first and last terms. -/]
/--
lemma `prod_range_div'` / 引理 `prod_range_div'`

English:
lemma prod_range_div'
  given: (f : Nat -> G) (n : Nat)
  statement: (∏ i in range n, f i / f (i + 1)) = f 0 / f n
  proof: by
  apply prod_range_induction <;> simp

中文:
引理 prod_range_div'
  条件: (f : 自然数 -> G) (n : 自然数)
  结论: (∏ i in range n, f i / f (i + 1)) = f 0 / f n
  证明: by
  apply prod_range_induction <;> simp

Depends on / 依赖: prod_range_induction
-/
lemma prod_range_div' (f : Nat -> G) (n : Nat) : (∏ i in range n, f i / f (i + 1)) = f 0 / f n := by
  apply prod_range_induction <;> simp

/-- Express `f n` as `f 0` multiplied by the telescoping product of consecutive ratios from
`0` to `n - 1`. -/
@[to_additive /-- Express `f n` as `f 0` plus the telescoping sum of consecutive differences from
`0` to `n - 1`. -/]
/--
lemma `eq_prod_range_div` / 引理 `eq_prod_range_div`

English:
lemma eq_prod_range_div
  given: (f : Nat -> G) (n : Nat)
  statement: f n = f 0 * ∏ i in range n, f (i + 1) / f i
  proof: by
  rw [prod_range_div]; rw [mul_div_cancel]

@[to_additive]

中文:
引理 eq_prod_range_div
  条件: (f : 自然数 -> G) (n : 自然数)
  结论: f n = f 0 * ∏ i in range n, f (i + 1) / f i
  证明: by
  rw [prod_range_div]; rw [mul_div_cancel]

@[to_additive]

Depends on / 依赖: mul_div_cancel, prod_range_div
-/
lemma eq_prod_range_div (f : Nat -> G) (n : Nat) : f n = f 0 * ∏ i in range n, f (i + 1) / f i := by
  rw [prod_range_div]; rw [mul_div_cancel]

@[to_additive]
/--
lemma `eq_prod_range_div'` / 引理 `eq_prod_range_div'`

English:
lemma eq_prod_range_div'
  given: (f : Nat -> G) (n : Nat)
  proof: by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

@[to_additive]

中文:
引理 eq_prod_range_div'
  条件: (f : 自然数 -> G) (n : 自然数)
  证明: by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

@[to_additive]

Depends on / 依赖: Finset, Finset.eq_prod_range_div, Finset.prod_range_succ, conv_lhs, eq_prod_range_div, mul_comm, prod_range_succ
-/
lemma eq_prod_range_div' (f : Nat -> G) (n : Nat) :
    f n = ∏ i in range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

@[to_additive]
/--
lemma `prod_range_add_div_prod_range` / 引理 `prod_range_add_div_prod_range`

English:
lemma prod_range_add_div_prod_range
  given: (f : Nat -> G) (n m : Nat)
  proof: div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive (attr := simp)]

中文:
引理 prod_range_add_div_prod_range
  条件: (f : 自然数 -> G) (n m : 自然数)
  证明: div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_of_eq_mul, prod_range_add
-/
lemma prod_range_add_div_prod_range (f : Nat -> G) (n m : Nat) :
    (∏ k in range (n + m), f k) / ∏ k in range n, f k = ∏ k in Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive (attr := simp)]
/--
lemma `prod_sdiff_eq_div` / 引理 `prod_sdiff_eq_div`

English:
lemma prod_sdiff_eq_div
  given: (h : s₁ subseteq s₂)
  statement: ∏ x in s₂ \ s₁, f x = (∏ x in s₂, f x) / ∏ x in s₁, f x
  proof: by
  rw [eq_div_iff_mul_eq']; rw [prod_sdiff h]

@[to_additive]

中文:
引理 prod_sdiff_eq_div
  条件: (h : s₁ subseteq s₂)
  结论: ∏ x in s₂ \ s₁, f x = (∏ x in s₂, f x) / ∏ x in s₁, f x
  证明: by
  rw [eq_div_iff_mul_eq']; rw [prod_sdiff h]

@[to_additive]

Depends on / 依赖: eq_div_iff_mul_eq, prod_sdiff
-/
lemma prod_sdiff_eq_div (h : s₁ subseteq s₂) : ∏ x in s₂ \ s₁, f x = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  rw [eq_div_iff_mul_eq']; rw [prod_sdiff h]

@[to_additive]
/--
theorem `prod_sdiff_div_prod_sdiff` / 定理 `prod_sdiff_div_prod_sdiff`

English:
theorem prod_sdiff_div_prod_sdiff
  proof: by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

中文:
定理 prod_sdiff_div_prod_sdiff
  证明: by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

Depends on / 依赖: Finset, Finset.prod_sdiff, inf_le_left, inf_le_right, prod_sdiff
-/
theorem prod_sdiff_div_prod_sdiff :
    (∏ x in s₂ \ s₁, f x) / ∏ x in s₁ \ s₂, f x = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

end CommGroup

section OrderedSub
variable [AddCommMonoid M] [PartialOrder M] [Sub M] [OrderedSub M] [AddLeftMono M]
  [AddLeftReflectLE M] [ExistsAddOfLE M]

/--
lemma `sum_range_tsub` / 引理 `sum_range_tsub`

English:
lemma sum_range_tsub
  given: {f : Nat -> M} (h : Monotone f) (n : Nat)
  proof: by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n _
    have h₁ : f n <= f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 <= f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂]; rw [add_tsub_cancel_of_le h₁]

中文:
引理 sum_range_tsub
  条件: {f : 自然数 -> M} (h : Monotone f) (n : 自然数)
  证明: by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n _
    have h₁ : f n <= f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 <= f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂]; rw [add_tsub_cancel_of_le h₁]

Depends on / 依赖: Nat.le_succ, Nat.zero_le, add_tsub_cancel_of_le, le_succ, sum_range_induction, tsub_add_eq_add_tsub, tsub_eq_of_eq_add, zero_add, zero_le
-/
lemma sum_range_tsub {f : Nat -> M} (h : Monotone f) (n : Nat) :
    ∑ i in range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n _
    have h₁ : f n <= f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 <= f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂]; rw [add_tsub_cancel_of_le h₁]

/--
lemma `sum_tsub_distrib` / 引理 `sum_tsub_distrib`

English:
lemma sum_tsub_distrib
  given: (s : Finset ι) {f g : ι -> M} (hfg : forall x in s, g x <= f x)
  proof: Multiset.sum_map_tsub _ hfg

中文:
引理 sum_tsub_distrib
  条件: (s : Finset ι) {f g : ι -> M} (hfg : 对任意 x in s, g x <= f x)
  证明: Multiset.sum_map_tsub _ hfg

Depends on / 依赖: Multiset, Multiset.sum_map_tsub, sum_map_tsub
-/
lemma sum_tsub_distrib (s : Finset ι) {f g : ι -> M} (hfg : forall x in s, g x <= f x) :
    ∑ x in s, (f x - g x) = ∑ x in s, f x - ∑ x in s, g x := Multiset.sum_map_tsub _ hfg

end OrderedSub

section Nat

/--
lemma `card_eq_sum_ones` / 引理 `card_eq_sum_ones`

English:
lemma card_eq_sum_ones
  given: (s : Finset ι)
  statement: #s = ∑ _ in s, 1
  proof: by simp

中文:
引理 card_eq_sum_ones
  条件: (s : Finset ι)
  结论: #s = ∑ _ in s, 1
  证明: by simp
-/
lemma card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s, 1 := by simp

/--
theorem `sum_const_nat` / 定理 `sum_const_nat`

English:
theorem sum_const_nat
  given: {m : Nat} {f : ι -> Nat} (h₁ : forall x in s, f x = m)
  statement: ∑ x in s, f x = #s * m
  proof: by
  rw [← Nat.nsmul_eq_mul]; rw [← sum_const]
  apply sum_congr rfl h₁

中文:
定理 sum_const_nat
  条件: {m : 自然数} {f : ι -> 自然数} (h₁ : 对任意 x in s, f x = m)
  结论: ∑ x in s, f x = #s * m
  证明: by
  rw [← Nat.nsmul_eq_mul]; rw [← sum_const]
  apply sum_congr rfl h₁

Depends on / 依赖: Nat.nsmul_eq_mul, nsmul_eq_mul, sum_congr, sum_const
-/
theorem sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : forall x in s, f x = m) : ∑ x in s, f x = #s * m := by
  rw [← Nat.nsmul_eq_mul]; rw [← sum_const]
  apply sum_congr rfl h₁

/--
lemma `sum_card_fiberwise_eq_card_filter` / 引理 `sum_card_fiberwise_eq_card_filter`

English:
lemma sum_card_fiberwise_eq_card_filter
  statement: {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
  proof: by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

@[simp]

中文:
引理 sum_card_fiberwise_eq_card_filter
  结论: {κ : 类型} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
  证明: by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

@[simp]

Depends on / 依赖: card_eq_sum_ones, sum_fiberwise_eq_sum_filter
-/
lemma sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι -> κ) : ∑ j in t, #{i in s | g i = j} = #{i in s | g i in t} := by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

@[simp]
/--
theorem `card_disjiUnion` / 定理 `card_disjiUnion`

English:
theorem card_disjiUnion
  given: (s : Finset ι) (t : ι -> Finset M) (h)
  proof: Multiset.card_bind _ _

中文:
定理 card_disjiUnion
  条件: (s : Finset ι) (t : ι -> Finset M) (h)
  证明: Multiset.card_bind _ _

Depends on / 依赖: Multiset, Multiset.card_bind, card_bind
-/
theorem card_disjiUnion (s : Finset ι) (t : ι -> Finset M) (h) :
    #(s.disjiUnion t h) = ∑ a in s, #(t a) :=
  Multiset.card_bind _ _

/--
theorem `card_biUnion` / 定理 `card_biUnion`

English:
theorem card_biUnion
  given: [DecidableEq M] {t : ι -> Finset M} (h : (s : Set ι).PairwiseDisjoint t)
  proof: by simpa using sum_biUnion h (M := Nat) (f := 1)

中文:
定理 card_biUnion
  条件: [DecidableEq M] {t : ι -> Finset M} (h : (s : Set ι).PairwiseDisjoint t)
  证明: by simpa using sum_biUnion h (M := Nat) (f := 1)

Depends on / 依赖: sum_biUnion
-/
theorem card_biUnion [DecidableEq M] {t : ι -> Finset M} (h : (s : Set ι).PairwiseDisjoint t) :
    #(s.biUnion t) = ∑ u in s, #(t u) := by simpa using sum_biUnion h (M := Nat) (f := 1)

/--
theorem `card_biUnion_le` / 定理 `card_biUnion_le`

English:
theorem card_biUnion_le
  given: [DecidableEq M] {s : Finset ι} {t : ι -> Finset M}
  proof: haveI := Classical.decEq ι
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) <= #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ <= ∑ a in insert a s, #(t a) := by grind

中文:
定理 card_biUnion_le
  条件: [DecidableEq M] {s : Finset ι} {t : ι -> Finset M}
  证明: haveI := Classical.decEq ι
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) <= #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ <= ∑ a in insert a s, #(t a) := by grind

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, biUnion, biUnion_insert, card_union_le, induction_on, insert, s.biUnion
-/
theorem card_biUnion_le [DecidableEq M] {s : Finset ι} {t : ι -> Finset M} :
    #(s.biUnion t) <= ∑ a in s, #(t a) :=
  haveI := Classical.decEq ι
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) <= #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ <= ∑ a in insert a s, #(t a) := by grind

/--
theorem `card_eq_sum_card_fiberwise` / 定理 `card_eq_sum_card_fiberwise`

English:
theorem card_eq_sum_card_fiberwise
  statement: [DecidableEq M] {f : ι -> M} {s : Finset ι} {t : Finset M}
  proof: by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

中文:
定理 card_eq_sum_card_fiberwise
  结论: [DecidableEq M] {f : ι -> M} {s : Finset ι} {t : Finset M}
  证明: by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

Depends on / 依赖: card_eq_sum_ones, sum_fiberwise_of_maps_to
-/
theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι -> M} {s : Finset ι} {t : Finset M}
    (H : (s : Set ι).MapsTo f t) : #s = ∑ b in t, #{a in s | f a = b} := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

/--
theorem `card_eq_sum_card_image` / 定理 `card_eq_sum_card_image`

English:
theorem card_eq_sum_card_image
  given: [DecidableEq M] (f : ι -> M) (s : Finset ι)
  proof: card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

中文:
定理 card_eq_sum_card_image
  条件: [DecidableEq M] (f : ι -> M) (s : Finset ι)
  证明: card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

Depends on / 依赖: card_eq_sum_card_fiberwise, mem_image_of_mem
-/
theorem card_eq_sum_card_image [DecidableEq M] (f : ι -> M) (s : Finset ι) :
    #s = ∑ b in s.image f, #{a in s | f a = b} :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

end Nat
end Finset

namespace Fintype
variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid M]

@[to_additive]
/--
lemma `prod_of_injective` / 引理 `prod_of_injective`

English:
lemma prod_of_injective
  statement: (e : ι -> κ) (he : Injective e) (f : ι -> M) (g : κ -> M)
  proof: prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ => h i)

@[to_additive]

中文:
引理 prod_of_injective
  结论: (e : ι -> κ) (he : Injective e) (f : ι -> M) (g : κ -> M)
  证明: prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ => h i)

@[to_additive]

Depends on / 依赖: he.injOn, prod_of_injOn
-/
lemma prod_of_injective (e : ι -> κ) (he : Injective e) (f : ι -> M) (g : κ -> M)
    (h' : forall i ∉ Set.range e, g i = 1) (h : forall i, f i = g (e i)) : ∏ i, f i = ∏ j, g j :=
  prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ => h i)

@[to_additive]
/--
lemma `prod_fiberwise` / 引理 `prod_fiberwise`

English:
lemma prod_fiberwise
  given: [DecidableEq κ] (g : ι -> κ) (f : ι -> M)
  proof: by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]

中文:
引理 prod_fiberwise
  条件: [DecidableEq κ] (g : ι -> κ) (f : ι -> M)
  证明: by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_fiberwise, prod_fiberwise, prod_subtype
-/
lemma prod_fiberwise [DecidableEq κ] (g : ι -> κ) (f : ι -> M) :
    ∏ j, ∏ i : {i // g i = j}, f i = ∏ i, f i := by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]
/--
lemma `prod_fiberwise'` / 引理 `prod_fiberwise'`

English:
lemma prod_fiberwise'
  given: [DecidableEq κ] (g : ι -> κ) (f : κ -> M)
  proof: by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ => _).symm

@[to_additive]

中文:
引理 prod_fiberwise'
  条件: [DecidableEq κ] (g : ι -> κ) (f : κ -> M)
  证明: by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ => _).symm

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_fiberwise, prod_fiberwise, prod_subtype
-/
lemma prod_fiberwise' [DecidableEq κ] (g : ι -> κ) (f : κ -> M) :
    ∏ j, ∏ _i : {i // g i = j}, f j = ∏ i, f (g i) := by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ => _).symm

@[to_additive]
/--
theorem `prod_unique` / 定理 `prod_unique`

English:
theorem prod_unique
  given: [Unique ι] (f : ι -> M)
  statement: ∏ x : ι, f x = f default
  proof: by
  rw [univ_unique]; rw [prod_singleton]

@[to_additive]

中文:
定理 prod_unique
  条件: [Unique ι] (f : ι -> M)
  结论: ∏ x : ι, f x = f default
  证明: by
  rw [univ_unique]; rw [prod_singleton]

@[to_additive]

Depends on / 依赖: prod_singleton, univ_unique
-/
theorem prod_unique [Unique ι] (f : ι -> M) : ∏ x : ι, f x = f default := by
  rw [univ_unique]; rw [prod_singleton]

@[to_additive]
/--
theorem `prod_subsingleton` / 定理 `prod_subsingleton`

English:
theorem prod_subsingleton
  given: [Subsingleton ι] (f : ι -> M) (a : ι)
  statement: ∏ x : ι, f x = f a
  proof: by
  have : Unique ι := uniqueOfSubsingleton a
  rw [prod_unique f]; rw [Subsingleton.elim default a]

中文:
定理 prod_subsingleton
  条件: [Subsingleton ι] (f : ι -> M) (a : ι)
  结论: ∏ x : ι, f x = f a
  证明: by
  have : Unique ι := uniqueOfSubsingleton a
  rw [prod_unique f]; rw [Subsingleton.elim default a]

Depends on / 依赖: Subsingleton, Subsingleton.elim, Unique, prod_unique, uniqueOfSubsingleton
-/
theorem prod_subsingleton [Subsingleton ι] (f : ι -> M) (a : ι) : ∏ x : ι, f x = f a := by
  have : Unique ι := uniqueOfSubsingleton a
  rw [prod_unique f]; rw [Subsingleton.elim default a]

/--
theorem `prod_Prop` / 定理 `prod_Prop`

English:
theorem prod_Prop
  given: (f : Prop -> M)
  statement: ∏ p, f p = f True * f False
  proof: by simp

@[to_additive]

中文:
定理 prod_Prop
  条件: (f : 命题 -> M)
  结论: ∏ p, f p = f True * f False
  证明: by simp

@[to_additive]
-/
@[to_additive] theorem prod_Prop (f : Prop -> M) : ∏ p, f p = f True * f False := by simp

@[to_additive]
/--
theorem `prod_subtype_mul_prod_subtype` / 定理 `prod_subtype_mul_prod_subtype`

English:
theorem prod_subtype_mul_prod_subtype
  given: (p : ι -> Prop) (f : ι -> M) [DecidablePred p]
  proof: by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s]; rw [← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

中文:
定理 prod_subtype_mul_prod_subtype
  条件: (p : ι -> 命题) (f : ι -> M) [DecidablePred p]
  证明: by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s]; rw [← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

Depends on / 依赖: Finset, Finset.prod_mul_prod_compl, Finset.prod_subtype, classical, prod_mul_prod_compl, prod_subtype, toFinset
-/
theorem prod_subtype_mul_prod_subtype (p : ι -> Prop) (f : ι -> M) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s]; rw [← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

/--
lemma `prod_subset` / 引理 `prod_subset`

English:
lemma prod_subset
  given: {s : Finset ι} {f : ι -> M} (h : forall i, f i != 1 -> i in s)
  proof: Finset.prod_subset s.subset_univ by simpa [not_imp_comm (a := _ in s)]

中文:
引理 prod_subset
  条件: {s : Finset ι} {f : ι -> M} (h : 对任意 i, f i != 1 -> i in s)
  证明: Finset.prod_subset s.subset_univ by simpa [not_imp_comm (a := _ in s)]
-/
@[to_additive] lemma prod_subset {s : Finset ι} {f : ι -> M} (h : forall i, f i != 1 -> i in s) :
    ∏ i in s, f i = ∏ i, f i :=
Finset.prod_subset s.subset_univ by simpa [not_imp_comm (a := _ in s)]

end CommMonoid
end Fintype

namespace List

@[to_additive]
/--
theorem `prod_toFinset` / 定理 `prod_toFinset`

English:
theorem prod_toFinset
  given: {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι -> M)
  proof: List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp notMem), prod_toFinset _ hl]

@[simp]

中文:
定理 prod_toFinset
  条件: {M : 类型} [DecidableEq ι] [CommMonoid M] (f : ι -> M)
  证明: List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp notMem), prod_toFinset _ hl]

@[simp]

Depends on / 依赖: List.nodup_cons.mp, nodup_cons
-/
theorem prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι -> M) :
    forall {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨notMem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp notMem), prod_toFinset _ hl]

@[simp]
/--
theorem `sum_toFinset_count_eq_length` / 定理 `sum_toFinset_count_eq_length`

English:
theorem sum_toFinset_count_eq_length
  given: [DecidableEq ι] (l : List ι)
  proof: by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : Nat)).symm

中文:
定理 sum_toFinset_count_eq_length
  条件: [DecidableEq ι] (l : List ι)
  证明: by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : Nat)).symm

Depends on / 依赖: Finset, Finset.sum_list_map_count, List.map_const, map_const, sum_list_map_count
-/
theorem sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) :
    ∑ a in l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : Nat)).symm

end List

namespace Multiset

@[simp]
/--
lemma `mem_sum` / 引理 `mem_sum`

English:
lemma mem_sum
  given: {a : M} {s : Finset ι} {m : ι -> Multiset M}
  proof: by
  induction s using Finset.cons_induction with grind

@[to_additive]

中文:
引理 mem_sum
  条件: {a : M} {s : Finset ι} {m : ι -> Multiset M}
  证明: by
  induction s using Finset.cons_induction with grind

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma mem_sum {a : M} {s : Finset ι} {m : ι -> Multiset M} :
    a in ∑ i in s, m i ↔ exists i in s, a in m i := by
  induction s using Finset.cons_induction with grind

@[to_additive]
/--
lemma `prod_map_prod` / 引理 `prod_map_prod`

English:
lemma prod_map_prod
  given: {α : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α} {f : ι -> α -> M}
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, prod_map_mul, ih]

中文:
引理 prod_map_prod
  条件: {α : 类型} [CommMonoid M] {m : Multiset ι} {s : Finset α} {f : ι -> α -> M}
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, prod_map_mul, ih]

Depends on / 依赖: Finset, Finset.induction, Finset.prod_insert, classical, insert, prod_insert, prod_map_mul
-/
lemma prod_map_prod {α : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α} {f : ι -> α -> M} :
    (m.map fun i => ∏ a in s, f i a).prod = ∏ a in s, (m.map fun i => f i a).prod := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, prod_map_mul, ih]

variable [DecidableEq ι]

/--
theorem `toFinset_sum_count_eq` / 定理 `toFinset_sum_count_eq`

English:
theorem toFinset_sum_count_eq
  given: (s : Multiset ι)
  statement: ∑ a in s.toFinset, s.count a = card s
  proof: by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : Nat))).symm

中文:
定理 toFinset_sum_count_eq
  条件: (s : Multiset ι)
  结论: ∑ a in s.toFinset, s.count a = card s
  证明: by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : Nat))).symm

Depends on / 依赖: Finset, Finset.sum_multiset_map_count, sum_multiset_map_count
-/
theorem toFinset_sum_count_eq (s : Multiset ι) : ∑ a in s.toFinset, s.count a = card s := by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : Nat))).symm

/--
lemma `sum_count_eq_card` / 引理 `sum_count_eq_card`

English:
lemma sum_count_eq_card
  given: {s : Finset ι} {m : Multiset ι} (hms : forall a in m, a in s)
  proof: by
  rw [← toFinset_sum_count_eq]; rw [← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[simp]

中文:
引理 sum_count_eq_card
  条件: {s : Finset ι} {m : Multiset ι} (hms : 对任意 a in m, a in s)
  证明: by
  rw [← toFinset_sum_count_eq]; rw [← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[simp]
-/
@[simp] lemma sum_count_eq_card {s : Finset ι} {m : Multiset ι} (hms : forall a in m, a in s) :
    ∑ a in s, m.count a = card m := by
  rw [← toFinset_sum_count_eq]; rw [← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[simp]
/--
theorem `toFinset_sum_count_nsmul_eq` / 定理 `toFinset_sum_count_nsmul_eq`

English:
theorem toFinset_sum_count_nsmul_eq
  given: (s : Multiset ι)
  proof: by
  rw [← Finset.sum_multiset_map_count]; rw [Multiset.sum_map_singleton]

中文:
定理 toFinset_sum_count_nsmul_eq
  条件: (s : Multiset ι)
  证明: by
  rw [← Finset.sum_multiset_map_count]; rw [Multiset.sum_map_singleton]

Depends on / 依赖: Finset, Finset.sum_multiset_map_count, Multiset, Multiset.sum_map_singleton, sum_map_singleton, sum_multiset_map_count
-/
theorem toFinset_sum_count_nsmul_eq (s : Multiset ι) :
    ∑ a in s.toFinset, s.count a • {a} = s := by
  rw [← Finset.sum_multiset_map_count]; rw [Multiset.sum_map_singleton]

/--
theorem `exists_smul_of_dvd_count` / 定理 `exists_smul_of_dvd_count`

English:
theorem exists_smul_of_dvd_count
  statement: (s : Multiset ι) {k : Nat}
  proof: by
  use ∑ a in s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x in s.toFinset, k • (count x s / k) • ({x} : Multiset ι)) =
      ∑ x in s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul']; rw [Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  

中文:
定理 exists_smul_of_dvd_count
  结论: (s : Multiset ι) {k : 自然数}
  证明: by
  use ∑ a in s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x in s.toFinset, k • (count x s / k) • ({x} : Multiset ι)) =
      ∑ x in s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul']; rw [Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_nsmul, Multiset, Nat.mul_div_cancel, mem_toFinset, mem_toFinset.mp, mul_div_cancel, mul_nsmul, s.count, s.toFinset, sum_congr, sum_nsmul, toFinset, toFinset_sum_count_nsmul_eq
-/
theorem exists_smul_of_dvd_count (s : Multiset ι) {k : Nat}
    (h : forall a : ι, a in s -> k ∣ Multiset.count a s) : exists u : Multiset ι, s = k • u := by
  use ∑ a in s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x in s.toFinset, k • (count x s / k) • ({x} : Multiset ι)) =
      ∑ x in s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul']; rw [Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul]; rw [h₂]; rw [toFinset_sum_count_nsmul_eq]

@[to_additive]
/--
theorem `prod_sum` / 定理 `prod_sum`

English:
theorem prod_sum
  given: {ι : Type*} [CommMonoid M] (f : ι -> Multiset M) (s : Finset ι)
  proof: by
  induction s using Finset.cons_induction with grind

中文:
定理 prod_sum
  条件: {ι : 类型} [CommMonoid M] (f : ι -> Multiset M) (s : Finset ι)
  证明: by
  induction s using Finset.cons_induction with grind

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
theorem prod_sum {ι : Type*} [CommMonoid M] (f : ι -> Multiset M) (s : Finset ι) :
    (∑ x in s, f x).prod = ∏ x in s, (f x).prod := by
  induction s using Finset.cons_induction with grind

end Multiset

@[to_additive (attr := simp)]
/--
lemma `IsUnit.multisetProd_iff` / 引理 `IsUnit.multisetProd_iff`

English:
lemma IsUnit.multisetProd_iff
  given: [CommMonoid M] {s : Multiset M}
  proof: by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simpa using fun _ => ih

@[to_additive (attr := simp)]

中文:
引理 IsUnit.multisetProd_iff
  条件: [CommMonoid M] {s : Multiset M}
  证明: by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simpa using fun _ => ih

@[to_additive (attr := simp)]

Depends on / 依赖: Multiset, Multiset.induction
-/
lemma IsUnit.multisetProd_iff [CommMonoid M] {s : Multiset M} :
    IsUnit s.prod ↔ forall a in s, IsUnit a := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simpa using fun _ => ih

@[to_additive (attr := simp)]
/--
lemma `IsUnit.prod_iff` / 引理 `IsUnit.prod_iff`

English:
lemma IsUnit.prod_iff
  given: [CommMonoid M] {f : ι -> M}
  proof: by
  induction s using Finset.cons_induction with grind

@[to_additive]

中文:
引理 IsUnit.prod_iff
  条件: [CommMonoid M] {f : ι -> M}
  证明: by
  induction s using Finset.cons_induction with grind

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma IsUnit.prod_iff [CommMonoid M] {f : ι -> M} :
    IsUnit (∏ a in s, f a) ↔ forall a in s, IsUnit (f a) := by
  induction s using Finset.cons_induction with grind

@[to_additive]
/--
lemma `IsUnit.prod_univ_iff` / 引理 `IsUnit.prod_univ_iff`

English:
lemma IsUnit.prod_univ_iff
  given: [Fintype ι] [CommMonoid M] {f : ι -> M}
  proof: by simp

中文:
引理 IsUnit.prod_univ_iff
  条件: [Fintype ι] [CommMonoid M] {f : ι -> M}
  证明: by simp
-/
lemma IsUnit.prod_univ_iff [Fintype ι] [CommMonoid M] {f : ι -> M} :
    IsUnit (∏ a, f a) ↔ forall a, IsUnit (f a) := by simp

/--
theorem `Int.natAbs_sum_le` / 定理 `Int.natAbs_sum_le`

English:
theorem Int.natAbs_sum_le
  given: (s : Finset ι) (f : ι -> Int)
  proof: by
  induction s using Finset.cons_induction with grind

@[deprecated (since := "2026-02-14")]
alias nat_abs_sum_le := Int.natAbs_sum_le

中文:
定理 Int.natAbs_sum_le
  条件: (s : Finset ι) (f : ι -> 整数)
  证明: by
  induction s using Finset.cons_induction with grind

@[deprecated (since := "2026-02-14")]
alias nat_abs_sum_le := Int.natAbs_sum_le

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
theorem Int.natAbs_sum_le (s : Finset ι) (f : ι -> Int) :
    (∑ i in s, f i).natAbs <= ∑ i in s, (f i).natAbs := by
  induction s using Finset.cons_induction with grind

@[deprecated (since := "2026-02-14")]
alias nat_abs_sum_le := Int.natAbs_sum_le
