/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Order.Filter.Extr

/-!
# Lemmas about the `sup` and `inf` of the support of `AddMonoidAlgebra`

## TODO
The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/

@[expose] public section


variable {R R' A T B ι : Type*}

namespace AddMonoidAlgebra

/-!

## sup-degree and inf-degree of an `AddMonoidAlgebra`

Let `R` be a semiring and let `A` be a `SemilatticeSup`.
For an element `f : R[A]`, this file defines
* `AddMonoidAlgebra.supDegree`: the sup-degree taking values in `WithBot A`,
* `AddMonoidAlgebra.infDegree`: the inf-degree taking values in `WithTop A`.

If the grading type `A` is a linearly ordered additive monoid, then these two notions of degree
coincide with the standard one:
* the sup-degree is the maximum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊥`, if `f = 0`;
* the inf-degree is the minimum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊤`, if `f = 0`.

The main results are
* `AddMonoidAlgebra.supDegree_mul_le`:
  the sup-degree of a product is at most the sum of the sup-degrees,
* `AddMonoidAlgebra.le_infDegree_mul`:
  the inf-degree of a product is at least the sum of the inf-degrees,
* `AddMonoidAlgebra.supDegree_add_le`:
  the sup-degree of a sum is at most the sup of the sup-degrees,
* `AddMonoidAlgebra.le_infDegree_add`:
  the inf-degree of a sum is at least the inf of the inf-degrees.

### Implementation notes

The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.
Next, the general lemmas get specialized twice:
* once for `supDegree` (essentially a simple application) and
* once for `infDegree` (a simple application, via `OrderDual`).

These final lemmas are the ones that likely get used the most. The generic lemmas about
`Finset.support.sup` may not be used directly much outside of this file.
To see this in action, you can look at the triple
`(sup_support_mul_le, maxDegree_mul_le, le_minDegree_mul)`.
-/


section GeneralResultsAssumingSemilatticeSup

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

section Semiring

variable [Semiring R]

section ExplicitDegrees

/-!

In this section, we use `degb` and `degt` to denote "degree functions" on `A` with values in
a type with *b*ot or *t*op respectively.
-/


variable (degb : A -> B) (degt : A -> T) (f g : R[A])

/--
theorem `sup_support_coeff_add_le` / 定理 `sup_support_coeff_add_le`

English:
theorem sup_support_coeff_add_le
  proof: by
  classical
  exact (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

@[deprecated (since := "2026-06-18")] alias sup_support_add_le := sup_support_coeff_add_le

中文:
定理 sup_support_coeff_add_le
  证明: by
  classical
  exact (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

@[deprecated (since := "2026-06-18")] alias sup_support_add_le := sup_support_coeff_add_le

Depends on / 依赖: Finset, Finset.sup_mono, Finset.sup_union, Finsupp, Finsupp.support_add, classical, sup_mono, sup_union, support_add, trans_eq
-/
theorem sup_support_coeff_add_le :
    (f + g).coeff.support.sup degb <= f.coeff.support.sup degb ⊔ g.coeff.support.sup degb := by
  classical
  exact (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

@[deprecated (since := "2026-06-18")] alias sup_support_add_le := sup_support_coeff_add_le

/--
theorem `le_inf_support_coeff_add` / 定理 `le_inf_support_coeff_add`

English:
theorem le_inf_support_coeff_add
  proof: sup_support_coeff_add_le (fun a : A => OrderDual.toDual (degt a)) f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_add := le_inf_support_coeff_add

中文:
定理 le_inf_support_coeff_add
  证明: sup_support_coeff_add_le (fun a : A => OrderDual.toDual (degt a)) f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_add := le_inf_support_coeff_add

Depends on / 依赖: OrderDual, OrderDual.toDual, sup_support_coeff_add_le, toDual
-/
theorem le_inf_support_coeff_add :
    f.coeff.support.inf degt ⊓ g.coeff.support.inf degt <= (f + g).coeff.support.inf degt :=
  sup_support_coeff_add_le (fun a : A => OrderDual.toDual (degt a)) f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_add := le_inf_support_coeff_add

end ExplicitDegrees

section AddOnly

variable [Add A] [Add B] [Add T] [AddLeftMono B] [AddRightMono B]
  [AddLeftMono T] [AddRightMono T]

/--
theorem `sup_support_coeff_mul_le` / 定理 `sup_support_coeff_mul_le`

English:
theorem sup_support_coeff_mul_le
  statement: {degb : A -> B} (degbm : forall a b, degb (a + b) <= degb a + degb b)
  proof: by
  classical
  grw [support_coeff_mul_subset, Finset.sup_add_le]
  rintro _fd fds _gd gds
  grw [degbm, ← Finset.le_sup fds, ← Finset.le_sup gds]

@[deprecated (since := "2026-06-18")] alias sup_support_mul_le := sup_support_coeff_mul_le

中文:
定理 sup_support_coeff_mul_le
  结论: {degb : A -> B} (degbm : 对任意 a b, degb (a + b) <= degb a + degb b)
  证明: by
  classical
  grw [support_coeff_mul_subset, Finset.sup_add_le]
  rintro _fd fds _gd gds
  grw [degbm, ← Finset.le_sup fds, ← Finset.le_sup gds]

@[deprecated (since := "2026-06-18")] alias sup_support_mul_le := sup_support_coeff_mul_le

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_add_le, classical, le_sup, sup_add_le, support_coeff_mul_subset
-/
theorem sup_support_coeff_mul_le {degb : A -> B} (degbm : forall a b, degb (a + b) <= degb a + degb b)
    (f g : R[A]) :
    (f * g).coeff.support.sup degb <= f.coeff.support.sup degb + g.coeff.support.sup degb := by
  classical
  grw [support_coeff_mul_subset, Finset.sup_add_le]
  rintro _fd fds _gd gds
  grw [degbm, ← Finset.le_sup fds, ← Finset.le_sup gds]

@[deprecated (since := "2026-06-18")] alias sup_support_mul_le := sup_support_coeff_mul_le

/--
theorem `le_inf_support_coeff_mul` / 定理 `le_inf_support_coeff_mul`

English:
theorem le_inf_support_coeff_mul
  statement: {degt : A -> T} (degtm : forall a b, degt a + degt b <= degt (a + b))
  proof: sup_support_coeff_mul_le (B := Tᵒᵈ) degtm f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_mul := le_inf_support_coeff_mul

中文:
定理 le_inf_support_coeff_mul
  结论: {degt : A -> T} (degtm : 对任意 a b, degt a + degt b <= degt (a + b))
  证明: sup_support_coeff_mul_le (B := Tᵒᵈ) degtm f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_mul := le_inf_support_coeff_mul

Depends on / 依赖: sup_support_coeff_mul_le
-/
theorem le_inf_support_coeff_mul {degt : A -> T} (degtm : forall a b, degt a + degt b <= degt (a + b))
    (f g : R[A]) :
    f.coeff.support.inf degt + g.coeff.support.inf degt <= (f * g).coeff.support.inf degt :=
  sup_support_coeff_mul_le (B := Tᵒᵈ) degtm f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_mul := le_inf_support_coeff_mul

end AddOnly

section AddMonoids

variable [AddMonoid A] [AddMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A -> B} {degt : A -> T}

/--
theorem `sup_support_list_prod_le` / 定理 `sup_support_list_prod_le`

English:
theorem sup_support_list_prod_le
  statement: (degb0 : degb 0 <= 0)

中文:
定理 sup_support_list_prod_le
  结论: (degb0 : degb 0 <= 0)
-/
theorem sup_support_list_prod_le (degb0 : degb 0 <= 0)
    (degbm : forall a b, degb (a + b) <= degb a + degb b) :
    forall l : List R[A],
      l.prod.coeff.support.sup degb <= (l.map fun f : R[A] => f.coeff.support.sup degb).sum
  | [] => by
    rw [List.map_nil]; rw [Finset.sup_le_iff]; rw [List.prod_nil]; rw [List.sum_nil]
    exact fun a ha => by rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
  | f::fs => by
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.sum_cons]
    grw [sup_support_coeff_mul_le degbm, sup_support_list_prod_le degb0 degbm]

/--
theorem `le_inf_support_list_prod` / 定理 `le_inf_support_list_prod`

English:
theorem le_inf_support_list_prod
  statement: (degt0 : 0 <= degt 0)
  proof: by
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b

中文:
定理 le_inf_support_list_prod
  结论: (degt0 : 0 <= degt 0)
  证明: by
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b

Depends on / 依赖: OrderDual, OrderDual.ofDual_le_ofDual.mp, OrderDual.ofDual_le_ofDual.mpr, ofDual_le_ofDual, sup_support_list_prod_le
-/
theorem le_inf_support_list_prod (degt0 : 0 <= degt 0)
    (degtm : forall a b, degt a + degt b <= degt (a + b)) (l : List R[A]) :
    (l.map fun f : R[A] => f.coeff.support.inf degt).sum <= l.prod.coeff.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b

/--
theorem `sup_support_pow_le` / 定理 `sup_support_pow_le`

English:
theorem sup_support_pow_le
  statement: (degb0 : degb 0 <= 0) (degbm : forall a b, degb (a + b) <= degb a + degb b)
  proof: by
  rw [← List.prod_replicate]; rw [← List.sum_replicate]
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq ?_
  rw [List.map_replicate]

中文:
定理 sup_support_pow_le
  结论: (degb0 : degb 0 <= 0) (degbm : 对任意 a b, degb (a + b) <= degb a + degb b)
  证明: by
  rw [← List.prod_replicate]; rw [← List.sum_replicate]
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq ?_
  rw [List.map_replicate]

Depends on / 依赖: List.map_replicate, List.prod_replicate, List.sum_replicate, map_replicate, prod_replicate, sum_replicate, sup_support_list_prod_le, trans_eq
-/
theorem sup_support_pow_le (degb0 : degb 0 <= 0) (degbm : forall a b, degb (a + b) <= degb a + degb b)
    (n : Nat) (f : R[A]) : (f ^ n).coeff.support.sup degb <= n • f.coeff.support.sup degb := by
  rw [← List.prod_replicate]; rw [← List.sum_replicate]
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq ?_
  rw [List.map_replicate]

/--
theorem `le_inf_support_pow` / 定理 `le_inf_support_pow`

English:
theorem le_inf_support_pow
  statement: (degt0 : 0 <= degt 0) (degtm : forall a b, degt a + degt b <= degt (a + b))
  proof: by
refine OrderDual.ofDual_le_ofDual.mpr sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
  · exact degt0
  · exact degtm _ _

中文:
定理 le_inf_support_pow
  结论: (degt0 : 0 <= degt 0) (degtm : 对任意 a b, degt a + degt b <= degt (a + b))
  证明: by
refine OrderDual.ofDual_le_ofDual.mpr sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
  · exact degt0
  · exact degtm _ _

Depends on / 依赖: OrderDual, OrderDual.ofDual_le_ofDual.mp, OrderDual.ofDual_le_ofDual.mpr, ofDual_le_ofDual, sup_support_pow_le
-/
theorem le_inf_support_pow (degt0 : 0 <= degt 0) (degtm : forall a b, degt a + degt b <= degt (a + b))
    (n : Nat) (f : R[A]) : n • f.coeff.support.inf degt <= (f ^ n).coeff.support.inf degt := by
refine OrderDual.ofDual_le_ofDual.mpr sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
  · exact degt0
  · exact degtm _ _

end AddMonoids

end Semiring

section CommutativeLemmas

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddCommMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A -> B} {degt : A -> T}

/--
theorem `sup_support_coeff_multisetProd_le` / 定理 `sup_support_coeff_multisetProd_le`

English:
theorem sup_support_coeff_multisetProd_le
  statement: (degb0 : degb 0 <= 0)
  proof: by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'']; rw [Multiset.map_coe]; rw [Multiset.sum_coe]; rw [Multiset.prod_coe]
  exact sup_support_list_prod_le degb0 degbm _

@[deprecated (since := "2026-06-18")]
alias sup_support_multiset_prod_le := sup_support_coeff_multisetProd_le

中文:
定理 sup_support_coeff_multisetProd_le
  结论: (degb0 : degb 0 <= 0)
  证明: by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'']; rw [Multiset.map_coe]; rw [Multiset.sum_coe]; rw [Multiset.prod_coe]
  exact sup_support_list_prod_le degb0 degbm _

@[deprecated (since := "2026-06-18")]
alias sup_support_multiset_prod_le := sup_support_coeff_multisetProd_le

Depends on / 依赖: Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, Multiset.sum_coe, Quot.inductionOn, inductionOn, map_coe, prod_coe, quot_mk_to_coe, sum_coe, sup_support_list_prod_le
-/
theorem sup_support_coeff_multisetProd_le (degb0 : degb 0 <= 0)
    (degbm : forall a b, degb (a + b) <= degb a + degb b) (m : Multiset R[A]) :
    m.prod.coeff.support.sup degb <= (m.map fun f : R[A] => f.coeff.support.sup degb).sum := by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'']; rw [Multiset.map_coe]; rw [Multiset.sum_coe]; rw [Multiset.prod_coe]
  exact sup_support_list_prod_le degb0 degbm _

@[deprecated (since := "2026-06-18")]
alias sup_support_multiset_prod_le := sup_support_coeff_multisetProd_le

/--
theorem `le_inf_support_coeff_multisetProd` / 定理 `le_inf_support_coeff_multisetProd`

English:
theorem le_inf_support_coeff_multisetProd
  statement: (degt0 : 0 <= degt 0)
  proof: by
refine OrderDual.ofDual_le_ofDual.mpr
    sup_support_coeff_multisetProd_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _

@[deprecated (since := "2026-06-18")]
alias le_inf_support_multiset_prod := le_inf_support_coef

中文:
定理 le_inf_support_coeff_multisetProd
  结论: (degt0 : 0 <= degt 0)
  证明: by
refine OrderDual.ofDual_le_ofDual.mpr
    sup_support_coeff_multisetProd_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _

@[deprecated (since := "2026-06-18")]
alias le_inf_support_multiset_prod := le_inf_support_coef

Depends on / 依赖: OrderDual, OrderDual.ofDual_le_ofDual.mp, OrderDual.ofDual_le_ofDual.mpr, ofDual_le_ofDual, sup_support_coeff_multisetProd_le
-/
theorem le_inf_support_coeff_multisetProd (degt0 : 0 <= degt 0)
    (degtm : forall a b, degt a + degt b <= degt (a + b)) (m : Multiset R[A]) :
    (m.map fun f : R[A] => f.coeff.support.inf degt).sum <= m.prod.coeff.support.inf degt := by
refine OrderDual.ofDual_le_ofDual.mpr
    sup_support_coeff_multisetProd_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _

@[deprecated (since := "2026-06-18")]
alias le_inf_support_multiset_prod := le_inf_support_coeff_multisetProd

/--
theorem `sup_support_coeff_finsetProd_le` / 定理 `sup_support_coeff_finsetProd_le`

English:
theorem sup_support_coeff_finsetProd_le
  statement: (degb0 : degb 0 <= 0)
  proof: (sup_support_coeff_multisetProd_le degb0 degbm _).trans_eq congr_arg _ Multiset.map_map ..

@[deprecated (since := "2026-06-18")]
alias sup_support_finsetProd_le := sup_support_coeff_finsetProd_le

@[deprecated (since := "2026-04-08")]
alias sup_support_finset_prod_le := sup_support_coeff_finsetProd

中文:
定理 sup_support_coeff_finsetProd_le
  结论: (degb0 : degb 0 <= 0)
  证明: (sup_support_coeff_multisetProd_le degb0 degbm _).trans_eq congr_arg _ Multiset.map_map ..

@[deprecated (since := "2026-06-18")]
alias sup_support_finsetProd_le := sup_support_coeff_finsetProd_le

@[deprecated (since := "2026-04-08")]
alias sup_support_finset_prod_le := sup_support_coeff_finsetProd

Depends on / 依赖: Multiset, Multiset.map_map, congr_arg, map_map, sup_support_coeff_multisetProd_le, trans_eq
-/
theorem sup_support_coeff_finsetProd_le (degb0 : degb 0 <= 0)
    (degbm : forall a b, degb (a + b) <= degb a + degb b) (s : Finset ι) (f : ι -> R[A]) :
    (∏ i in s, f i).coeff.support.sup degb <= ∑ i in s, (f i).coeff.support.sup degb :=
(sup_support_coeff_multisetProd_le degb0 degbm _).trans_eq congr_arg _ Multiset.map_map ..

@[deprecated (since := "2026-06-18")]
alias sup_support_finsetProd_le := sup_support_coeff_finsetProd_le

@[deprecated (since := "2026-04-08")]
alias sup_support_finset_prod_le := sup_support_coeff_finsetProd_le

/--
theorem `le_inf_support_coeff_finsetProd` / 定理 `le_inf_support_coeff_finsetProd`

English:
theorem le_inf_support_coeff_finsetProd
  statement: (degt0 : 0 <= degt 0)
  proof: le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_coeff_multisetProd degt0 degtm _)

@[deprecated (since := "2026-06-18")]
alias le_inf_support_finsetProd := le_inf_support_coeff_finsetProd

@[deprecated (since := "2026-04-08")]
alias le_inf_support_finset_prod := le_inf_support_coeff_f

中文:
定理 le_inf_support_coeff_finsetProd
  结论: (degt0 : 0 <= degt 0)
  证明: le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_coeff_multisetProd degt0 degtm _)

@[deprecated (since := "2026-06-18")]
alias le_inf_support_finsetProd := le_inf_support_coeff_finsetProd

@[deprecated (since := "2026-04-08")]
alias le_inf_support_finset_prod := le_inf_support_coeff_f

Depends on / 依赖: Multiset, Multiset.map_map, le_inf_support_coeff_multisetProd, le_of_eq_of_le, map_map
-/
theorem le_inf_support_coeff_finsetProd (degt0 : 0 <= degt 0)
    (degtm : forall a b, degt a + degt b <= degt (a + b)) (s : Finset ι) (f : ι -> R[A]) :
    (∑ i in s, (f i).coeff.support.inf degt) <= (∏ i in s, f i).coeff.support.inf degt :=
  le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_coeff_multisetProd degt0 degtm _)

@[deprecated (since := "2026-06-18")]
alias le_inf_support_finsetProd := le_inf_support_coeff_finsetProd

@[deprecated (since := "2026-04-08")]
alias le_inf_support_finset_prod := le_inf_support_coeff_finsetProd

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup


/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/


section Degrees

variable [Semiring R] [Ring R']

section SupDegree

variable [SemilatticeSup B] [OrderBot B] (D : A -> B)

/--
Definition of `supDegree` / `supDegree` 的定义

English:
abbreviation supDegree
  signature: (f : R[A])
  body: f.coeff.support.sup D

中文:
缩写 supDegree
  签名: (f : R[A])
  定义体: f.coeff.support.sup D

Depends on / 依赖: f.coeff.support.sup, support
-/
abbrev supDegree (f : R[A]) : B :=
  f.coeff.support.sup D

variable {D}

/--
theorem `supDegree_add_le` / 定理 `supDegree_add_le`

English:
theorem supDegree_add_le
  given: {f g : R[A]}
  proof: sup_support_coeff_add_le D f g

@[simp]

中文:
定理 supDegree_add_le
  条件: {f g : R[A]}
  证明: sup_support_coeff_add_le D f g

@[simp]

Depends on / 依赖: sup_support_coeff_add_le
-/
theorem supDegree_add_le {f g : R[A]} :
    (f + g).supDegree D <= (f.supDegree D) ⊔ (g.supDegree D) :=
  sup_support_coeff_add_le D f g

@[simp]
/--
theorem `supDegree_neg` / 定理 `supDegree_neg`

English:
theorem supDegree_neg
  given: {f : R'[A]}
  statement: (-f).supDegree D = f.supDegree D
  proof: by simp [supDegree]

中文:
定理 supDegree_neg
  条件: {f : R'[A]}
  结论: (-f).supDegree D = f.supDegree D
  证明: by simp [supDegree]

Depends on / 依赖: supDegree
-/
theorem supDegree_neg {f : R'[A]} : (-f).supDegree D = f.supDegree D := by simp [supDegree]

/--
theorem `supDegree_sub_le` / 定理 `supDegree_sub_le`

English:
theorem supDegree_sub_le
  given: {f g : R'[A]}
  proof: by
  rw [sub_eq_add_neg]; rw [← supDegree_neg (f := g)]; apply supDegree_add_le

中文:
定理 supDegree_sub_le
  条件: {f g : R'[A]}
  证明: by
  rw [sub_eq_add_neg]; rw [← supDegree_neg (f := g)]; apply supDegree_add_le

Depends on / 依赖: sub_eq_add_neg, supDegree_add_le, supDegree_neg
-/
theorem supDegree_sub_le {f g : R'[A]} :
    (f - g).supDegree D <= f.supDegree D ⊔ g.supDegree D := by
  rw [sub_eq_add_neg]; rw [← supDegree_neg (f := g)]; apply supDegree_add_le

/--
theorem `supDegree_sum_le` / 定理 `supDegree_sum_le`

English:
theorem supDegree_sum_le
  given: {ι} {s : Finset ι} {f : ι -> R[A]}
  proof: by
  classical
  simp only [supDegree, coeff_sum]
  grw [Finsupp.support_finsetSum, Finset.sup_biUnion]

中文:
定理 supDegree_sum_le
  条件: {ι} {s : Finset ι} {f : ι -> R[A]}
  证明: by
  classical
  simp only [supDegree, coeff_sum]
  grw [Finsupp.support_finsetSum, Finset.sup_biUnion]

Depends on / 依赖: Finset, Finset.sup_biUnion, Finsupp, Finsupp.support_finsetSum, classical, coeff_sum, supDegree, sup_biUnion, support_finsetSum
-/
theorem supDegree_sum_le {ι} {s : Finset ι} {f : ι -> R[A]} :
    (∑ i in s, f i).supDegree D <= s.sup (fun i => (f i).supDegree D) := by
  classical
  simp only [supDegree, coeff_sum]
  grw [Finsupp.support_finsetSum, Finset.sup_biUnion]

/--
theorem `supDegree_single_ne_zero` / 定理 `supDegree_single_ne_zero`

English:
theorem supDegree_single_ne_zero
  given: (a : A) {r : R} (hr : r != 0)
  proof: by
  simp [supDegree, hr]

中文:
定理 supDegree_single_ne_zero
  条件: (a : A) {r : R} (hr : r != 0)
  证明: by
  simp [supDegree, hr]

Depends on / 依赖: supDegree
-/
theorem supDegree_single_ne_zero (a : A) {r : R} (hr : r != 0) :
    (single a r).supDegree D = D a := by
  simp [supDegree, hr]

open scoped Classical in
/--
theorem `supDegree_single` / 定理 `supDegree_single`

English:
theorem supDegree_single
  given: (a : A) (r : R)
  proof: by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]

中文:
定理 supDegree_single
  条件: (a : A) (r : R)
  证明: by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]

Depends on / 依赖: split_ifs, supDegree_single_ne_zero
-/
theorem supDegree_single (a : A) (r : R) :
    (single a r).supDegree D = if r = 0 then ⊥ else D a := by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]

/--
theorem `coeff_eq_zero_of_not_le_supDegree` / 定理 `coeff_eq_zero_of_not_le_supDegree`

English:
theorem coeff_eq_zero_of_not_le_supDegree
  given: {p : R[A]} {a : A} (hlt : ¬ D a <= p.supDegree D)
  proof: by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

@[deprecated (since := "2026-06-18")]
alias apply_eq_zero_of_not_le_supDegree := coeff_eq_zero_of_not_le_supDegree

中文:
定理 coeff_eq_zero_of_not_le_supDegree
  条件: {p : R[A]} {a : A} (hlt : ¬ D a <= p.supDegree D)
  证明: by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

@[deprecated (since := "2026-06-18")]
alias apply_eq_zero_of_not_le_supDegree := coeff_eq_zero_of_not_le_supDegree

Depends on / 依赖: Finset, Finset.le_sup, Finsupp, Finsupp.mem_support_iff, contrapose, le_sup, mem_support_iff
-/
theorem coeff_eq_zero_of_not_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a <= p.supDegree D) :
    p.coeff a = 0 := by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

@[deprecated (since := "2026-06-18")]
alias apply_eq_zero_of_not_le_supDegree := coeff_eq_zero_of_not_le_supDegree

/--
theorem `supDegree_withBot_some_comp` / 定理 `supDegree_withBot_some_comp`

English:
theorem supDegree_withBot_some_comp
  given: {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty)
  proof: by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs]; rw [Finset.sup'_eq_sup]

中文:
定理 supDegree_withBot_some_comp
  条件: {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty)
  证明: by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs]; rw [Finset.sup'_eq_sup]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supDegree, Finset, Finset.coe_sup, Finset.sup, _eq_sup, coe_sup, supDegree
-/
theorem supDegree_withBot_some_comp {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty) :
    supDegree (WithBot.some ∘ D) s = supDegree D s := by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs]; rw [Finset.sup'_eq_sup]

/--
theorem `supDegree_eq_of_isMaxOn` / 定理 `supDegree_eq_of_isMaxOn`

English:
theorem supDegree_eq_of_isMaxOn
  statement: {p : R[A]} {a : A} (hmem : a in p.coeff.support)
  proof: sup_eq_of_isMaxOn hmem hmax

中文:
定理 supDegree_eq_of_isMaxOn
  结论: {p : R[A]} {a : A} (hmem : a in p.coeff.support)
  证明: sup_eq_of_isMaxOn hmem hmax

Depends on / 依赖: sup_eq_of_isMaxOn
-/
theorem supDegree_eq_of_isMaxOn {p : R[A]} {a : A} (hmem : a in p.coeff.support)
    (hmax : IsMaxOn D p.coeff.support a) : p.supDegree D = D a :=
  sup_eq_of_isMaxOn hmem hmax

variable {p q : R[A]}

@[simp]
/--
theorem `supDegree_zero` / 定理 `supDegree_zero`

English:
theorem supDegree_zero
  statement: (0 : R[A]).supDegree D = ⊥
  proof: by simp [supDegree]

中文:
定理 supDegree_zero
  结论: (0 : R[A]).supDegree D = ⊥
  证明: by simp [supDegree]

Depends on / 依赖: supDegree
-/
theorem supDegree_zero : (0 : R[A]).supDegree D = ⊥ := by simp [supDegree]

/--
theorem `ne_zero_of_supDegree_ne_bot` / 定理 `ne_zero_of_supDegree_ne_bot`

English:
theorem ne_zero_of_supDegree_ne_bot
  statement: p.supDegree D != ⊥ -> p != 0
  proof: mt (fun h => h ▸ supDegree_zero)

中文:
定理 ne_zero_of_supDegree_ne_bot
  结论: p.supDegree D != ⊥ -> p != 0
  证明: mt (fun h => h ▸ supDegree_zero)

Depends on / 依赖: supDegree_zero
-/
theorem ne_zero_of_supDegree_ne_bot : p.supDegree D != ⊥ -> p != 0 := mt (fun h => h ▸ supDegree_zero)

/--
theorem `ne_zero_of_not_supDegree_le` / 定理 `ne_zero_of_not_supDegree_le`

English:
theorem ne_zero_of_not_supDegree_le
  given: {b : B} (h : ¬ p.supDegree D <= b)
  statement: p != 0
  proof: ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

中文:
定理 ne_zero_of_not_supDegree_le
  条件: {b : B} (h : ¬ p.supDegree D <= b)
  结论: p != 0
  证明: ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

Depends on / 依赖: bot_le, ne_zero_of_supDegree_ne_bot
-/
theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D <= b) : p != 0 :=
  ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

variable [AddZeroClass A]

/--
theorem `supDegree_eq_of_max` / 定理 `supDegree_eq_of_max`

English:
theorem supDegree_eq_of_max
  statement: {b : B} (hb : b in Set.range D) (hmem : D.invFun b in p.coeff.support)
  proof: sup_eq_of_max hb hmem hmax

中文:
定理 supDegree_eq_of_max
  结论: {b : B} (hb : b in Set.range D) (hmem : D.invFun b in p.coeff.support)
  证明: sup_eq_of_max hb hmem hmax

Depends on / 依赖: sup_eq_of_max
-/
theorem supDegree_eq_of_max {b : B} (hb : b in Set.range D) (hmem : D.invFun b in p.coeff.support)
    (hmax : forall a in p.coeff.support, D a <= b) : p.supDegree D = b :=
  sup_eq_of_max hb hmem hmax

variable [Add B]

/--
theorem `supDegree_mul_le` / 定理 `supDegree_mul_le`

English:
theorem supDegree_mul_le
  statement: (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
  proof: sup_support_coeff_mul_le (fun {_ _} => (hadd _ _).le) p q

中文:
定理 supDegree_mul_le
  结论: (hadd : 对任意 a1 a2, D (a1 + a2) = D a1 + D a2)
  证明: sup_support_coeff_mul_le (fun {_ _} => (hadd _ _).le) p q

Depends on / 依赖: sup_support_coeff_mul_le
-/
theorem supDegree_mul_le (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftMono B] [AddRightMono B] :
    (p * q).supDegree D <= p.supDegree D + q.supDegree D :=
  sup_support_coeff_mul_le (fun {_ _} => (hadd _ _).le) p q

/--
theorem `supDegree_prod_le` / 定理 `supDegree_prod_le`

English:
theorem supDegree_prod_le
  statement: {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  proof: by
  classical
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his]; rw [Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (by gcongr)

中文:
定理 supDegree_prod_le
  结论: {R A B : 类型} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  证明: by
  classical
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his]; rw [Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (by gcongr)

Depends on / 依赖: Finset, Finset.prod_empty, Finset.prod_insert, Finset.sum_empty, Finset.sum_insert, bot_le, classical, exacts, hzero.le, one_def, prod_empty, prod_insert, s.induction, split_ifs, sum_empty, sum_insert, supDegree_mul_le, supDegree_single
-/
theorem supDegree_prod_le {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
    [SemilatticeSup B] [OrderBot B]
    [AddLeftMono B] [AddRightMono B]
    {D : A -> B} (hzero : D 0 = 0) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι -> R[A]} :
    (∏ i in s, f i).supDegree D <= ∑ i in s, (f i).supDegree D := by
  classical
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his]; rw [Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (by gcongr)

/--
theorem `coeff_add_of_supDegree_le` / 定理 `coeff_add_of_supDegree_le`

English:
theorem coeff_add_of_supDegree_le
  statement: (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
  proof: by
  classical
  simp_rw [coeff_mul, Finsupp.sum]
  rw [Finset.sum_eq_single ap]; rw [Finset.sum_eq_single aq]; rw [if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_right (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_if

中文:
定理 coeff_add_of_supDegree_le
  结论: (hadd : 对任意 a1 a2, D (a1 + a2) = D a1 + D a2)
  证明: by
  classical
  simp_rw [coeff_mul, Finsupp.sum]
  rw [Finset.sum_eq_single ap]; rw [Finset.sum_eq_single aq]; rw [if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_right (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_if

Depends on / 依赖: Finset, Finset.le_sup, Finset.sum_eq_single, Finset.sum_eq_zero, Finsupp, Finsupp.notMem_support_iff, Finsupp.sum, add_lt_add_right, apply_fun, classical, coeff_mul, hD.ne_iff, if_neg, if_pos, le_sup, lt_of_ne, mul_zero, ne_iff, notMem_support_iff, simp_rw
-/
theorem coeff_add_of_supDegree_le (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (hD : D.Injective) {ap aq : A} (hp : p.supDegree D <= D ap) (hq : q.supDegree D <= D aq) :
    (p * q).coeff (ap + aq) = p.coeff ap * q.coeff aq := by
  classical
  simp_rw [coeff_mul, Finsupp.sum]
  rw [Finset.sum_eq_single ap]; rw [Finset.sum_eq_single aq]; rw [if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_right (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_iff.2 hne) _).ne he
  · intro h; rw [if_pos rfl, Finsupp.notMem_support_iff.1 h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun a' ha' => if_neg <| fun he => ?_)
    apply_fun D at he
    simp_rw [hadd] at he
    have := addLeftMono_of_addLeftStrictMono B
    exact (add_lt_add_of_lt_of_le (((Finset.le_sup ha).trans hp).lt_of_ne <| hD.ne_iff.2 hne)
 (Finset.le_sup ha').trans hq).ne he
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr <| fun _ => ?_)
    rw [Finsupp.notMem_support_iff.mp h]; rw [zero_mul]

@[deprecated (since := "2026-06-18")] alias apply_add_of_supDegree_le := coeff_add_of_supDegree_le

end SupDegree

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A -> B)

/--
Definition of `leadingCoeff` / `leadingCoeff` 的定义

English:
definition leadingCoeff
  signature: [Nonempty A] (f : R[A])
  body: f.coeff D.invFun f.supDegree D

中文:
定义 leadingCoeff
  签名: [Nonempty A] (f : R[A])
  定义体: f.coeff D.invFun f.supDegree D

Depends on / 依赖: D.invFun, f.coeff, f.supDegree, invFun, supDegree
-/
noncomputable def leadingCoeff [Nonempty A] (f : R[A]) : R := f.coeff D.invFun f.supDegree D

/--
Definition of `Monic` / `Monic` 的定义

English:
definition Monic
  signature: [Nonempty A] (f : R[A])
  body: f.leadingCoeff D = 1

中文:
定义 Monic
  签名: [Nonempty A] (f : R[A])
  定义体: f.leadingCoeff D = 1
-/
@[reducible] def Monic [Nonempty A] (f : R[A]) : Prop :=
  f.leadingCoeff D = 1

variable {D}

@[simp]
/--
theorem `leadingCoeff_single` / 定理 `leadingCoeff_single`

English:
theorem leadingCoeff_single
  given: [Nonempty A] (hD : D.Injective) (a : A) (r : R)
  proof: by
  rw [leadingCoeff]; rw [supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD]
    simp

@[simp]

中文:
定理 leadingCoeff_single
  条件: [Nonempty A] (hD : D.Injective) (a : A) (r : R)
  证明: by
  rw [leadingCoeff]; rw [supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD]
    simp

@[simp]

Depends on / 依赖: Function, Function.leftInverse_invFun, leadingCoeff, leftInverse_invFun, split_ifs, supDegree_single
-/
theorem leadingCoeff_single [Nonempty A] (hD : D.Injective) (a : A) (r : R) :
    (single a r).leadingCoeff D = r := by
  rw [leadingCoeff]; rw [supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD]
    simp

@[simp]
/--
theorem `leadingCoeff_zero` / 定理 `leadingCoeff_zero`

English:
theorem leadingCoeff_zero
  given: [Nonempty A]
  statement: (0 : R[A]).leadingCoeff D = 0
  proof: rfl

中文:
定理 leadingCoeff_zero
  条件: [Nonempty A]
  结论: (0 : R[A]).leadingCoeff D = 0
  证明: rfl
-/
theorem leadingCoeff_zero [Nonempty A] : (0 : R[A]).leadingCoeff D = 0 := rfl

/--
lemma `Monic.ne_zero` / 引理 `Monic.ne_zero`

English:
lemma Monic.ne_zero
  given: [Nonempty A] [Nontrivial R] (hp : p.Monic D)
  statement: p != 0
  proof: fun h => by
  simp_rw [Monic, h, leadingCoeff_zero, zero_ne_one] at hp

@[simp]

中文:
引理 Monic.ne_zero
  条件: [Nonempty A] [Nontrivial R] (hp : p.Monic D)
  结论: p != 0
  证明: fun h => by
  simp_rw [Monic, h, leadingCoeff_zero, zero_ne_one] at hp

@[simp]

Depends on / 依赖: leadingCoeff_zero, simp_rw, zero_ne_one
-/
lemma Monic.ne_zero [Nonempty A] [Nontrivial R] (hp : p.Monic D) : p != 0 := fun h => by
  simp_rw [Monic, h, leadingCoeff_zero, zero_ne_one] at hp

@[simp]
/--
theorem `monic_one` / 定理 `monic_one`

English:
theorem monic_one
  given: [AddZeroClass A] (hD : D.Injective)
  statement: (1 : R[A]).Monic D
  proof: by
  rw [Monic]; rw [one_def]; rw [leadingCoeff_single hD]

中文:
定理 monic_one
  条件: [AddZeroClass A] (hD : D.Injective)
  结论: (1 : R[A]).Monic D
  证明: by
  rw [Monic]; rw [one_def]; rw [leadingCoeff_single hD]

Depends on / 依赖: leadingCoeff_single, one_def
-/
theorem monic_one [AddZeroClass A] (hD : D.Injective) : (1 : R[A]).Monic D := by
  rw [Monic]; rw [one_def]; rw [leadingCoeff_single hD]

variable (D) in
/--
lemma `exists_supDegree_mem_support` / 引理 `exists_supDegree_mem_support`

English:
lemma exists_supDegree_mem_support
  given: (hp : p != 0)
  statement: exists a in p.coeff.support, p.supDegree D = D a
  proof: Finset.exists_mem_eq_sup _ (by simpa [Finsupp.support_nonempty_iff]) D

中文:
引理 exists_supDegree_mem_support
  条件: (hp : p != 0)
  结论: 存在 a in p.coeff.support, p.supDegree D = D a
  证明: Finset.exists_mem_eq_sup _ (by simpa [Finsupp.support_nonempty_iff]) D

Depends on / 依赖: Finset, Finset.exists_mem_eq_sup, Finsupp, Finsupp.support_nonempty_iff, exists_mem_eq_sup, support_nonempty_iff
-/
lemma exists_supDegree_mem_support (hp : p != 0) : exists a in p.coeff.support, p.supDegree D = D a :=
  Finset.exists_mem_eq_sup _ (by simpa [Finsupp.support_nonempty_iff]) D

variable (D) in
/--
lemma `supDegree_mem_range` / 引理 `supDegree_mem_range`

English:
lemma supDegree_mem_range
  given: (hp : p != 0)
  statement: p.supDegree D in Set.range D
  proof: by
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

中文:
引理 supDegree_mem_range
  条件: (hp : p != 0)
  结论: p.supDegree D in Set.range D
  证明: by
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

Depends on / 依赖: exists_supDegree_mem_support, he.symm
-/
lemma supDegree_mem_range (hp : p != 0) : p.supDegree D in Set.range D := by
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i in s) {f : ι -> R[A]}

/--
lemma `supDegree_sum_lt` / 引理 `supDegree_sum_lt`

English:
lemma supDegree_sum_lt
  statement: (hs : s.Nonempty) {b : B}
  proof: by
  refine supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

中文:
引理 supDegree_sum_lt
  结论: (hs : s.Nonempty) {b : B}
  证明: by
  refine supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

Depends on / 依赖: Finset, Finset.sup_lt_iff, bot_le, bot_le.trans_lt, supDegree_sum_le, supDegree_sum_le.trans_lt, sup_lt_iff, trans_lt
-/
lemma supDegree_sum_lt (hs : s.Nonempty) {b : B}
    (h : forall i in s, (f i).supDegree D < b) : (∑ i in s, f i).supDegree D < b := by
  refine supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

variable [AddZeroClass A]

open Finsupp in
/--
lemma `supDegree_add_eq_left` / 引理 `supDegree_add_eq_left`

English:
lemma supDegree_add_eq_left
  given: (h : q.supDegree D < p.supDegree D)
  proof: by
  apply (supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [he] at h ⊢
  apply Finset.le_sup
  simpa [coeff_eq_zero_of_not_le_supDegree h.not_ge] using ha

中文:
引理 supDegree_add_eq_left
  条件: (h : q.supDegree D < p.supDegree D)
  证明: by
  apply (supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [he] at h ⊢
  apply Finset.le_sup
  simpa [coeff_eq_zero_of_not_le_supDegree h.not_ge] using ha

Depends on / 依赖: Finset, Finset.le_sup, antisymm, coeff_eq_zero_of_not_le_supDegree, exists_supDegree_mem_support, h.le, h.not_ge, le_rfl, le_sup, ne_zero_of_not_supDegree_le, not_ge, supDegree_add_le, supDegree_add_le.trans, sup_le
-/
lemma supDegree_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).supDegree D = p.supDegree D := by
  apply (supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [he] at h ⊢
  apply Finset.le_sup
  simpa [coeff_eq_zero_of_not_le_supDegree h.not_ge] using ha

/--
lemma `supDegree_add_eq_right` / 引理 `supDegree_add_eq_right`

English:
lemma supDegree_add_eq_right
  given: (h : p.supDegree D < q.supDegree D)
  proof: by
  rw [add_comm]; rw [supDegree_add_eq_left h]

中文:
引理 supDegree_add_eq_right
  条件: (h : p.supDegree D < q.supDegree D)
  证明: by
  rw [add_comm]; rw [supDegree_add_eq_left h]

Depends on / 依赖: add_comm, supDegree_add_eq_left
-/
lemma supDegree_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).supDegree D = q.supDegree D := by
  rw [add_comm]; rw [supDegree_add_eq_left h]

/--
lemma `leadingCoeff_add_eq_left` / 引理 `leadingCoeff_add_eq_left`

English:
lemma leadingCoeff_add_eq_left
  given: (h : q.supDegree D < p.supDegree D)
  proof: by
  obtain ⟨a, he⟩ := supDegree_mem_range D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [leadingCoeff]; rw [supDegree_add_eq_left h]; rw [coeff_add]; rw [Finsupp.add_apply]; rw [← leadingCoeff]; rw [coeff_eq_zero_of_not_le_supDegree (D := D)]; rw [add_zero]
  rw [← he]; rw [Function.apply_invFun_ap

中文:
引理 leadingCoeff_add_eq_left
  条件: (h : q.supDegree D < p.supDegree D)
  证明: by
  obtain ⟨a, he⟩ := supDegree_mem_range D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [leadingCoeff]; rw [supDegree_add_eq_left h]; rw [coeff_add]; rw [Finsupp.add_apply]; rw [← leadingCoeff]; rw [coeff_eq_zero_of_not_le_supDegree (D := D)]; rw [add_zero]
  rw [← he]; rw [Function.apply_invFun_ap

Depends on / 依赖: Finsupp, Finsupp.add_apply, Function, Function.apply_invFun_apply, add_apply, add_zero, apply_invFun_apply, coeff_add, coeff_eq_zero_of_not_le_supDegree, h.not_ge, leadingCoeff, ne_zero_of_not_supDegree_le, not_ge, supDegree_add_eq_left, supDegree_mem_range
-/
lemma leadingCoeff_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).leadingCoeff D = p.leadingCoeff D := by
  obtain ⟨a, he⟩ := supDegree_mem_range D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [leadingCoeff]; rw [supDegree_add_eq_left h]; rw [coeff_add]; rw [Finsupp.add_apply]; rw [← leadingCoeff]; rw [coeff_eq_zero_of_not_le_supDegree (D := D)]; rw [add_zero]
  rw [← he]; rw [Function.apply_invFun_apply (f := D)]; rw [he]; exact h.not_ge

/--
lemma `leadingCoeff_add_eq_right` / 引理 `leadingCoeff_add_eq_right`

English:
lemma leadingCoeff_add_eq_right
  given: (h : p.supDegree D < q.supDegree D)
  proof: by
  rw [add_comm]; rw [leadingCoeff_add_eq_left h]

中文:
引理 leadingCoeff_add_eq_right
  条件: (h : p.supDegree D < q.supDegree D)
  证明: by
  rw [add_comm]; rw [leadingCoeff_add_eq_left h]

Depends on / 依赖: add_comm, leadingCoeff_add_eq_left
-/
lemma leadingCoeff_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).leadingCoeff D = q.leadingCoeff D := by
  rw [add_comm]; rw [leadingCoeff_add_eq_left h]

/--
lemma `supDegree_mem_support` / 引理 `supDegree_mem_support`

English:
lemma supDegree_mem_support
  given: (hD : D.Injective) (hp : p != 0)
  proof: by
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D hp
  rwa [he, Function.leftInverse_invFun hD]

中文:
引理 supDegree_mem_support
  条件: (hD : D.Injective) (hp : p != 0)
  证明: by
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D hp
  rwa [he, Function.leftInverse_invFun hD]

Depends on / 依赖: Function, Function.leftInverse_invFun, exists_supDegree_mem_support, leftInverse_invFun
-/
lemma supDegree_mem_support (hD : D.Injective) (hp : p != 0) :
    D.invFun (p.supDegree D) in p.coeff.support := by
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D hp
  rwa [he, Function.leftInverse_invFun hD]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `leadingCoeff_eq_zero` / 引理 `leadingCoeff_eq_zero`

English:
lemma leadingCoeff_eq_zero
  given: (hD : D.Injective)
  statement: p.leadingCoeff D = 0 ↔ p = 0
  proof: by
  refine ⟨(fun h => ?_).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff]; rw [← Ne]; rw [← Finsupp.mem_support_iff]
  exact supDegree_mem_support hD h

中文:
引理 leadingCoeff_eq_zero
  条件: (hD : D.Injective)
  结论: p.leadingCoeff D = 0 ↔ p = 0
  证明: by
  refine ⟨(fun h => ?_).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff]; rw [← Ne]; rw [← Finsupp.mem_support_iff]
  exact supDegree_mem_support hD h

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, leadingCoeff, leadingCoeff_zero, mem_support_iff, supDegree_mem_support
-/
lemma leadingCoeff_eq_zero (hD : D.Injective) : p.leadingCoeff D = 0 ↔ p = 0 := by
  refine ⟨(fun h => ?_).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff]; rw [← Ne]; rw [← Finsupp.mem_support_iff]
  exact supDegree_mem_support hD h

/--
lemma `leadingCoeff_ne_zero` / 引理 `leadingCoeff_ne_zero`

English:
lemma leadingCoeff_ne_zero
  given: (hD : D.Injective)
  statement: p.leadingCoeff D != 0 ↔ p != 0
  proof: (leadingCoeff_eq_zero hD).ne

中文:
引理 leadingCoeff_ne_zero
  条件: (hD : D.Injective)
  结论: p.leadingCoeff D != 0 ↔ p != 0
  证明: (leadingCoeff_eq_zero hD).ne

Depends on / 依赖: leadingCoeff_eq_zero
-/
lemma leadingCoeff_ne_zero (hD : D.Injective) : p.leadingCoeff D != 0 ↔ p != 0 :=
  (leadingCoeff_eq_zero hD).ne

/--
lemma `supDegree_sub_lt_of_leadingCoeff_eq` / 引理 `supDegree_sub_lt_of_leadingCoeff_eq`

English:
lemma supDegree_sub_lt_of_leadingCoeff_eq
  statement: (hD : D.Injective) {R} [Ring R] {p q : R[A]}
  proof: by
  rw [or_iff_not_imp_right]
  refine fun he => (supDegree_sub_le.trans ?_).lt_of_ne ?_
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero hD, leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, coeff_sub, Finsupp.sub_apply, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]

中文:
引理 supDegree_sub_lt_of_leadingCoeff_eq
  结论: (hD : D.Injective) {R} [Ring R] {p q : R[A]}
  证明: by
  rw [or_iff_not_imp_right]
  refine fun he => (supDegree_sub_le.trans ?_).lt_of_ne ?_
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero hD, leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, coeff_sub, Finsupp.sub_apply, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]

Depends on / 依赖: Finsupp, Finsupp.sub_apply, coeff_sub, leadingCoeff, leadingCoeff_eq_zero, lt_of_ne, or_iff_not_imp_right, sub_apply, sub_eq_zero, supDegree_sub_le, supDegree_sub_le.trans, sup_idem
-/
lemma supDegree_sub_lt_of_leadingCoeff_eq (hD : D.Injective) {R} [Ring R] {p q : R[A]}
    (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCoeff D) :
    (p - q).supDegree D < p.supDegree D ∨ p = q := by
  rw [or_iff_not_imp_right]
  refine fun he => (supDegree_sub_le.trans ?_).lt_of_ne ?_
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero hD, leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, coeff_sub, Finsupp.sub_apply, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]

/--
lemma `supDegree_leadingCoeff_sum_eq` / 引理 `supDegree_leadingCoeff_sum_eq`

English:
lemma supDegree_leadingCoeff_sum_eq
  proof: by
  classical
  rw [← s.add_sum_erase _ hi]
  by_cases! hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨supDegree_add_eq_left this, leadingCoeff_add_eq_left this⟩
  refine supDegree_sum_lt ?_ (fun j hj => ?_)
  · exact hs
  · rw [Finset.mem_erase] at 

中文:
引理 supDegree_leadingCoeff_sum_eq
  证明: by
  classical
  rw [← s.add_sum_erase _ hi]
  by_cases! hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨supDegree_add_eq_left this, leadingCoeff_add_eq_left this⟩
  refine supDegree_sum_lt ?_ (fun j hj => ?_)
  · exact hs
  · rw [Finset.mem_erase] at 

Depends on / 依赖: Finset, Finset.mem_erase, Finset.sum_empty, add_sum_erase, add_zero, classical, leadingCoeff_add_eq_left, mem_erase, s.add_sum_erase, s.erase, sum_empty, supDegree_add_eq_left, supDegree_sum_lt
-/
lemma supDegree_leadingCoeff_sum_eq
    (hi : i in s) (hmax : forall j in s, j != i -> (f j).supDegree D < (f i).supDegree D) :
    (∑ j in s, f j).supDegree D = (f i).supDegree D ∧
    (∑ j in s, f j).leadingCoeff D = (f i).leadingCoeff D := by
  classical
  rw [← s.add_sum_erase _ hi]
  by_cases! hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨supDegree_add_eq_left this, leadingCoeff_add_eq_left this⟩
  refine supDegree_sum_lt ?_ (fun j hj => ?_)
  · exact hs
  · rw [Finset.mem_erase] at hj; exact hmax j hj.2 hj.1

open Finset in
/--
lemma `sum_ne_zero_of_injOn_supDegree'` / 引理 `sum_ne_zero_of_injOn_supDegree'`

English:
lemma sum_ne_zero_of_injOn_supDegree'
  statement: (hs : exists i in s, f i != 0)
  proof: by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases! h : forall k in s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk]; rw [h j hj] at hne; exact hne.irrefl.elim
  obtain ⟨j, hj, hne⟩ := h
  a

中文:
引理 sum_ne_zero_of_injOn_supDegree'
  结论: (hs : 存在 i in s, f i != 0)
  证明: by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases! h : forall k in s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk]; rw [h j hj] at hne; exact hne.irrefl.elim
  obtain ⟨j, hj, hne⟩ := h
  a

Depends on / 依赖: exists_mem_eq_sup, hd.ne, hne.irrefl.elim, irrefl, le_sup, lt_of_ne, ne_zero_of_supDegree_ne_bot, sum_eq_single_of_mem, supDegree, supDegree_leadingCoeff_sum_eq, trans_eq, trans_ne
-/
lemma sum_ne_zero_of_injOn_supDegree' (hs : exists i in s, f i != 0)
    (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i in s, f i != 0 := by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases! h : forall k in s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk]; rw [h j hj] at hne; exact hne.irrefl.elim
  obtain ⟨j, hj, hne⟩ := h
  apply ne_zero_of_supDegree_ne_bot (D := D)
  have (k) (hk : k in s) (hne : k != i) : supDegree D (f k) < supDegree D (f i) :=
    ((le_sup hk).trans_eq he).lt_of_ne (hd.ne hk hi hne)
  rw [(supDegree_leadingCoeff_sum_eq hi this).1]
  exact (this j hj hne).ne_bot

/--
lemma `sum_ne_zero_of_injOn_supDegree` / 引理 `sum_ne_zero_of_injOn_supDegree`

English:
lemma sum_ne_zero_of_injOn_supDegree
  statement: (hs : s.Nonempty)
  proof: let ⟨i, hi⟩ := hs
  sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

中文:
引理 sum_ne_zero_of_injOn_supDegree
  结论: (hs : s.Nonempty)
  证明: let ⟨i, hi⟩ := hs
  sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

Depends on / 依赖: sum_ne_zero_of_injOn_supDegree
-/
lemma sum_ne_zero_of_injOn_supDegree (hs : s.Nonempty)
    (hf : forall i in s, f i != 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i in s, f i != 0 :=
  let ⟨i, hi⟩ := hs
  sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

variable [Add B]
variable [AddLeftStrictMono B] [AddRightStrictMono B]

/--
lemma `coeff_supDegree_add_supDegree` / 引理 `coeff_supDegree_add_supDegree`

English:
lemma coeff_supDegree_add_supDegree
  given: (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | hq := eq_or_ne q 0
  · simp
  obtain ⟨ap, -, hp⟩ := exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := exists_supDegree_mem_support D hq
  simp_rw [leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact coeff_add_of

中文:
引理 coeff_supDegree_add_supDegree
  条件: (hD : D.Injective) (hadd : 对任意 a1 a2, D (a1 + a2) = D a1 + D a2)
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | hq := eq_or_ne q 0
  · simp
  obtain ⟨ap, -, hp⟩ := exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := exists_supDegree_mem_support D hq
  simp_rw [leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact coeff_add_of

Depends on / 依赖: Function, Function.leftInverse_invFun, coeff_add_of_supDegree_le, eq_or_ne, exists_supDegree_mem_support, hp.le, hq.le, leadingCoeff, leftInverse_invFun, simp_rw
-/
lemma coeff_supDegree_add_supDegree (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).coeff (D.invFun (p.supDegree D + q.supDegree D)) =
      p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | hq := eq_or_ne q 0
  · simp
  obtain ⟨ap, -, hp⟩ := exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := exists_supDegree_mem_support D hq
  simp_rw [leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact coeff_add_of_supDegree_le hadd hD hp.le hq.le

@[deprecated (since := "2026-06-18")]
alias apply_supDegree_add_supDegree := coeff_supDegree_add_supDegree

set_option backward.isDefEq.respectTransparency false in
/--
lemma `supDegree_mul` / 引理 `supDegree_mul`

English:
lemma supDegree_mul
  proof: by
  apply supDegree_eq_of_max
  · rw [← AddSubsemigroup.coe_set_mk (Set.range D), ← AddHom.srange_mk _ hadd, SetLike.mem_coe]
    · exact add_mem (supDegree_mem_range D hp) (supDegree_mem_range D hq)
    · exact (AddHom.srange ⟨D, hadd⟩).add_mem
  · simp_rw [Finsupp.mem_support_iff, coeff_supDegree

中文:
引理 supDegree_mul
  证明: by
  apply supDegree_eq_of_max
  · rw [← AddSubsemigroup.coe_set_mk (Set.range D), ← AddHom.srange_mk _ hadd, SetLike.mem_coe]
    · exact add_mem (supDegree_mem_range D hp) (supDegree_mem_range D hq)
    · exact (AddHom.srange ⟨D, hadd⟩).add_mem
  · simp_rw [Finsupp.mem_support_iff, coeff_supDegree

Depends on / 依赖: AddHom, AddHom.srange, AddHom.srange_mk, AddSubsemigroup, AddSubsemigroup.coe_set_mk, Finset, Finset.le_sup, Finsupp, Finsupp.mem_support_iff, Set.range, SetLike, SetLike.mem_coe, addLeftMono_of_addLeftStrictMono, addRightMono_of_addRightStrictMono, add_mem, coe_set_mk, coeff_supDegree_add_supDegree, le_sup, mem_coe, mem_support_iff
-/
lemma supDegree_mul
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    (hpq : leadingCoeff D p * leadingCoeff D q != 0)
    (hp : p != 0) (hq : q != 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  apply supDegree_eq_of_max
  · rw [← AddSubsemigroup.coe_set_mk (Set.range D), ← AddHom.srange_mk _ hadd, SetLike.mem_coe]
    · exact add_mem (supDegree_mem_range D hp) (supDegree_mem_range D hq)
    · exact (AddHom.srange ⟨D, hadd⟩).add_mem
  · simp_rw [Finsupp.mem_support_iff, coeff_supDegree_add_supDegree hD hadd]
    exact hpq
  · have := addLeftMono_of_addLeftStrictMono B
    have := addRightMono_of_addRightStrictMono B
    exact fun a ha => (Finset.le_sup ha).trans (supDegree_mul_le hadd)

/--
lemma `Monic.supDegree_mul_of_ne_zero_left` / 引理 `Monic.supDegree_mul_of_ne_zero_left`

English:
lemma Monic.supDegree_mul_of_ne_zero_left
  proof: by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp hq.ne_zero
  simp_rw [hq, mul_one, Ne, leadingCoeff_eq_zero hD, hp, not_false_eq_true]

中文:
引理 Monic.supDegree_mul_of_ne_zero_left
  证明: by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp hq.ne_zero
  simp_rw [hq, mul_one, Ne, leadingCoeff_eq_zero hD, hp, not_false_eq_true]

Depends on / 依赖: Subsingleton, Subsingleton.elim, hq.ne_zero, leadingCoeff_eq_zero, mul_one, ne_zero, not_false_eq_true, simp_rw, subsingleton_or_nontrivial, supDegree_mul
-/
lemma Monic.supDegree_mul_of_ne_zero_left
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    (hq : q.Monic D) (hp : p != 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp hq.ne_zero
  simp_rw [hq, mul_one, Ne, leadingCoeff_eq_zero hD, hp, not_false_eq_true]

/--
lemma `Monic.supDegree_mul_of_ne_zero_right` / 引理 `Monic.supDegree_mul_of_ne_zero_right`

English:
lemma Monic.supDegree_mul_of_ne_zero_right
  proof: by
  cases subsingleton_or_nontrivial R; · exact (hq (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp.ne_zero hq
  simp_rw [hp, one_mul, Ne, leadingCoeff_eq_zero hD, hq, not_false_eq_true]

中文:
引理 Monic.supDegree_mul_of_ne_zero_right
  证明: by
  cases subsingleton_or_nontrivial R; · exact (hq (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp.ne_zero hq
  simp_rw [hp, one_mul, Ne, leadingCoeff_eq_zero hD, hq, not_false_eq_true]

Depends on / 依赖: Subsingleton, Subsingleton.elim, hp.ne_zero, leadingCoeff_eq_zero, ne_zero, not_false_eq_true, one_mul, simp_rw, subsingleton_or_nontrivial, supDegree_mul
-/
lemma Monic.supDegree_mul_of_ne_zero_right
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q != 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hq (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp.ne_zero hq
  simp_rw [hp, one_mul, Ne, leadingCoeff_eq_zero hD, hq, not_false_eq_true]

/--
lemma `Monic.supDegree_mul` / 引理 `Monic.supDegree_mul`

English:
lemma Monic.supDegree_mul
  proof: by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero

中文:
引理 Monic.supDegree_mul
  证明: by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, hp.ne_zero, hq.supDegree_mul_of_ne_zero_left, mul_zero, ne_zero, simp_rw, subsingleton_or_nontrivial, supDegree_mul_of_ne_zero_left, supDegree_zero
-/
lemma Monic.supDegree_mul
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    (hbot : (⊥ : B) + ⊥ = ⊥) (hp : p.Monic D) (hq : q.Monic D) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero

/--
lemma `leadingCoeff_mul` / 引理 `leadingCoeff_mul`

English:
lemma leadingCoeff_mul
  statement: [NoZeroDivisors R]
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul, leadingCoeff_zero]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero, leadingCoeff_zero]
  rw [← coeff_supDegree_add_supDegree hD hadd]; rw [← supDegree_mul hD hadd ?_ hp hq]; rw [leadingCoeff]
  

中文:
引理 leadingCoeff_mul
  结论: [NoZeroDivisors R]
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul, leadingCoeff_zero]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero, leadingCoeff_zero]
  rw [← coeff_supDegree_add_supDegree hD hadd]; rw [← supDegree_mul hD hadd ?_ hp hq]; rw [leadingCoeff]
  

Depends on / 依赖: coeff_supDegree_add_supDegree, eq_or_ne, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_zero, mul_ne_zero, mul_zero, simp_rw, supDegree_mul, zero_mul
-/
lemma leadingCoeff_mul [NoZeroDivisors R]
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).leadingCoeff D = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul, leadingCoeff_zero]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero, leadingCoeff_zero]
  rw [← coeff_supDegree_add_supDegree hD hadd]; rw [← supDegree_mul hD hadd ?_ hp hq]; rw [leadingCoeff]
  apply mul_ne_zero <;> rwa [Ne, leadingCoeff_eq_zero hD]

/--
lemma `Monic.leadingCoeff_mul_eq_left` / 引理 `Monic.leadingCoeff_mul_eq_left`

English:
lemma Monic.leadingCoeff_mul_eq_left
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_mul]
  rw [leadingCoeff]; rw [hq.supDegree_mul_of_ne_zero_left hD hadd hp]; rw [coeff_supDegree_add_supDegree hD hadd]; rw [hq]; rw [mul_one]

中文:
引理 Monic.leadingCoeff_mul_eq_left
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_mul]
  rw [leadingCoeff]; rw [hq.supDegree_mul_of_ne_zero_left hD hadd hp]; rw [coeff_supDegree_add_supDegree hD hadd]; rw [hq]; rw [mul_one]

Depends on / 依赖: coeff_supDegree_add_supDegree, eq_or_ne, hq.supDegree_mul_of_ne_zero_left, leadingCoeff, mul_one, supDegree_mul_of_ne_zero_left, zero_mul
-/
lemma Monic.leadingCoeff_mul_eq_left
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) (hq : q.Monic D) :
    (p * q).leadingCoeff D = p.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_mul]
  rw [leadingCoeff]; rw [hq.supDegree_mul_of_ne_zero_left hD hadd hp]; rw [coeff_supDegree_add_supDegree hD hadd]; rw [hq]; rw [mul_one]

/--
lemma `Monic.leadingCoeff_mul_eq_right` / 引理 `Monic.leadingCoeff_mul_eq_right`

English:
lemma Monic.leadingCoeff_mul_eq_right
  proof: by
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero]
  rw [leadingCoeff]; rw [hp.supDegree_mul_of_ne_zero_right hD hadd hq]; rw [coeff_supDegree_add_supDegree hD hadd]; rw [hp]; rw [one_mul]

中文:
引理 Monic.leadingCoeff_mul_eq_right
  证明: by
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero]
  rw [leadingCoeff]; rw [hp.supDegree_mul_of_ne_zero_right hD hadd hq]; rw [coeff_supDegree_add_supDegree hD hadd]; rw [hp]; rw [one_mul]

Depends on / 依赖: coeff_supDegree_add_supDegree, eq_or_ne, hp.supDegree_mul_of_ne_zero_right, leadingCoeff, mul_zero, one_mul, supDegree_mul_of_ne_zero_right
-/
lemma Monic.leadingCoeff_mul_eq_right
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) (hp : p.Monic D) :
    (p * q).leadingCoeff D = q.leadingCoeff D := by
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero]
  rw [leadingCoeff]; rw [hp.supDegree_mul_of_ne_zero_right hD hadd hq]; rw [coeff_supDegree_add_supDegree hD hadd]; rw [hp]; rw [one_mul]

/--
lemma `Monic.mul` / 引理 `Monic.mul`

English:
lemma Monic.mul
  proof: by
  rw [Monic]; rw [hq.leadingCoeff_mul_eq_left hD hadd]; exact hp

中文:
引理 Monic.mul
  证明: by
  rw [Monic]; rw [hq.leadingCoeff_mul_eq_left hD hadd]; exact hp

Depends on / 依赖: hq.leadingCoeff_mul_eq_left, leadingCoeff_mul_eq_left
-/
lemma Monic.mul
    (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q.Monic D) : (p * q).Monic D := by
  rw [Monic]; rw [hq.leadingCoeff_mul_eq_left hD hadd]; exact hp

section AddMonoid

variable {A B : Type*} [AddMonoid A] [AddMonoid B] [LinearOrder B] [OrderBot B]
  [AddLeftStrictMono B] [AddRightStrictMono B]
  {D : A -> B} {p : R[A]} {n : Nat}

/--
lemma `Monic.pow` / 引理 `Monic.pow`

English:
lemma Monic.pow
  proof: by
  induction n with
  | zero => rw [pow_zero]; exact monic_one hD
  | succ n ih => rw [pow_succ']; exact hp.mul hD hadd ih

中文:
引理 Monic.pow
  证明: by
  induction n with
  | zero => rw [pow_zero]; exact monic_one hD
  | succ n ih => rw [pow_succ']; exact hp.mul hD hadd ih

Depends on / 依赖: hp.mul, monic_one, pow_succ, pow_zero
-/
lemma Monic.pow
    (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    (hp : p.Monic D) : (p ^ n).Monic D := by
  induction n with
  | zero => rw [pow_zero]; exact monic_one hD
  | succ n ih => rw [pow_succ']; exact hp.mul hD hadd ih

/--
lemma `Monic.supDegree_pow` / 引理 `Monic.supDegree_pow`

English:
lemma Monic.supDegree_pow
  proof: by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_def, supDegree_single 0 1, if_neg one_ne_zero, hzero]
  | succ n ih => rw [pow_succ', (hp.pow hadd hD).supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero,
      ih, succ_nsmul']

中文:
引理 Monic.supDegree_pow
  证明: by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_def, supDegree_single 0 1, if_neg one_ne_zero, hzero]
  | succ n ih => rw [pow_succ', (hp.pow hadd hD).supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero,
      ih, succ_nsmul']

Depends on / 依赖: hp.ne_zero, hp.pow, if_neg, ne_zero, one_def, one_ne_zero, pow_succ, pow_zero, succ_nsmul, supDegree_mul_of_ne_zero_left, supDegree_single, zero_nsmul
-/
lemma Monic.supDegree_pow
    (hzero : D 0 = 0) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    [Nontrivial R] (hp : p.Monic D) :
    (p ^ n).supDegree D = n • p.supDegree D := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_def, supDegree_single 0 1, if_neg one_ne_zero, hzero]
  | succ n ih => rw [pow_succ', (hp.pow hadd hD).supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero,
      ih, succ_nsmul']

end AddMonoid

end LinearOrder

section InfDegree

variable [SemilatticeInf T] [OrderTop T] (D : A -> T)

/--
Definition of `infDegree` / `infDegree` 的定义

English:
abbreviation infDegree
  signature: (f : R[A])
  body: f.coeff.support.inf D

中文:
缩写 infDegree
  签名: (f : R[A])
  定义体: f.coeff.support.inf D

Depends on / 依赖: f.coeff.support.inf, support
-/
abbrev infDegree (f : R[A]) : T :=
  f.coeff.support.inf D

/--
theorem `le_infDegree_add` / 定理 `le_infDegree_add`

English:
theorem le_infDegree_add
  given: (f g : R[A])
  proof: le_inf_support_coeff_add D f g

中文:
定理 le_infDegree_add
  条件: (f g : R[A])
  证明: le_inf_support_coeff_add D f g

Depends on / 依赖: le_inf_support_coeff_add
-/
theorem le_infDegree_add (f g : R[A]) :
    (f.infDegree D) ⊓ (g.infDegree D) <= (f + g).infDegree D :=
  le_inf_support_coeff_add D f g

variable {D} in
/--
theorem `infDegree_withTop_some_comp` / 定理 `infDegree_withTop_some_comp`

English:
theorem infDegree_withTop_some_comp
  given: {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty)
  proof: by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs]; rw [Finset.inf'_eq_inf]

中文:
定理 infDegree_withTop_some_comp
  条件: {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty)
  证明: by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs]; rw [Finset.inf'_eq_inf]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.infDegree, Finset, Finset.coe_inf, Finset.inf, _eq_inf, coe_inf, infDegree
-/
theorem infDegree_withTop_some_comp {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty) :
    infDegree (WithTop.some ∘ D) s = infDegree D s := by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs]; rw [Finset.inf'_eq_inf]

/--
theorem `le_infDegree_mul` / 定理 `le_infDegree_mul`

English:
theorem le_infDegree_mul
  statement: [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
  proof: le_inf_support_coeff_mul (fun {a b : A} => (map_add D a b).ge) _ _

中文:
定理 le_infDegree_mul
  结论: [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
  证明: le_inf_support_coeff_mul (fun {a b : A} => (map_add D a b).ge) _ _

Depends on / 依赖: le_inf_support_coeff_mul, map_add
-/
theorem le_infDegree_mul [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
    (D : AddHom A T) (f g : R[A]) :
    f.infDegree D + g.infDegree D <= (f * g).infDegree D :=
  le_inf_support_coeff_mul (fun {a b : A} => (map_add D a b).ge) _ _

end InfDegree

end Degrees

end AddMonoidAlgebra
