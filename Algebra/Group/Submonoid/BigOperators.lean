/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Finset.NoncommProd

/-!
# Submonoids: membership criteria for products and sums

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;

## Tags
submonoid, submonoids
-/

public section

-- We don't need ordered structures to establish basic membership facts for submonoids
assert_not_exists IsOrderedRing

variable {M A B : Type*}

section SubmonoidClass
variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

namespace SubmonoidClass

@[to_additive (attr := norm_cast, simp)]
/--
theorem `coe_list_prod` / 定理 `coe_list_prod`

English:
theorem coe_list_prod
  given: (l : List S)
  statement: (l.prod : M) = (l.map (↑)).prod
  proof: map_list_prod (SubmonoidClass.subtype S : _ ->* M) l

@[to_additive (attr := norm_cast, simp)]

中文:
定理 coe_list_prod
  条件: (l : List S)
  结论: (l.prod : M) = (l.map (↑)).prod
  证明: map_list_prod (SubmonoidClass.subtype S : _ ->* M) l

@[to_additive (attr := norm_cast, simp)]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, map_list_prod, subtype
-/
theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod :=
  map_list_prod (SubmonoidClass.subtype S : _ ->* M) l

@[to_additive (attr := norm_cast, simp)]
/--
theorem `coe_multiset_prod` / 定理 `coe_multiset_prod`

English:
theorem coe_multiset_prod
  given: {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S)
  proof: (SubmonoidClass.subtype S : _ ->* M).map_multiset_prod m

@[to_additive (attr := norm_cast, simp)]

中文:
定理 coe_multiset_prod
  条件: {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S)
  证明: (SubmonoidClass.subtype S : _ ->* M).map_multiset_prod m

@[to_additive (attr := norm_cast, simp)]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, map_multiset_prod, subtype
-/
theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  (SubmonoidClass.subtype S : _ ->* M).map_multiset_prod m

@[to_additive (attr := norm_cast, simp)]
/--
theorem `coe_finsetProd` / 定理 `coe_finsetProd`

English:
theorem coe_finsetProd
  statement: {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι -> S)
  proof: map_prod (SubmonoidClass.subtype S) f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoidClass.coe_finset_sum := _root_.AddSubmonoidClass.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

中文:
定理 coe_finsetProd
  结论: {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι -> S)
  证明: map_prod (SubmonoidClass.subtype S) f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoidClass.coe_finset_sum := _root_.AddSubmonoidClass.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, map_prod, subtype
-/
theorem coe_finsetProd {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι -> S)
    (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  map_prod (SubmonoidClass.subtype S) f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoidClass.coe_finset_sum := _root_.AddSubmonoidClass.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

end SubmonoidClass

open SubmonoidClass

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive /-- Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`. -/]
/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {l : List M} (hl : forall x in l, x in S)
  statement: l.prod in S
  proof: by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

中文:
定理 list_prod_mem
  条件: {l : List M} (hl : 对任意 x in l, x in S)
  结论: l.prod in S
  证明: by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

Depends on / 依赖: coe_list_prod, coe_prop, l.prod.coe_prop
-/
theorem list_prod_mem {l : List M} (hl : forall x in l, x in S) : l.prod in S := by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      /-- Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`. -/]
/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  statement: {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
  proof: by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

中文:
定理 multiset_prod_mem
  结论: {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
  证明: by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

Depends on / 依赖: Multiset, coe_multiset_prod, coe_prop, m.prod.coe_prop
-/
theorem multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : forall a in m, a in S) : m.prod in S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
submonoid. -/
@[to_additive
      /-- Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`. -/]
/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type*}
  proof: multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

中文:
定理 prod_mem
  结论: {M : 类型} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : 类型}
  证明: multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

Depends on / 依赖: Multiset, Multiset.mem_map, mem_map, multiset_prod_mem
-/
theorem prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type*}
    {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S) : (∏ c in t, f c) in S :=
  multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

end SubmonoidClass

namespace Submonoid
section Monoid
variable [Monoid M] {x : M} (s : Submonoid M)

@[to_additive (attr := norm_cast)]
/--
theorem `coe_list_prod` / 定理 `coe_list_prod`

English:
theorem coe_list_prod
  given: (l : List s)
  statement: (l.prod : M) = (l.map (↑)).prod
  proof: map_list_prod s.subtype l

@[to_additive (attr := norm_cast)]

中文:
定理 coe_list_prod
  条件: (l : List s)
  结论: (l.prod : M) = (l.map (↑)).prod
  证明: map_list_prod s.subtype l

@[to_additive (attr := norm_cast)]

Depends on / 依赖: map_list_prod, s.subtype, subtype
-/
theorem coe_list_prod (l : List s) : (l.prod : M) = (l.map (↑)).prod :=
  map_list_prod s.subtype l

@[to_additive (attr := norm_cast)]
/--
theorem `coe_multiset_prod` / 定理 `coe_multiset_prod`

English:
theorem coe_multiset_prod
  given: {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S)
  proof: S.subtype.map_multiset_prod m

@[to_additive (attr := norm_cast)]

中文:
定理 coe_multiset_prod
  条件: {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S)
  证明: S.subtype.map_multiset_prod m

@[to_additive (attr := norm_cast)]

Depends on / 依赖: S.subtype.map_multiset_prod, map_multiset_prod, subtype
-/
theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  S.subtype.map_multiset_prod m

@[to_additive (attr := norm_cast)]
/--
theorem `coe_finsetProd` / 定理 `coe_finsetProd`

English:
theorem coe_finsetProd
  given: {ι M} [CommMonoid M] (S : Submonoid M) (f : ι -> S) (s : Finset ι)
  proof: map_prod S.subtype f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoid.coe_finset_sum := _root_.AddSubmonoid.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

中文:
定理 coe_finsetProd
  条件: {ι M} [CommMonoid M] (S : Submonoid M) (f : ι -> S) (s : Finset ι)
  证明: map_prod S.subtype f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoid.coe_finset_sum := _root_.AddSubmonoid.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

Depends on / 依赖: S.subtype, map_prod, subtype
-/
theorem coe_finsetProd {ι M} [CommMonoid M] (S : Submonoid M) (f : ι -> S) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  map_prod S.subtype f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoid.coe_finset_sum := _root_.AddSubmonoid.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive /-- Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`. -/]
/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {l : List M} (hl : forall x in l, x in s)
  statement: l.prod in s
  proof: _root_.list_prod_mem hl

中文:
定理 list_prod_mem
  条件: {l : List M} (hl : 对任意 x in l, x in s)
  结论: l.prod in s
  证明: _root_.list_prod_mem hl

Depends on / 依赖: _root_, _root_.list_prod_mem, list_prod_mem
-/
theorem list_prod_mem {l : List M} (hl : forall x in l, x in s) : l.prod in s := _root_.list_prod_mem hl

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      /-- Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`. -/]
/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  statement: {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
  proof: _root_.multiset_prod_mem m hm

@[to_additive]

中文:
定理 multiset_prod_mem
  结论: {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
  证明: _root_.multiset_prod_mem m hm

@[to_additive]

Depends on / 依赖: _root_, _root_.multiset_prod_mem, multiset_prod_mem
-/
theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : forall a in m, a in S) : m.prod in S := _root_.multiset_prod_mem m hm

@[to_additive]
/--
theorem `multiset_noncommProd_mem` / 定理 `multiset_noncommProd_mem`

English:
theorem multiset_noncommProd_mem
  given: (S : Submonoid M) (m : Multiset M) (comm) (h : forall x in m, x in S)
  proof: by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

中文:
定理 multiset_noncommProd_mem
  条件: (S : Submonoid M) (m : Multiset M) (comm) (h : 对任意 x in m, x in S)
  证明: by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

Depends on / 依赖: Multiset, Multiset.noncommProd_coe, Multiset.quot_mk_to_coe, Quotient, Quotient.inductionOn, Submonoid, Submonoid.list_prod_mem, inductionOn, list_prod_mem, noncommProd_coe, quot_mk_to_coe
-/
theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : forall x in m, x in S) :
    m.noncommProd comm in S := by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
submonoid. -/
@[to_additive
      /-- Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`. -/]
/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Finset ι}
  proof: S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

@[to_additive]

中文:
定理 prod_mem
  结论: {M : 类型} [CommMonoid M] (S : Submonoid M) {ι : 类型} {t : Finset ι}
  证明: S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

@[to_additive]

Depends on / 依赖: Multiset, Multiset.mem_map, S.multiset_prod_mem, mem_map, multiset_prod_mem
-/
theorem prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Finset ι}
    {f : ι -> M} (h : forall c in t, f c in S) : (∏ c in t, f c) in S :=
  S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

@[to_additive]
/--
theorem `noncommProd_mem` / 定理 `noncommProd_mem`

English:
theorem noncommProd_mem
  statement: (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι -> M) (comm)
  proof: by
  apply multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

中文:
定理 noncommProd_mem
  结论: (S : Submonoid M) {ι : 类型} (t : Finset ι) (f : ι -> M) (comm)
  证明: by
  apply multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

Depends on / 依赖: Multiset, Multiset.mem_map, mem_map, multiset_noncommProd_mem
-/
theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι -> M) (comm)
    (h : forall c in t, f c in S) : t.noncommProd f comm in S := by
  apply multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

end Monoid

section CommMonoid
variable [CommMonoid M] {x : M}

@[to_additive]
/--
lemma `mem_closure_iff_exists_finset_subset` / 引理 `mem_closure_iff_exists_finset_subset`

English:
lemma mem_closure_iff_exists_finset_subset
  given: {s : Set M}
  proof: by
    classical
    induction hx using closure_induction with
    | one => exact ⟨0, ∅, by simp⟩
    | mem x hx =>
      exact ⟨Pi.single x 1, {x}, by simp [hx, Pi.single_apply]⟩
    | mul x y _ _ hx hy =>
    obtain ⟨f, t, hts, hf, rfl⟩ := hx
    obtain ⟨g, u, hus, hg, rfl⟩ := hy
    refine ⟨f + g

中文:
引理 mem_closure_iff_exists_finset_subset
  条件: {s : Set M}
  证明: by
    classical
    induction hx using closure_induction with
    | one => exact ⟨0, ∅, by simp⟩
    | mem x hx =>
      exact ⟨Pi.single x 1, {x}, by simp [hx, Pi.single_apply]⟩
    | mul x y _ _ hx hy =>
    obtain ⟨f, t, hts, hf, rfl⟩ := hx
    obtain ⟨g, u, hus, hg, rfl⟩ := hy
    refine ⟨f + g

Depends on / 依赖: Finset, Finset.prod_mul_distrib, Finset.prod_subset, Finset.sub, Function, Function.support_add, Pi.add_apply, Pi.single, Pi.single_apply, Set.union_subset, Set.union_subset_union, add_apply, classical, closure_induction, mod_cast, pow_add, prod_mul_distrib, prod_subset, single, single_apply
-/
lemma mem_closure_iff_exists_finset_subset {s : Set M} :
    x in closure s ↔
      exists (f : M -> Nat) (t : Finset M), ↑t subseteq s ∧ f.support subseteq t ∧ ∏ a in t, a ^ f a = x where
  mp hx := by
    classical
    induction hx using closure_induction with
    | one => exact ⟨0, ∅, by simp⟩
    | mem x hx =>
      exact ⟨Pi.single x 1, {x}, by simp [hx, Pi.single_apply]⟩
    | mul x y _ _ hx hy =>
    obtain ⟨f, t, hts, hf, rfl⟩ := hx
    obtain ⟨g, u, hus, hg, rfl⟩ := hy
    refine ⟨f + g, t union u, mod_cast Set.union_subset hts hus,
(Function.support_add _ _).trans mod_cast Set.union_subset_union hf hg, ?_⟩
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1 <;> symm
    · refine Finset.prod_subset Finset.subset_union_left ?_
      simp +contextual [Function.support_subset_iff'.1 hf]
    · refine Finset.prod_subset Finset.subset_union_right ?_
      simp +contextual [Function.support_subset_iff'.1 hg]
  mpr := by
    rintro ⟨n, t, hts, -, rfl⟩; exact prod_mem _ fun x hx => pow_mem (subset_closure <| hts hx) _

@[to_additive]
/--
lemma `mem_closure_finset` / 引理 `mem_closure_finset`

English:
lemma mem_closure_finset
  given: {s : Finset M}
  proof: by
    rw [mem_closure_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
refine ⟨f, hf.trans hts, .symm Finset.prod_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
  mpr := by rintro ⟨n, -, rfl⟩; exact prod_mem _ fun x hx => pow_mem (subset_closure hx) _

中文:
引理 mem_closure_finset
  条件: {s : Finset M}
  证明: by
    rw [mem_closure_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
refine ⟨f, hf.trans hts, .symm Finset.prod_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
  mpr := by rintro ⟨n, -, rfl⟩; exact prod_mem _ fun x hx => pow_mem (subset_closure hx) _

Depends on / 依赖: Finset, Finset.prod_subset, Function, Function.support_subset_iff, contextual, hf.trans, mem_closure_iff_exists_finset_subset, pow_mem, prod_mem, prod_subset, subset_closure, support_subset_iff
-/
lemma mem_closure_finset {s : Finset M} :
    x in closure s ↔ exists f : M -> Nat, f.support subseteq s ∧ ∏ a in s, a ^ f a = x where
  mp := by
    rw [mem_closure_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
refine ⟨f, hf.trans hts, .symm Finset.prod_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
  mpr := by rintro ⟨n, -, rfl⟩; exact prod_mem _ fun x hx => pow_mem (subset_closure hx) _

end CommMonoid
end Submonoid
