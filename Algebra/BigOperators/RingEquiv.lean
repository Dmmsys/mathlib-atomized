/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Results about mapping big operators across ring equivalences
-/

public section


namespace RingEquiv

variable {α R S : Type*}

/--
theorem `map_list_prod` / 定理 `map_list_prod`

English:
theorem map_list_prod
  given: [Semiring R] [Semiring S] (f : R ≃+* S) (l : List R)
  proof: map_list_prod f l

中文:
定理 map_list_prod
  条件: [半环 R] [半环 S] (f : R ≃+* S) (l : 列表 R)
  证明: map_list_prod f l
-/
protected theorem map_list_prod [Semiring R] [Semiring S] (f : R ≃+* S) (l : List R) :
    f l.prod = (l.map f).prod := map_list_prod f l

/--
theorem `map_list_sum` / 定理 `map_list_sum`

English:
theorem map_list_sum
  statement: [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  proof: map_list_sum f l

中文:
定理 map_list_sum
  结论: [非幺非结合半环 R] [非幺非结合半环 S]
  证明: map_list_sum f l
-/
protected theorem map_list_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R ≃+* S) (l : List R) : f l.sum = (l.map f).sum := map_list_sum f l

/--
theorem `unop_map_list_prod` / 定理 `unop_map_list_prod`

English:
theorem unop_map_list_prod
  given: [Semiring R] [Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R)
  proof: unop_map_list_prod f l

中文:
定理 unop_map_list_prod
  条件: [半环 R] [半环 S] (f : R ≃+* Sᵐᵒᵖ) (l : 列表 R)
  证明: unop_map_list_prod f l
-/
protected theorem unop_map_list_prod [Semiring R] [Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R) :
    MulOpposite.unop (f l.prod) = (l.map (MulOpposite.unop ∘ f)).reverse.prod :=
  unop_map_list_prod f l

/--
theorem `map_multiset_prod` / 定理 `map_multiset_prod`

English:
theorem map_multiset_prod
  statement: [CommSemiring R] [CommSemiring S] (f : R ≃+* S)
  proof: map_multiset_prod f s

中文:
定理 map_multiset_prod
  结论: [交换半环 R] [交换半环 S] (f : R ≃+* S)
  证明: map_multiset_prod f s
-/
protected theorem map_multiset_prod [CommSemiring R] [CommSemiring S] (f : R ≃+* S)
    (s : Multiset R) : f s.prod = (s.map f).prod :=
  map_multiset_prod f s

/--
theorem `map_multiset_sum` / 定理 `map_multiset_sum`

English:
theorem map_multiset_sum
  statement: [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  proof: map_multiset_sum f s

中文:
定理 map_multiset_sum
  结论: [非幺非结合半环 R] [非幺非结合半环 S]
  证明: map_multiset_sum f s
-/
protected theorem map_multiset_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R ≃+* S) (s : Multiset R) : f s.sum = (s.map f).sum :=
  map_multiset_sum f s

/--
theorem `map_prod` / 定理 `map_prod`

English:
theorem map_prod
  statement: [CommSemiring R] [CommSemiring S] (g : R ≃+* S) (f : α -> R)
  proof: map_prod g f s

中文:
定理 map_prod
  结论: [交换半环 R] [交换半环 S] (g : R ≃+* S) (f : α -> R)
  证明: map_prod g f s
-/
protected theorem map_prod [CommSemiring R] [CommSemiring S] (g : R ≃+* S) (f : α -> R)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  statement: [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (g : R ≃+* S)
  proof: map_sum g f s

中文:
定理 map_sum
  结论: [非幺非结合半环 R] [非幺非结合半环 S] (g : R ≃+* S)
  证明: map_sum g f s
-/
protected theorem map_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (g : R ≃+* S)
    (f : α -> R) (s : Finset α) : g (∑ x in s, f x) = ∑ x in s, g (f x) :=
  map_sum g f s

end RingEquiv
