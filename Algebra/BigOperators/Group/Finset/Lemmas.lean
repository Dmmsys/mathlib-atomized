/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Notation.Support

/-!
# Miscellaneous lemmas on big operators

The lemmas in this file have been moved out of
`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` to reduce its imports.
-/

public section

variable {ι κ M N β : Type*}

@[to_additive]
/--
theorem `MonoidHom.coe_finsetProd` / 定理 `MonoidHom.coe_finsetProd`

English:
theorem MonoidHom.coe_finsetProd
  given: [MulOneClass M] [CommMonoid N] (f : ι -> M ->* N) (s : Finset ι)
  proof: map_prod (MonoidHom.coeFn M N) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.coe_finset_sum := AddMonoidHom.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.coe_finset_prod := MonoidHom.coe_finsetProd

中文:
定理 幺半群态射.coe_finsetProd
  条件: [MulOne类 M] [交换幺半群 N] (f : ι -> M ->* N) (s : 有限集 ι)
  证明: map_prod (MonoidHom.coeFn M N) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.coe_finset_sum := AddMonoidHom.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.coe_finset_prod := MonoidHom.coe_finsetProd

Depends on / 依赖: MonoidHom, MonoidHom.coeFn, map_prod
-/
theorem MonoidHom.coe_finsetProd [MulOneClass M] [CommMonoid N] (f : ι -> M ->* N) (s : Finset ι) :
    ⇑(∏ x in s, f x) = ∏ x in s, ⇑(f x) :=
  map_prod (MonoidHom.coeFn M N) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.coe_finset_sum := AddMonoidHom.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.coe_finset_prod := MonoidHom.coe_finsetProd

/-- See also `Finset.prod_apply`, with the same conclusion but with the weaker hypothesis
`f : α → M → N` -/
@[to_additive (attr := simp)
  /-- See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
  `f : α → M → N` -/]
/--
theorem `MonoidHom.finsetProd_apply` / 定理 `MonoidHom.finsetProd_apply`

English:
theorem MonoidHom.finsetProd_apply
  statement: [MulOneClass M] [CommMonoid N] (f : ι -> M ->* N) (s : Finset ι)
  proof: map_prod (MonoidHom.eval b) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.finset_sum_apply := AddMonoidHom.finsetSum_apply

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.finset_prod_apply := MonoidHom.finsetProd_apply

中文:
定理 幺半群态射.finsetProd_apply
  结论: [MulOne类 M] [交换幺半群 N] (f : ι -> M ->* N) (s : 有限集 ι)
  证明: map_prod (MonoidHom.eval b) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.finset_sum_apply := AddMonoidHom.finsetSum_apply

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.finset_prod_apply := MonoidHom.finsetProd_apply

Depends on / 依赖: MonoidHom, MonoidHom.eval, map_prod
-/
theorem MonoidHom.finsetProd_apply [MulOneClass M] [CommMonoid N] (f : ι -> M ->* N) (s : Finset ι)
    (b : M) : (∏ x in s, f x) b = ∏ x in s, f x b :=
  map_prod (MonoidHom.eval b) _ _

@[deprecated (since := "2026-04-08")]
alias AddMonoidHom.finset_sum_apply := AddMonoidHom.finsetSum_apply

@[to_additive existing, deprecated (since := "2026-04-08")]
alias MonoidHom.finset_prod_apply := MonoidHom.finsetProd_apply

namespace Finset

variable [CommMonoid M]

open Function in
@[to_additive]
/--
lemma `mulSupport_prod` / 引理 `mulSupport_prod`

English:
lemma mulSupport_prod
  given: (s : Finset ι) (f : ι -> κ -> M)
  proof: by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, notMem_mulSupport]
  exact fun x => prod_eq_one

@[to_additive]

中文:
引理 mulSupport_prod
  条件: (s : 有限集 ι) (f : ι -> κ -> M)
  证明: by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, notMem_mulSupport]
  exact fun x => prod_eq_one

@[to_additive]

Depends on / 依赖: Set.mem_iUnion, mem_iUnion, mulSupport_subset_iff, notMem_mulSupport, not_exists, prod_eq_one
-/
lemma mulSupport_prod (s : Finset ι) (f : ι -> κ -> M) :
    mulSupport (fun x => ∏ i in s, f i x) subseteq ⋃ i in s, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, notMem_mulSupport]
  exact fun x => prod_eq_one

@[to_additive]
/--
lemma `isSquare_prod` / 引理 `isSquare_prod`

English:
lemma isSquare_prod
  given: {s : Finset ι} (f : ι -> M) (h : forall c in s, IsSquare (f c))
  proof: by
  rw [isSquare_iff_exists_sq]
  use (∏ (x : s), ((isSquare_iff_exists_sq _).mp (h _ x.2)).choose)
  rw [@sq]; rw [← Finset.prod_mul_distrib]; rw [← Finset.prod_coe_sort]
  congr
  ext i
  rw [← @sq]
  exact ((isSquare_iff_exists_sq _).mp (h _ i.2)).choose_spec

中文:
引理 isSquare_prod
  条件: {s : 有限集 ι} (f : ι -> M) (h : 对任意 c in s, IsSquare (f c))
  证明: by
  rw [isSquare_iff_exists_sq]
  use (∏ (x : s), ((isSquare_iff_exists_sq _).mp (h _ x.2)).choose)
  rw [@sq]; rw [← Finset.prod_mul_distrib]; rw [← Finset.prod_coe_sort]
  congr
  ext i
  rw [← @sq]
  exact ((isSquare_iff_exists_sq _).mp (h _ i.2)).choose_spec

Depends on / 依赖: Finset, Finset.prod_coe_sort, Finset.prod_mul_distrib, choose_spec, isSquare_iff_exists_sq, prod_coe_sort, prod_mul_distrib
-/
lemma isSquare_prod {s : Finset ι} (f : ι -> M) (h : forall c in s, IsSquare (f c)) :
    IsSquare (∏ i in s, f i) := by
  rw [isSquare_iff_exists_sq]
  use (∏ (x : s), ((isSquare_iff_exists_sq _).mp (h _ x.2)).choose)
  rw [@sq]; rw [← Finset.prod_mul_distrib]; rw [← Finset.prod_coe_sort]
  congr
  ext i
  rw [← @sq]
  exact ((isSquare_iff_exists_sq _).mp (h _ i.2)).choose_spec

end Finset
