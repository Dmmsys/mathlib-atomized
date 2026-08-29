/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.SkewMonoidAlgebra.Basic

/-!
# Lemmas about the support of an element of a skew monoid algebra

For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that `f.coeff a ≠ 0`.
-/

public section

open scoped Pointwise

namespace SkewMonoidAlgebra

open Finset Finsupp

variable {k G : Type*}

section AddCommMonoid

variable [AddCommMonoid k] {a : G} {b : k}

/--
lemma `support_single` / 引理 `support_single`

English:
lemma support_single
  given: (a : G) (h : b != 0)
  statement: (single a b).support = {a}
  proof: Finsupp.support_single _ h

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

中文:
引理 support_single
  条件: (a : G) (h : b != 0)
  结论: (single a b).support = {a}
  证明: Finsupp.support_single _ h

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single
-/
@[simp] lemma support_single (a : G) (h : b != 0) : (single a b).support = {a} :=
  Finsupp.support_single _ h

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

/--
theorem `support_single_subset` / 定理 `support_single_subset`

English:
theorem support_single_subset
  statement: (single a b).support subseteq {a}
  proof: Finsupp.support_single_subset

中文:
定理 support_single_subset
  结论: (single a b).support subseteq {a}
  证明: Finsupp.support_single_subset

Depends on / 依赖: Finsupp, Finsupp.support_single_subset, support_single_subset
-/
theorem support_single_subset : (single a b).support subseteq {a} := Finsupp.support_single_subset

/--
theorem `support_sum` / 定理 `support_sum`

English:
theorem support_sum
  statement: {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
  proof: by
  simp_rw [support, coeff_sum']
  apply Finsupp.support_sum

中文:
定理 support_sum
  结论: {k' G' : 类型} [DecidableEq G'] [加法交换幺半群 k'] {f : 斜幺半群代数 k G}
  证明: by
  simp_rw [support, coeff_sum']
  apply Finsupp.support_sum

Depends on / 依赖: Finsupp, Finsupp.support_sum, coeff_sum, simp_rw, support, support_sum
-/
theorem support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G -> k -> SkewMonoidAlgebra k' G'} :
    (f.sum g).support subseteq f.support.biUnion fun a => (g a (f.coeff a)).support := by
  simp_rw [support, coeff_sum']
  apply Finsupp.support_sum

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup k]

/--
theorem `support_neg` / 定理 `support_neg`

English:
theorem support_neg
  given: (p : SkewMonoidAlgebra k G)
  statement: (-p).support = p.support
  proof: by
  rw [support]; rw [coeff_neg]; rw [Finsupp.support_neg]; rw [support_coeff]

中文:
定理 support_neg
  条件: (p : 斜幺半群代数 k G)
  结论: (-p).support = p.support
  证明: by
  rw [support]; rw [coeff_neg]; rw [Finsupp.support_neg]; rw [support_coeff]

Depends on / 依赖: Finsupp, Finsupp.support_neg, coeff_neg, support, support_coeff, support_neg
-/
theorem support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support := by
  rw [support]; rw [coeff_neg]; rw [Finsupp.support_neg]; rw [support_coeff]

end AddCommGroup

section AddCommMonoidWithOne

variable [One G] [AddCommMonoidWithOne k]

/--
lemma `support_one_subset` / 引理 `support_one_subset`

English:
lemma support_one_subset
  statement: (1 : SkewMonoidAlgebra k G).support subseteq 1
  proof: Finsupp.support_single_subset

@[simp]

中文:
引理 support_one_subset
  结论: (1 : 斜幺半群代数 k G).support subseteq 1
  证明: Finsupp.support_single_subset

@[simp]

Depends on / 依赖: Finsupp, Finsupp.support_single_subset, support_single_subset
-/
lemma support_one_subset : (1 : SkewMonoidAlgebra k G).support subseteq 1 :=
  Finsupp.support_single_subset

@[simp]
/--
lemma `support_one` / 引理 `support_one`

English:
lemma support_one
  given: [NeZero (1 : k)]
  statement: (1 : SkewMonoidAlgebra k G).support = 1
  proof: Finsupp.support_single _ one_ne_zero

中文:
引理 support_one
  条件: [NeZero (1 : k)]
  结论: (1 : 斜幺半群代数 k G).support = 1
  证明: Finsupp.support_single _ one_ne_zero

Depends on / 依赖: Finsupp, Finsupp.support_single, one_ne_zero, support_single
-/
lemma support_one [NeZero (1 : k)] : (1 : SkewMonoidAlgebra k G).support = 1 :=
  Finsupp.support_single _ one_ne_zero

end AddCommMonoidWithOne

section Semiring

variable [Monoid G] [Semiring k] [MulSemiringAction G k]
variable (f g : SkewMonoidAlgebra k G)

section DecidableEq

variable [DecidableEq G]

/--
theorem `support_mul` / 定理 `support_mul`

English:
theorem support_mul
  statement: (f * g).support subseteq f.support * g.support
  proof: support_sum.trans biUnion_subset.2 fun _x hx =>
support_sum.trans biUnion_subset.2 fun _y hy =>
support_single_subset.trans singleton_subset_iff.2 mem_image₂_of_mem hx hy

中文:
定理 support_mul
  结论: (f * g).support subseteq f.support * g.support
  证明: support_sum.trans biUnion_subset.2 fun _x hx =>
support_sum.trans biUnion_subset.2 fun _y hy =>
support_single_subset.trans singleton_subset_iff.2 mem_image₂_of_mem hx hy

Depends on / 依赖: biUnion_subset, singleton_subset_iff, support_single_subset, support_single_subset.trans, support_sum, support_sum.trans
-/
theorem support_mul : (f * g).support subseteq f.support * g.support :=
support_sum.trans biUnion_subset.2 fun _x hx =>
support_sum.trans biUnion_subset.2 fun _y hy =>
support_single_subset.trans singleton_subset_iff.2 mem_image₂_of_mem hx hy

/--
theorem `support_single_mul_subset` / 定理 `support_single_mul_subset`

English:
theorem support_single_mul_subset
  given: (r : k) (a : G)
  proof: (support_mul _ _).trans (Finset.image₂_subset_right support_single_subset).trans by
    rw [Finset.image₂_singleton_left]

中文:
定理 support_single_mul_subset
  条件: (r : k) (a : G)
  证明: (support_mul _ _).trans (Finset.image₂_subset_right support_single_subset).trans by
    rw [Finset.image₂_singleton_left]

Depends on / 依赖: Finset, Finset.image, support_mul, support_single_subset
-/
theorem support_single_mul_subset (r : k) (a : G) :
    (single a r * f : SkewMonoidAlgebra k G).support subseteq Finset.image (a * ·) f.support :=
(support_mul _ _).trans (Finset.image₂_subset_right support_single_subset).trans by
    rw [Finset.image₂_singleton_left]

/--
theorem `support_mul_single_subset` / 定理 `support_mul_single_subset`

English:
theorem support_mul_single_subset
  given: (r : k) (a : G)
  proof: (support_mul _ _).trans (Finset.image₂_subset_left support_single_subset).trans by
    rw [Finset.image₂_singleton_right]

中文:
定理 support_mul_single_subset
  条件: (r : k) (a : G)
  证明: (support_mul _ _).trans (Finset.image₂_subset_left support_single_subset).trans by
    rw [Finset.image₂_singleton_right]

Depends on / 依赖: Finset, Finset.image, support_mul, support_single_subset
-/
theorem support_mul_single_subset (r : k) (a : G) :
    (f * single a r).support subseteq Finset.image (· * a) f.support :=
(support_mul _ _).trans (Finset.image₂_subset_left support_single_subset).trans by
    rw [Finset.image₂_singleton_right]

/--
theorem `support_single_mul_eq_image` / 定理 `support_single_mul_eq_image`

English:
theorem support_single_mul_eq_image
  statement: {r : k} {x : G} (lx : IsLeftRegular x)
  proof: by
  refine subset_antisymm (support_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_m

中文:
定理 support_single_mul_eq_image
  结论: {r : k} {x : G} (lx : IsLeftRegular x)
  证明: by
  refine subset_antisymm (support_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_m

Depends on / 依赖: Finset, Finset.mem_image, coeff_mul, eq_iff, exists_prop, f.support, ite_self, lx.eq_iff, mem_image, mem_support_iff, mem_support_iff.mp, subset_antisymm, sum_single_index, sum_zero, support, support_single_mul_subset, zero_mul
-/
theorem support_single_mul_eq_image {r : k} {x : G} (lx : IsLeftRegular x)
    (hrx : forall y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = Finset.image (x * ·) f.support := by
  refine subset_antisymm (support_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_mul, ite_self, sum_zero, lx.eq_iff]

/--
theorem `support_mul_single_eq_image` / 定理 `support_mul_single_eq_image`

English:
theorem support_mul_single_eq_image
  statement: {r : k} {x : G} (rx : IsRightRegular x)
  proof: by
  refine subset_antisymm (support_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    

中文:
定理 support_mul_single_eq_image
  结论: {r : k} {x : G} (rx : IsRightRegular x)
  证明: by
  refine subset_antisymm (support_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    

Depends on / 依赖: Finset, Finset.mem_image, coeff_mul, eq_iff, exists_prop, f.support, ite_self, mem_image, mem_support_iff, mem_support_iff.mp, mul_zero, rx.eq_iff, subset_antisymm, sum_single_index, support, support_mul_single_subset
-/
theorem support_mul_single_eq_image {r : k} {x : G} (rx : IsRightRegular x)
    (hrx : forall g : G, forall y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine subset_antisymm (support_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    ite_self, rx.eq_iff]

end DecidableEq

/--
theorem `support_mul_single` / 定理 `support_mul_single`

English:
theorem support_mul_single
  statement: [IsRightCancelMul G] (r : k) (x : G)
  proof: by
  classical
  ext a
  simp [support_mul_single_eq_image f (IsRightRegular.all x) hrx]

中文:
定理 support_mul_single
  结论: [右乘消去 G] (r : k) (x : G)
  证明: by
  classical
  ext a
  simp [support_mul_single_eq_image f (IsRightRegular.all x) hrx]

Depends on / 依赖: IsRightRegular, IsRightRegular.all, classical, support_mul_single_eq_image
-/
theorem support_mul_single [IsRightCancelMul G] (r : k) (x : G)
    (hrx : forall g : G, forall y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
  ext a
  simp [support_mul_single_eq_image f (IsRightRegular.all x) hrx]

/--
theorem `support_single_mul` / 定理 `support_single_mul`

English:
theorem support_single_mul
  statement: [IsLeftCancelMul G] (r : k) (x : G)
  proof: by
  classical
  ext a
  simp [support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

中文:
定理 support_single_mul
  结论: [左乘消去 G] (r : k) (x : G)
  证明: by
  classical
  ext a
  simp [support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

Depends on / 依赖: IsLeftRegular, IsLeftRegular.all, classical, support_single_mul_eq_image
-/
theorem support_single_mul [IsLeftCancelMul G] (r : k) (x : G)
    (hrx : forall y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
  ext a
  simp [support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

section Span

/--
theorem `mem_span_support` / 定理 `mem_span_support`

English:
theorem mem_span_support
  given: (f : SkewMonoidAlgebra k G)
  proof: by
  rw [Fintype.mem_span_image_iff_exists_fun k]
  use Finset.restrict f.support f.coeff
  simp [smul_single, ← sum_def', sum_single]

中文:
定理 mem_span_support
  条件: (f : 斜幺半群代数 k G)
  证明: by
  rw [Fintype.mem_span_image_iff_exists_fun k]
  use Finset.restrict f.support f.coeff
  simp [smul_single, ← sum_def', sum_single]

Depends on / 依赖: Finset, Finset.restrict, Fintype, Fintype.mem_span_image_iff_exists_fun, f.coeff, f.support, mem_span_image_iff_exists_fun, restrict, smul_single, sum_def, sum_single, support
-/
theorem mem_span_support (f : SkewMonoidAlgebra k G) :
    f in Submodule.span k (of k G '' (f.support : Set G)) := by
  rw [Fintype.mem_span_image_iff_exists_fun k]
  use Finset.restrict f.support f.coeff
  simp [smul_single, ← sum_def', sum_single]

end Span

end Semiring

end SkewMonoidAlgebra
