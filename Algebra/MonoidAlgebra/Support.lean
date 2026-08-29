/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import Mathlib.LinearAlgebra.Span.Basic

/-!
# Lemmas about the support of a finitely supported function
-/

public section

open scoped Pointwise

universe u₁ u₂ u₃

namespace MonoidAlgebra

open Finset Finsupp

variable {k : Type u₁} {G : Type u₂} [Semiring k]

section Mul
variable [Mul G]

@[to_additive (dont_translate := k) support_coeff_mul_subset]
/--
theorem `support_coeff_mul_subset` / 定理 `support_coeff_mul_subset`

English:
theorem support_coeff_mul_subset
  given: [DecidableEq G] (x y : k[G])
  proof: by
  simp only [MonoidAlgebra.mul_def, coeff_finsuppSum]
  grw [Finsupp.support_sum, biUnion_subset]
  rintro x hx
  grw [Finsupp.support_sum, biUnion_subset]
exact fun y hy => support_single_subset.trans singleton_subset_iff.2 mem_image₂_of_mem hx hy

@[deprecated (since := "2026-06-18")] alias sup

中文:
定理 support_coeff_mul_subset
  条件: [DecidableEq G] (x y : k[G])
  证明: by
  simp only [MonoidAlgebra.mul_def, coeff_finsuppSum]
  grw [Finsupp.support_sum, biUnion_subset]
  rintro x hx
  grw [Finsupp.support_sum, biUnion_subset]
exact fun y hy => support_single_subset.trans singleton_subset_iff.2 mem_image₂_of_mem hx hy

@[deprecated (since := "2026-06-18")] alias sup

Depends on / 依赖: Finsupp, Finsupp.support_sum, MonoidAlgebra, MonoidAlgebra.mul_def, biUnion_subset, coeff_finsuppSum, mul_def, singleton_subset_iff, support_single_subset, support_single_subset.trans, support_sum
-/
theorem support_coeff_mul_subset [DecidableEq G] (x y : k[G]) :
    (x * y).coeff.support subseteq x.coeff.support * y.coeff.support := by
  simp only [MonoidAlgebra.mul_def, coeff_finsuppSum]
  grw [Finsupp.support_sum, biUnion_subset]
  rintro x hx
  grw [Finsupp.support_sum, biUnion_subset]
exact fun y hy => support_single_subset.trans singleton_subset_iff.2 mem_image₂_of_mem hx hy

@[deprecated (since := "2026-06-18")] alias support_single_mul_eq_image := support_coeff_mul_subset

@[to_additive (dont_translate := k) support_coeff_single_mul_subset]
/--
lemma `support_coeff_single_mul_subset` / 引理 `support_coeff_single_mul_subset`

English:
lemma support_coeff_single_mul_subset
  given: [DecidableEq G] (x : k[G]) (r : k) (a : G)
  proof: by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ subseteq _
  rw [image₂_singleton_left]

@[to_additive (dont_translate := k) support_coeff_mul_single_subset]

中文:
引理 support_coeff_single_mul_subset
  条件: [DecidableEq G] (x : k[G]) (r : k) (a : G)
  证明: by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ subseteq _
  rw [image₂_singleton_left]

@[to_additive (dont_translate := k) support_coeff_mul_single_subset]

Depends on / 依赖: coeff_single, subseteq, support_coeff_mul_subset, support_single_subset
-/
lemma support_coeff_single_mul_subset [DecidableEq G] (x : k[G]) (r : k) (a : G) :
    (single a r * x).coeff.support subseteq x.coeff.support.image (a * ·) := by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ subseteq _
  rw [image₂_singleton_left]

@[to_additive (dont_translate := k) support_coeff_mul_single_subset]
/--
theorem `support_coeff_mul_single_subset` / 定理 `support_coeff_mul_single_subset`

English:
theorem support_coeff_mul_single_subset
  given: [DecidableEq G] (x : k[G]) (r : k) (a : G)
  proof: by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ subseteq _
  rw [image₂_singleton_right]

中文:
定理 support_coeff_mul_single_subset
  条件: [DecidableEq G] (x : k[G]) (r : k) (a : G)
  证明: by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ subseteq _
  rw [image₂_singleton_right]

Depends on / 依赖: coeff_single, subseteq, support_coeff_mul_subset, support_single_subset
-/
theorem support_coeff_mul_single_subset [DecidableEq G] (x : k[G]) (r : k) (a : G) :
    (x * single a r).coeff.support subseteq x.coeff.support.image (· * a) := by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ subseteq _
  rw [image₂_singleton_right]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := k) support_coeff_single_mul_eq_image]
/--
theorem `support_coeff_single_mul_eq_image` / 定理 `support_coeff_single_mul_eq_image`

English:
theorem support_coeff_single_mul_eq_image
  statement: [DecidableEq G] (f : k[G]) {r : k}
  proof: by
  refine subset_antisymm (support_coeff_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a in f.coeff.support, x * a = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, lx.eq_iff]

中文:
定理 support_coeff_single_mul_eq_image
  结论: [DecidableEq G] (f : k[G]) {r : k}
  证明: by
  refine subset_antisymm (support_coeff_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a in f.coeff.support, x * a = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, lx.eq_iff]

Depends on / 依赖: coeff_mul, eq_iff, f.coeff.support, lx.eq_iff, mem_support_iff, mem_support_iff.mp, subset_antisymm, support, support_coeff_single_mul_subset
-/
theorem support_coeff_single_mul_eq_image [DecidableEq G] (f : k[G]) {r : k}
    (hr : forall y, r * y = 0 ↔ y = 0) {x : G} (lx : IsLeftRegular x) :
    (single x r * f).coeff.support = f.coeff.support.image (x * ·) := by
  refine subset_antisymm (support_coeff_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a in f.coeff.support, x * a = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, lx.eq_iff]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := k) support_coeff_mul_single_eq_image]
/--
theorem `support_coeff_mul_single_eq_image` / 定理 `support_coeff_mul_single_eq_image`

English:
theorem support_coeff_mul_single_eq_image
  statement: [DecidableEq G] (f : k[G]) {r : k}
  proof: by
  refine subset_antisymm (support_coeff_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.coeff.support ∧ a * x = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, rx.eq_iff]

@[deprecated (since := "2026-06-18")]
alias support_mul_single_eq_image := s

中文:
定理 support_coeff_mul_single_eq_image
  结论: [DecidableEq G] (f : k[G]) {r : k}
  证明: by
  refine subset_antisymm (support_coeff_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.coeff.support ∧ a * x = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, rx.eq_iff]

@[deprecated (since := "2026-06-18")]
alias support_mul_single_eq_image := s

Depends on / 依赖: coeff_mul, eq_iff, f.coeff.support, mem_support_iff, mem_support_iff.mp, rx.eq_iff, subset_antisymm, support, support_coeff_mul_single_subset
-/
theorem support_coeff_mul_single_eq_image [DecidableEq G] (f : k[G]) {r : k}
    (hr : forall y, y * r = 0 ↔ y = 0) {x : G} (rx : IsRightRegular x) :
    (f * single x r).coeff.support = Finset.image (· * x) f.coeff.support := by
  refine subset_antisymm (support_coeff_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : exists a : G, a in f.coeff.support ∧ a * x = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, rx.eq_iff]

@[deprecated (since := "2026-06-18")]
alias support_mul_single_eq_image := support_coeff_mul_single_eq_image

@[to_additive (dont_translate := k) support_coeff_mul_single]
/--
theorem `support_coeff_mul_single` / 定理 `support_coeff_mul_single`

English:
theorem support_coeff_mul_single
  statement: [IsRightCancelMul G] (f : k[G]) (r : k)
  proof: by
  classical ext; simp [support_coeff_mul_single_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_mul_single := support_coeff_mul_single

@[to_additive (dont_translate := k) support_coeff_single_mul]

中文:
定理 support_coeff_mul_single
  结论: [IsRightCancelMul G] (f : k[G]) (r : k)
  证明: by
  classical ext; simp [support_coeff_mul_single_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_mul_single := support_coeff_mul_single

@[to_additive (dont_translate := k) support_coeff_single_mul]

Depends on / 依赖: classical, support_coeff_mul_single_eq_image
-/
theorem support_coeff_mul_single [IsRightCancelMul G] (f : k[G]) (r : k)
    (hr : forall y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r).coeff.support = f.coeff.support.map (mulRightEmbedding x) := by
  classical ext; simp [support_coeff_mul_single_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_mul_single := support_coeff_mul_single

@[to_additive (dont_translate := k) support_coeff_single_mul]
/--
theorem `support_coeff_single_mul` / 定理 `support_coeff_single_mul`

English:
theorem support_coeff_single_mul
  statement: [IsLeftCancelMul G] (f : k[G]) (r : k)
  proof: by
  classical ext; simp [support_coeff_single_mul_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_single_mul := support_coeff_single_mul

中文:
定理 support_coeff_single_mul
  结论: [IsLeftCancelMul G] (f : k[G]) (r : k)
  证明: by
  classical ext; simp [support_coeff_single_mul_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_single_mul := support_coeff_single_mul

Depends on / 依赖: classical, support_coeff_single_mul_eq_image
-/
theorem support_coeff_single_mul [IsLeftCancelMul G] (f : k[G]) (r : k)
    (hr : forall y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : k[G]).coeff.support =
      f.coeff.support.map (mulLeftEmbedding x) := by
  classical ext; simp [support_coeff_single_mul_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_single_mul := support_coeff_single_mul

end Mul

@[to_additive (dont_translate := k) support_coeff_one_subset]
/--
lemma `support_coeff_one_subset` / 引理 `support_coeff_one_subset`

English:
lemma support_coeff_one_subset
  given: [One G]
  statement: (1 : k[G]).coeff.support subseteq 1
  proof: Finsupp.support_single_subset

@[deprecated (since := "2026-06-18")] alias support_one_subset := support_coeff_one_subset

@[to_additive (dont_translate := k) (attr := simp) support_coeff_one]

中文:
引理 support_coeff_one_subset
  条件: [One G]
  结论: (1 : k[G]).coeff.support subseteq 1
  证明: Finsupp.support_single_subset

@[deprecated (since := "2026-06-18")] alias support_one_subset := support_coeff_one_subset

@[to_additive (dont_translate := k) (attr := simp) support_coeff_one]

Depends on / 依赖: Finsupp, Finsupp.support_single_subset, support_single_subset
-/
lemma support_coeff_one_subset [One G] : (1 : k[G]).coeff.support subseteq 1 :=
  Finsupp.support_single_subset

@[deprecated (since := "2026-06-18")] alias support_one_subset := support_coeff_one_subset

@[to_additive (dont_translate := k) (attr := simp) support_coeff_one]
/--
lemma `support_coeff_one` / 引理 `support_coeff_one`

English:
lemma support_coeff_one
  given: [One G] [NeZero (1 : k)]
  statement: (1 : k[G]).coeff.support = 1
  proof: Finsupp.support_single _ one_ne_zero

@[deprecated (since := "2026-06-18")] alias support_one := support_coeff_one

中文:
引理 support_coeff_one
  条件: [One G] [NeZero (1 : k)]
  结论: (1 : k[G]).coeff.support = 1
  证明: Finsupp.support_single _ one_ne_zero

@[deprecated (since := "2026-06-18")] alias support_one := support_coeff_one

Depends on / 依赖: Finsupp, Finsupp.support_single, one_ne_zero, support_single
-/
lemma support_coeff_one [One G] [NeZero (1 : k)] : (1 : k[G]).coeff.support = 1 :=
  Finsupp.support_single _ one_ne_zero

@[deprecated (since := "2026-06-18")] alias support_one := support_coeff_one

section Span

/--
theorem `mem_span_support_coeff` / 定理 `mem_span_support_coeff`

English:
theorem mem_span_support_coeff
  given: [MulOneClass G] (f : k[G])
  proof: by
  simp [of, ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

中文:
定理 mem_span_support_coeff
  条件: [MulOneClass G] (f : k[G])
  证明: by
  simp [of, ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

Depends on / 依赖: mem_supported, supported_eq_span_single
-/
theorem mem_span_support_coeff [MulOneClass G] (f : k[G]) :
    f in Submodule.span k (of k G '' f.coeff.support) := by
  simp [of, ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

end Span

end MonoidAlgebra

namespace AddMonoidAlgebra

open Finset Finsupp MulOpposite

variable {k : Type u₁} {G : Type u₂} [Semiring k]

section Span

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mem_span_support_coeff` / 定理 `mem_span_support_coeff`

English:
theorem mem_span_support_coeff
  given: (f : k[G])
  statement: f in Submodule.span k (of' k G '' f.coeff.support)
  proof: by
  simp [of', ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

中文:
定理 mem_span_support_coeff
  条件: (f : k[G])
  结论: f in Submodule.span k (of' k G '' f.coeff.support)
  证明: by
  simp [of', ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

Depends on / 依赖: mem_supported, supported_eq_span_single
-/
theorem mem_span_support_coeff (f : k[G]) : f in Submodule.span k (of' k G '' f.coeff.support) := by
  simp [of', ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

end Span

end AddMonoidAlgebra
