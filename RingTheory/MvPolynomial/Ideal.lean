/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.RingTheory.Ideal.Operations

/-!
# Lemmas about ideals of `MvPolynomial`

Notably this contains results about monomial ideals.

## Main results

* `MvPolynomial.mem_ideal_span_monomial_image`
* `MvPolynomial.mem_ideal_span_X_image`
* `MvPolynomial.mem_pow_idealOfVars_iff`
-/

public section


variable {σ R : Type*}

namespace MvPolynomial

variable [CommSemiring R]

/--
theorem `mem_ideal_span_monomial_image` / 定理 `mem_ideal_span_monomial_image`

English:
theorem mem_ideal_span_monomial_image
  given: {x : MvPolynomial σ R} {s : Set (σ ->₀ Nat)}
  proof: by
  refine AddMonoidAlgebra.mem_ideal_span_of'_image.trans ?_
  simp_rw [le_iff_exists_add, add_comm]
  rfl

中文:
定理 mem_ideal_span_monomial_image
  条件: {x : MvPolynomial σ R} {s : Set (σ ->₀ 自然数)}
  证明: by
  refine AddMonoidAlgebra.mem_ideal_span_of'_image.trans ?_
  simp_rw [le_iff_exists_add, add_comm]
  rfl

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mem_ideal_span_of, _image, _image.trans, add_comm, le_iff_exists_add, mem_ideal_span_of, simp_rw
-/
theorem mem_ideal_span_monomial_image {x : MvPolynomial σ R} {s : Set (σ ->₀ Nat)} :
    x in Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔ forall xi in x.support, exists si in s, si <= xi := by
  refine AddMonoidAlgebra.mem_ideal_span_of'_image.trans ?_
  simp_rw [le_iff_exists_add, add_comm]
  rfl

/--
theorem `mem_ideal_span_monomial_image_iff_dvd` / 定理 `mem_ideal_span_monomial_image_iff_dvd`

English:
theorem mem_ideal_span_monomial_image_iff_dvd
  given: {x : MvPolynomial σ R} {s : Set (σ ->₀ Nat)}
  proof: by
  refine mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => ?_)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true, mem_support_iff.mp hxi, false_or]

中文:
定理 mem_ideal_span_monomial_image_iff_dvd
  条件: {x : MvPolynomial σ R} {s : Set (σ ->₀ 自然数)}
  证明: by
  refine mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => ?_)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true, mem_support_iff.mp hxi, false_or]

Depends on / 依赖: and_true, false_or, mem_ideal_span_monomial_image, mem_ideal_span_monomial_image.trans, mem_support_iff, mem_support_iff.mp, monomial_dvd_monomial, one_dvd, simp_rw
-/
theorem mem_ideal_span_monomial_image_iff_dvd {x : MvPolynomial σ R} {s : Set (σ ->₀ Nat)} :
    x in Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔
      forall xi in x.support, exists si in s, monomial si 1 ∣ monomial xi (x.coeff xi) := by
  refine mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => ?_)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true, mem_support_iff.mp hxi, false_or]

/--
theorem `mem_ideal_span_X_image` / 定理 `mem_ideal_span_X_image`

English:
theorem mem_ideal_span_X_image
  given: {x : MvPolynomial σ R} {s : Set σ}
  proof: by
  have := @mem_ideal_span_monomial_image σ R _ x ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this
  refine this.trans ?_
  simp [Nat.one_le_iff_ne_zero]

中文:
定理 mem_ideal_span_X_image
  条件: {x : MvPolynomial σ R} {s : Set σ}
  证明: by
  have := @mem_ideal_span_monomial_image σ R _ x ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this
  refine this.trans ?_
  simp [Nat.one_le_iff_ne_zero]

Depends on / 依赖: Finsupp, Finsupp.single, Nat.one_le_iff_ne_zero, Set.image_image, image_image, mem_ideal_span_monomial_image, one_le_iff_ne_zero, single, this.trans
-/
theorem mem_ideal_span_X_image {x : MvPolynomial σ R} {s : Set σ} :
    x in Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial σ R)) ↔
      forall m in x.support, exists i in s, (m : σ ->₀ Nat) i != 0 := by
  have := @mem_ideal_span_monomial_image σ R _ x ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this
  refine this.trans ?_
  simp [Nat.one_le_iff_ne_zero]

section idealOfVars

open Finset Finsupp

variable (σ R) in
/--
Definition of `idealOfVars` / `idealOfVars` 的定义

English:
abbreviation idealOfVars
  signature: : Ideal (MvPolynomial σ R)
  body: .span (.range X)

中文:
缩写 idealOfVars
  签名: : Ideal (MvPolynomial σ R)
  定义体: .span (.range X)
-/
noncomputable abbrev idealOfVars : Ideal (MvPolynomial σ R) := .span (.range X)

variable (σ R) in
/--
lemma `idealOfVars_fg` / 引理 `idealOfVars_fg`

English:
lemma idealOfVars_fg
  given: [Finite σ]
  statement: (idealOfVars σ R).FG
  proof: Submodule.fg_span Set.finite_range _

中文:
引理 idealOfVars_fg
  条件: [Finite σ]
  结论: (idealOfVars σ R).FG
  证明: Submodule.fg_span Set.finite_range _

Depends on / 依赖: Set.finite_range, Submodule, Submodule.fg_span, fg_span, finite_range
-/
lemma idealOfVars_fg [Finite σ] : (idealOfVars σ R).FG :=
Submodule.fg_span Set.finite_range _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `idealOfVars_eq_restrictSupportIdeal` / 引理 `idealOfVars_eq_restrictSupportIdeal`

English:
lemma idealOfVars_eq_restrictSupportIdeal
  proof: by
  apply le_antisymm
  · simp [idealOfVars, Ideal.span_le, Set.range_subset_iff, restrictSupportIdeal, X]
  · simp only [SetLike.le_def, restrictSupportIdeal, Submodule.mem_mk, Submodule.mem_toAddSubmonoid,
      ← Submodule.restrictScalars_mem R (idealOfVars σ R)]
    rw [← SetLike.le_def]; rw [r

中文:
引理 idealOfVars_eq_restrictSupportIdeal
  证明: by
  apply le_antisymm
  · simp [idealOfVars, Ideal.span_le, Set.range_subset_iff, restrictSupportIdeal, X]
  · simp only [SetLike.le_def, restrictSupportIdeal, Submodule.mem_mk, Submodule.mem_toAddSubmonoid,
      ← Submodule.restrictScalars_mem R (idealOfVars σ R)]
    rw [← SetLike.le_def]; rw [r

Depends on / 依赖: Ideal.span_le, Nonempty, Set.image_subset_iff, Set.range_subset_iff, SetLike, SetLike.le_def, Submodule, Submodule.mem_mk, Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem, Submodule.span_le, idealOfVars, image_subset_iff, le_antisymm, le_def, le_iff_exists_add, mem_mk, mem_toAddSubmonoid, range_subset_iff, restrictScalars_mem
-/
lemma idealOfVars_eq_restrictSupportIdeal :
    idealOfVars σ R = restrictSupportIdeal _ _ ((isUpperSet_Ici 1).preimage degree_mono) := by
  apply le_antisymm
  · simp [idealOfVars, Ideal.span_le, Set.range_subset_iff, restrictSupportIdeal, X]
  · simp only [SetLike.le_def, restrictSupportIdeal, Submodule.mem_mk, Submodule.mem_toAddSubmonoid,
      ← Submodule.restrictScalars_mem R (idealOfVars σ R)]
    rw [← SetLike.le_def]; rw [restrictSupport_eq_span]; rw [Submodule.span_le]; rw [Set.image_subset_iff]
    intro x hx
    obtain ⟨i, hi⟩ : x.support.Nonempty := by aesop
    obtain ⟨c, rfl⟩ := le_iff_exists_add'.mp (show single i 1 <= x by simp_all; lia)
    simpa [monomial_add_single] using Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

open scoped Pointwise in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `pow_idealOfVars` / 定理 `pow_idealOfVars`

English:
theorem pow_idealOfVars
  given: (n : Nat)
  proof: by
  rw [idealOfVars_eq_restrictSupportIdeal]
  apply Submodule.restrictScalars_injective R
  by_cases hn : n = 0
  · simp [hn, Set.Ici_zero_eq_univ]
  rw [Submodule.restrictScalars_pow hn]
  simp [← restrictSupport_nsmul, ← degree_preimage_nsmul, hn, Set.Ici_nsmul_eq]

中文:
定理 pow_idealOfVars
  条件: (n : 自然数)
  证明: by
  rw [idealOfVars_eq_restrictSupportIdeal]
  apply Submodule.restrictScalars_injective R
  by_cases hn : n = 0
  · simp [hn, Set.Ici_zero_eq_univ]
  rw [Submodule.restrictScalars_pow hn]
  simp [← restrictSupport_nsmul, ← degree_preimage_nsmul, hn, Set.Ici_nsmul_eq]

Depends on / 依赖: Ici_nsmul_eq, Ici_zero_eq_univ, Set.Ici_nsmul_eq, Set.Ici_zero_eq_univ, Submodule, Submodule.restrictScalars_injective, Submodule.restrictScalars_pow, degree_preimage_nsmul, idealOfVars_eq_restrictSupportIdeal, restrictScalars_injective, restrictScalars_pow, restrictSupport_nsmul
-/
theorem pow_idealOfVars (n : Nat) :
    idealOfVars σ R ^ n = restrictSupportIdeal _ _ ((isUpperSet_Ici n).preimage degree_mono) := by
  rw [idealOfVars_eq_restrictSupportIdeal]
  apply Submodule.restrictScalars_injective R
  by_cases hn : n = 0
  · simp [hn, Set.Ici_zero_eq_univ]
  rw [Submodule.restrictScalars_pow hn]
  simp [← restrictSupport_nsmul, ← degree_preimage_nsmul, hn, Set.Ici_nsmul_eq]

/--
theorem `pow_idealOfVars_eq_span` / 定理 `pow_idealOfVars_eq_span`

English:
theorem pow_idealOfVars_eq_span
  given: (n)
  statement: idealOfVars σ R ^ n =
  proof: by
  rw [idealOfVars]; rw [Ideal.span]; rw [Submodule.span_pow]; rw [← Set.image_univ]; rw [image_pow_eq_finsuppProd_image]
  simp [monomial_eq, Set.preimage, degree]

中文:
定理 pow_idealOfVars_eq_span
  条件: (n)
  结论: idealOfVars σ R ^ n =
  证明: by
  rw [idealOfVars]; rw [Ideal.span]; rw [Submodule.span_pow]; rw [← Set.image_univ]; rw [image_pow_eq_finsuppProd_image]
  simp [monomial_eq, Set.preimage, degree]

Depends on / 依赖: Ideal.span, Set.image_univ, Set.preimage, Submodule, Submodule.span_pow, degree, idealOfVars, image_pow_eq_finsuppProd_image, image_univ, monomial_eq, preimage, span_pow
-/
theorem pow_idealOfVars_eq_span (n) : idealOfVars σ R ^ n =
    .span ((monomial · 1) '' degree ⁻¹' {n}) := by
  rw [idealOfVars]; rw [Ideal.span]; rw [Submodule.span_pow]; rw [← Set.image_univ]; rw [image_pow_eq_finsuppProd_image]
  simp [monomial_eq, Set.preimage, degree]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mem_pow_idealOfVars_iff` / 定理 `mem_pow_idealOfVars_iff`

English:
theorem mem_pow_idealOfVars_iff
  given: (n : Nat) (p : MvPolynomial σ R)
  proof: by
  rw [pow_idealOfVars]
  simp [restrictSupportIdeal, mem_restrictSupport_iff, Set.subset_def]

中文:
定理 mem_pow_idealOfVars_iff
  条件: (n : 自然数) (p : MvPolynomial σ R)
  证明: by
  rw [pow_idealOfVars]
  simp [restrictSupportIdeal, mem_restrictSupport_iff, Set.subset_def]

Depends on / 依赖: Set.subset_def, mem_restrictSupport_iff, pow_idealOfVars, restrictSupportIdeal, subset_def
-/
theorem mem_pow_idealOfVars_iff (n : Nat) (p : MvPolynomial σ R) :
    p in idealOfVars σ R ^ n ↔ forall x in p.support, n <= degree x := by
  rw [pow_idealOfVars]
  simp [restrictSupportIdeal, mem_restrictSupport_iff, Set.subset_def]

/--
theorem `mem_pow_idealOfVars_iff'` / 定理 `mem_pow_idealOfVars_iff'`

English:
theorem mem_pow_idealOfVars_iff'
  given: (n : Nat) (p : MvPolynomial σ R)
  proof: by
  grind only [mem_pow_idealOfVars_iff, mem_support_iff]

中文:
定理 mem_pow_idealOfVars_iff'
  条件: (n : 自然数) (p : MvPolynomial σ R)
  证明: by
  grind only [mem_pow_idealOfVars_iff, mem_support_iff]

Depends on / 依赖: mem_pow_idealOfVars_iff, mem_support_iff
-/
theorem mem_pow_idealOfVars_iff' (n : Nat) (p : MvPolynomial σ R) :
    p in idealOfVars σ R ^ n ↔ forall x, degree x < n -> p.coeff x = 0 := by
  grind only [mem_pow_idealOfVars_iff, mem_support_iff]

/--
theorem `monomial_mem_pow_idealOfVars_iff` / 定理 `monomial_mem_pow_idealOfVars_iff`

English:
theorem monomial_mem_pow_idealOfVars_iff
  given: (n : Nat) (x : σ ->₀ Nat) {r : R} (h : r != 0)
  proof: by
  classical
  grind only [mem_pow_idealOfVars_iff, mem_support_iff, coeff_monomial]

中文:
定理 monomial_mem_pow_idealOfVars_iff
  条件: (n : 自然数) (x : σ ->₀ 自然数) {r : R} (h : r != 0)
  证明: by
  classical
  grind only [mem_pow_idealOfVars_iff, mem_support_iff, coeff_monomial]

Depends on / 依赖: classical, coeff_monomial, mem_pow_idealOfVars_iff, mem_support_iff
-/
theorem monomial_mem_pow_idealOfVars_iff (n : Nat) (x : σ ->₀ Nat) {r : R} (h : r != 0) :
    monomial x r in idealOfVars σ R ^ n ↔ n <= degree x := by
  classical
  grind only [mem_pow_idealOfVars_iff, mem_support_iff, coeff_monomial]

/--
theorem `C_mem_pow_idealOfVars_iff` / 定理 `C_mem_pow_idealOfVars_iff`

English:
theorem C_mem_pow_idealOfVars_iff
  given: (n r)
  statement: C r in idealOfVars σ R ^ n ↔ r = 0 ∨ n = 0
  proof: by
  by_cases h : r = 0
  · simp [h]
  simpa [h] using monomial_mem_pow_idealOfVars_iff (σ := σ) n 0 h

中文:
定理 C_mem_pow_idealOfVars_iff
  条件: (n r)
  结论: C r in idealOfVars σ R ^ n ↔ r = 0 ∨ n = 0
  证明: by
  by_cases h : r = 0
  · simp [h]
  simpa [h] using monomial_mem_pow_idealOfVars_iff (σ := σ) n 0 h

Depends on / 依赖: monomial_mem_pow_idealOfVars_iff
-/
theorem C_mem_pow_idealOfVars_iff (n r) : C r in idealOfVars σ R ^ n ↔ r = 0 ∨ n = 0 := by
  by_cases h : r = 0
  · simp [h]
  simpa [h] using monomial_mem_pow_idealOfVars_iff (σ := σ) n 0 h

end idealOfVars

section Quotient

variable {A σ : Type*} [CommRing A] (I : Ideal (MvPolynomial σ A))

/--
theorem `mkₐ_eq_aeval` / 定理 `mkₐ_eq_aeval`

English:
theorem mkₐ_eq_aeval
  proof: by
  ext d
  simp

中文:
定理 mkₐ_eq_aeval
  证明: by
  ext d
  simp
-/
theorem mkₐ_eq_aeval :
    Ideal.Quotient.mkₐ A I = aeval fun d : σ => Ideal.Quotient.mk I (X d) := by
  ext d
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mk_eq_eval₂` / 定理 `mk_eq_eval₂`

English:
theorem mk_eq_eval₂
  statement: (Ideal.Quotient.mk I).toFun =
  proof: by
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← Ideal.Quotient.mkₐ_eq_mk A, mkₐ_eq_aeval, aeval_X, aeval,
    AlgHom.coe_mk, coe_eval₂Hom]

中文:
定理 mk_eq_eval₂
  结论: (Ideal.Quotient.mk I).toFun =
  证明: by
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← Ideal.Quotient.mkₐ_eq_mk A, mkₐ_eq_aeval, aeval_X, aeval,
    AlgHom.coe_mk, coe_eval₂Hom]

Depends on / 依赖: AlgHom, AlgHom.coe_mk, Ideal.Quotient.mk, Quotient, RingHom, RingHom.toFun_eq_coe, aeval_X, coe_mk, simp_rw, toFun_eq_coe
-/
theorem mk_eq_eval₂ : (Ideal.Quotient.mk I).toFun =
      eval₂ (algebraMap A (MvPolynomial σ A ⧸ I)) fun d : σ => Ideal.Quotient.mk I (X d) := by
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← Ideal.Quotient.mkₐ_eq_mk A, mkₐ_eq_aeval, aeval_X, aeval,
    AlgHom.coe_mk, coe_eval₂Hom]

end Quotient

end MvPolynomial

namespace MonomialOrder

variable [CommSemiring R] {m : MonomialOrder σ}
open Ideal

/--
lemma `span_leadingTerm_sdiff_singleton_zero` / 引理 `span_leadingTerm_sdiff_singleton_zero`

English:
lemma span_leadingTerm_sdiff_singleton_zero
  given: (B : Set (MvPolynomial σ R))
  proof: m.image_leadingTerm_sdiff_singleton_zero B ▸ Ideal.span_sdiff_singleton_zero

中文:
引理 span_leadingTerm_sdiff_singleton_zero
  条件: (B : Set (MvPolynomial σ R))
  证明: m.image_leadingTerm_sdiff_singleton_zero B ▸ Ideal.span_sdiff_singleton_zero

Depends on / 依赖: Ideal.span_sdiff_singleton_zero, image_leadingTerm_sdiff_singleton_zero, m.image_leadingTerm_sdiff_singleton_zero, span_sdiff_singleton_zero
-/
lemma span_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    span (m.leadingTerm '' (B \ {0})) = span (m.leadingTerm '' B) :=
  m.image_leadingTerm_sdiff_singleton_zero B ▸ Ideal.span_sdiff_singleton_zero

/--
lemma `span_leadingTerm_insert_zero` / 引理 `span_leadingTerm_insert_zero`

English:
lemma span_leadingTerm_insert_zero
  given: (B : Set (MvPolynomial σ R))
  proof: by
  by_cases h : 0 in B
  · rw [Set.insert_eq_of_mem h]
  · simp [image_leadingTerm_insert_zero]

中文:
引理 span_leadingTerm_insert_zero
  条件: (B : Set (MvPolynomial σ R))
  证明: by
  by_cases h : 0 in B
  · rw [Set.insert_eq_of_mem h]
  · simp [image_leadingTerm_insert_zero]

Depends on / 依赖: Set.insert_eq_of_mem, image_leadingTerm_insert_zero, insert_eq_of_mem
-/
lemma span_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) :
    span (m.leadingTerm '' (insert 0 B)) = span (m.leadingTerm '' B) := by
  by_cases h : 0 in B
  · rw [Set.insert_eq_of_mem h]
  · simp [image_leadingTerm_insert_zero]

/--
lemma `span_leadingTerm_eq_span_monomial` / 引理 `span_leadingTerm_eq_span_monomial`

English:
lemma span_leadingTerm_eq_span_monomial
  statement: {B : Set (MvPolynomial σ R)}
  proof: by
  apply le_antisymm
  all_goals
    rw [Ideal.span_le]; rw [Set.image_subset_iff]
    intro p hp
  · rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hp, rfl⟩)
  · rw [Set.mem_preimage, SetLike.mem_coe]
    conver

中文:
引理 span_leadingTerm_eq_span_monomial
  结论: {B : Set (MvPolynomial σ R)}
  证明: by
  apply le_antisymm
  all_goals
    rw [Ideal.span_le]; rw [Set.image_subset_iff]
    intro p hp
  · rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hp, rfl⟩)
  · rw [Set.mem_preimage, SetLike.mem_coe]
    conver

Depends on / 依赖: C_mul_leadingCoeff_monomial_degree, Ideal.mul_mem_left, Ideal.span_le, Ideal.subset_span, IsUnit, IsUnit.val_inv_mul, MvPolynomi, MvPolynomial, MvPolynomial.C, Set.image_subset_iff, Set.mem_preimage, SetLike, SetLike.mem_coe, all_goals, convert, image_subset_iff, le_antisymm, leadingTerm, m.leadingTerm, map_mul
-/
lemma span_leadingTerm_eq_span_monomial {B : Set (MvPolynomial σ R)}
    (hB : forall p in B, IsUnit (m.leadingCoeff p)) :
    span (m.leadingTerm '' B) =
      span ((fun p => MvPolynomial.monomial (m.degree p) (1 : R)) '' B) := by
  apply le_antisymm
  all_goals
    rw [Ideal.span_le]; rw [Set.image_subset_iff]
    intro p hp
  · rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hp, rfl⟩)
  · rw [Set.mem_preimage, SetLike.mem_coe]
    convert!
(span <| m.leadingTerm '' B).mul_mem_left (MvPolynomial.C (hB p hp).unit⁻¹.val)
        subset_span ⟨p, hp, rfl⟩
    rw [← C_mul_leadingCoeff_monomial_degree]; rw [← mul_assoc]; rw [← map_mul]; rw [IsUnit.val_inv_mul]; rw [MvPolynomial.C_1]; rw [one_mul]

/--
lemma `span_leadingTerm_eq_span_monomial₀` / 引理 `span_leadingTerm_eq_span_monomial₀`

English:
lemma span_leadingTerm_eq_span_monomial₀
  statement: {B : Set (MvPolynomial σ R)}
  proof: by
  rw [← m.span_leadingTerm_sdiff_singleton_zero]
  apply span_leadingTerm_eq_span_monomial
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

中文:
引理 span_leadingTerm_eq_span_monomial₀
  结论: {B : Set (MvPolynomial σ R)}
  证明: by
  rw [← m.span_leadingTerm_sdiff_singleton_zero]
  apply span_leadingTerm_eq_span_monomial
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

Depends on / 依赖: m.span_leadingTerm_sdiff_singleton_zero, or_iff_not_imp_right, or_iff_not_imp_right.mp, simp_intro, span_leadingTerm_eq_span_monomial, span_leadingTerm_sdiff_singleton_zero
-/
lemma span_leadingTerm_eq_span_monomial₀ {B : Set (MvPolynomial σ R)}
    (hB : forall p in B, IsUnit (m.leadingCoeff p) ∨ p = 0) :
    span (m.leadingTerm '' B) =
      span ((fun p => MvPolynomial.monomial (m.degree p) 1) '' (B \ {0})) := by
  rw [← m.span_leadingTerm_sdiff_singleton_zero]
  apply span_leadingTerm_eq_span_monomial
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

/--
lemma `span_leadingTerm_eq_span_monomial'` / 引理 `span_leadingTerm_eq_span_monomial'`

English:
lemma span_leadingTerm_eq_span_monomial'
  given: {k : Type*} [Field k] {B : Set (MvPolynomial σ k)}
  proof: by
  apply span_leadingTerm_eq_span_monomial₀
  simp [em']

中文:
引理 span_leadingTerm_eq_span_monomial'
  条件: {k : 类型} [Field k] {B : Set (MvPolynomial σ k)}
  证明: by
  apply span_leadingTerm_eq_span_monomial₀
  simp [em']
-/
lemma span_leadingTerm_eq_span_monomial' {k : Type*} [Field k] {B : Set (MvPolynomial σ k)} :
    span (m.leadingTerm '' B) =
      span ((fun p => MvPolynomial.monomial (m.degree p) 1) '' (B \ {0})) := by
  apply span_leadingTerm_eq_span_monomial₀
  simp [em']

/--
lemma `sPolynomial_mem_sup_ideal` / 引理 `sPolynomial_mem_sup_ideal`

English:
lemma sPolynomial_mem_sup_ideal
  statement: {R : Type*} [CommRing R]
  proof: sub_mem (mul_mem_left _ _ (mem_sup_left hp)) (mul_mem_left _ _ (mem_sup_right hq))

中文:
引理 sPolynomial_mem_sup_ideal
  结论: {R : 类型} [CommRing R]
  证明: sub_mem (mul_mem_left _ _ (mem_sup_left hp)) (mul_mem_left _ _ (mem_sup_right hq))

Depends on / 依赖: mem_sup_left, mem_sup_right, mul_mem_left, sub_mem
-/
lemma sPolynomial_mem_sup_ideal {R : Type*} [CommRing R]
    {I J : Ideal <| MvPolynomial σ R} {p q : MvPolynomial σ R}
    (hp : p in I) (hq : q in J) : m.sPolynomial p q in I ⊔ J :=
  sub_mem (mul_mem_left _ _ (mem_sup_left hp)) (mul_mem_left _ _ (mem_sup_right hq))

/--
lemma `sPolynomial_mem_ideal` / 引理 `sPolynomial_mem_ideal`

English:
lemma sPolynomial_mem_ideal
  statement: {R : Type*} [CommRing R]
  proof: sub_mem (mul_mem_left I _ hp) (mul_mem_left I _ hq)

中文:
引理 sPolynomial_mem_ideal
  结论: {R : 类型} [CommRing R]
  证明: sub_mem (mul_mem_left I _ hp) (mul_mem_left I _ hq)

Depends on / 依赖: mul_mem_left, sub_mem
-/
lemma sPolynomial_mem_ideal {R : Type*} [CommRing R]
    {I : Ideal <| MvPolynomial σ R} {p q : MvPolynomial σ R}
    (hp : p in I) (hq : q in I) : m.sPolynomial p q in I :=
  sub_mem (mul_mem_left I _ hp) (mul_mem_left I _ hq)

end MonomialOrder
