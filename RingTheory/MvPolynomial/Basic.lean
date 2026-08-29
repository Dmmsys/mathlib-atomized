/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.DFinsupp.Small
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Multivariate polynomials over commutative rings

This file contains basic facts about multivariate polynomials over commutative rings, for example
that the monomials form a basis.

## Main definitions

* `restrictTotalDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` of total degree at most `m`.
* `restrictDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` such that the degree in each individual variable is at most `m`.

## Main statements

* The multivariate polynomial ring over a commutative semiring of characteristic `p` has
  characteristic `p`, and similarly for `CharZero`.
* `basisMonomials`: shows that the monomials form a basis of the vector space of multivariate
  polynomials.

## TODO

Generalise to noncommutative (semi)rings
-/

@[expose] public section


noncomputable section

open Set LinearMap Module Submodule

universe u v

variable (σ : Type u) (R : Type v) [CommSemiring R] (p m : Nat)

namespace MvPolynomial

instance {σ R : Type*} [CommSemiring R] [Small.{u} R] [Small.{u} σ] :
    Small.{u} (MvPolynomial σ R) := small_map AddMonoidAlgebra.coeffEquiv

section CharP

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharP
  signature: R p] : CharP (MvPolynomial σ R) p where
  body: by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

中文:
实例 [CharP
  签名: R p] : CharP (MvPolynomial σ R) p where
  定义体: by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

Depends on / 依赖: C_eq_coe_nat, C_inj, CharP.cast_eq_zero_iff, cast_eq_zero_iff
-/
instance [CharP R p] : CharP (MvPolynomial σ R) p where
  cast_eq_zero_iff n := by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

end CharP

section CharZero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharZero
  signature: R] : CharZero (MvPolynomial σ R) where
  body: by rwa [← C_eq_coe_nat, ← C_eq_coe_nat, C_inj, Nat.cast_inj] at hxy

中文:
实例 [CharZero
  签名: R] : CharZero (MvPolynomial σ R) where
  定义体: by rwa [← C_eq_coe_nat, ← C_eq_coe_nat, C_inj, Nat.cast_inj] at hxy

Depends on / 依赖: C_eq_coe_nat, C_inj, Nat.cast_inj, cast_inj
-/
instance [CharZero R] : CharZero (MvPolynomial σ R) where
  cast_injective x y hxy := by rwa [← C_eq_coe_nat, ← C_eq_coe_nat, C_inj, Nat.cast_inj] at hxy

end CharZero

section ExpChar

variable [ExpChar R p]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ExpChar (MvPolynomial σ R) p
  body: by
  cases ‹ExpChar R p›; exacts [ExpChar.zero, ExpChar.prime ‹_›]

中文:
实例 :
  签名: ExpChar (MvPolynomial σ R) p
  定义体: by
  cases ‹ExpChar R p›; exacts [ExpChar.zero, ExpChar.prime ‹_›]

Depends on / 依赖: ExpChar, ExpChar.prime, ExpChar.zero, exacts
-/
instance : ExpChar (MvPolynomial σ R) p := by
  cases ‹ExpChar R p›; exacts [ExpChar.zero, ExpChar.prime ‹_›]

end ExpChar

section Homomorphism

/--
theorem `map_eq_map` / 定理 `map_eq_map`

English:
theorem map_eq_map
  statement: {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
  proof: rfl

@[deprecated (since := "2026-06-18")] alias mapRange_eq_map := map_eq_map

中文:
定理 map_eq_map
  结论: {R S : 类型} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
  证明: rfl

@[deprecated (since := "2026-06-18")] alias mapRange_eq_map := map_eq_map
-/
theorem map_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
    (f : R ->+* S) : AddMonoidAlgebra.map f p = map f p := rfl

@[deprecated (since := "2026-06-18")] alias mapRange_eq_map := map_eq_map

end Homomorphism

section Degree

variable {σ}

/--
Definition of `restrictSupport` / `restrictSupport` 的定义

English:
definition restrictSupport
  signature: (s : Set (σ ->₀ Nat))
  body: AddMonoidAlgebra.supported R R s

中文:
定义 restrictSupport
  签名: (s : Set (σ ->₀ 自然数))
  定义体: AddMonoidAlgebra.supported R R s

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supported, supported
-/
def restrictSupport (s : Set (σ ->₀ Nat)) : Submodule R (MvPolynomial σ R) :=
  AddMonoidAlgebra.supported R R s

/--
Definition of `basisRestrictSupport` / `basisRestrictSupport` 的定义

English:
definition basisRestrictSupport
  signature: (s : Set (σ ->₀ Nat))
  body: AddMonoidAlgebra.supportedEquivFinsupp s

中文:
定义 basisRestrictSupport
  签名: (s : Set (σ ->₀ 自然数))
  定义体: AddMonoidAlgebra.supportedEquivFinsupp s

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supportedEquivFinsupp, supportedEquivFinsupp
-/
def basisRestrictSupport (s : Set (σ ->₀ Nat)) : Basis s R (restrictSupport R s) where
  repr := AddMonoidAlgebra.supportedEquivFinsupp s

/--
theorem `restrictSupport_mono` / 定理 `restrictSupport_mono`

English:
theorem restrictSupport_mono
  given: {s t : Set (σ ->₀ Nat)} (h : s subseteq t)
  proof: AddMonoidAlgebra.supported_mono h

中文:
定理 restrictSupport_mono
  条件: {s t : Set (σ ->₀ 自然数)} (h : s subseteq t)
  证明: AddMonoidAlgebra.supported_mono h

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supported_mono, supported_mono
-/
theorem restrictSupport_mono {s t : Set (σ ->₀ Nat)} (h : s subseteq t) :
    restrictSupport R s <= restrictSupport R t := AddMonoidAlgebra.supported_mono h

/--
lemma `restrictSupport_eq_span` / 引理 `restrictSupport_eq_span`

English:
lemma restrictSupport_eq_span
  given: (s : Set (σ ->₀ Nat))
  proof: AddMonoidAlgebra.supported_eq_span_single ..

中文:
引理 restrictSupport_eq_span
  条件: (s : Set (σ ->₀ 自然数))
  证明: AddMonoidAlgebra.supported_eq_span_single ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supported_eq_span_single, supported_eq_span_single
-/
lemma restrictSupport_eq_span (s : Set (σ ->₀ Nat)) :
    restrictSupport R s = .span _ ((monomial · 1) '' s) :=
  AddMonoidAlgebra.supported_eq_span_single ..

/--
lemma `mem_restrictSupport_iff` / 引理 `mem_restrictSupport_iff`

English:
lemma mem_restrictSupport_iff
  given: {s : Set (σ ->₀ Nat)} {r : MvPolynomial σ R}
  proof: .rfl

@[simp]

中文:
引理 mem_restrictSupport_iff
  条件: {s : Set (σ ->₀ 自然数)} {r : MvPolynomial σ R}
  证明: .rfl

@[simp]
-/
lemma mem_restrictSupport_iff {s : Set (σ ->₀ Nat)} {r : MvPolynomial σ R} :
    r in restrictSupport R s ↔ ↑r.support subseteq s := .rfl

@[simp]
/--
lemma `monomial_mem_restrictSupport` / 引理 `monomial_mem_restrictSupport`

English:
lemma monomial_mem_restrictSupport
  given: {s : Set (σ ->₀ Nat)} {m} {r : R}
  proof: by
  classical
  by_cases r = 0 <;> simp [mem_restrictSupport_iff, support_monomial, *]

中文:
引理 monomial_mem_restrictSupport
  条件: {s : Set (σ ->₀ 自然数)} {m} {r : R}
  证明: by
  classical
  by_cases r = 0 <;> simp [mem_restrictSupport_iff, support_monomial, *]

Depends on / 依赖: classical, mem_restrictSupport_iff, support_monomial
-/
lemma monomial_mem_restrictSupport {s : Set (σ ->₀ Nat)} {m} {r : R} :
    monomial m r in restrictSupport R s ↔ m in s ∨ r = 0 := by
  classical
  by_cases r = 0 <;> simp [mem_restrictSupport_iff, support_monomial, *]

open scoped Pointwise in
/--
lemma `restrictSupport_add` / 引理 `restrictSupport_add`

English:
lemma restrictSupport_add
  given: (s t : Set (σ ->₀ Nat))
  proof: by
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff, Set.add_subset_iff]
    intro x hx y hy
    simp [show monomial (x + y) (1 : R) = monomial x 1 * monomial y 1 by simp, -monomial_mul,
      *, Submodule.mul_mem_mul]
  · rw [restrictSupport_eq_span, rest

中文:
引理 restrictSupport_add
  条件: (s t : Set (σ ->₀ 自然数))
  证明: by
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff, Set.add_subset_iff]
    intro x hx y hy
    simp [show monomial (x + y) (1 : R) = monomial x 1 * monomial y 1 by simp, -monomial_mul,
      *, Submodule.mul_mem_mul]
  · rw [restrictSupport_eq_span, rest

Depends on / 依赖: Set.add_mem_add, Set.add_subset_iff, Set.image_subset_iff, Set.mul_subset_iff, Submodule, Submodule.mul_mem_mul, Submodule.span_le, Submodule.span_mul_span, add_mem_add, add_subset_iff, contextual, image_subset_iff, le_antisymm, monomial, monomial_mul, mul_mem_mul, mul_subset_iff, restrictSupport_eq_span, span_le, span_mul_span
-/
lemma restrictSupport_add (s t : Set (σ ->₀ Nat)) :
    restrictSupport R (s + t) = restrictSupport R s * restrictSupport R t := by
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff, Set.add_subset_iff]
    intro x hx y hy
    simp [show monomial (x + y) (1 : R) = monomial x 1 * monomial y 1 by simp, -monomial_mul,
      *, Submodule.mul_mem_mul]
  · rw [restrictSupport_eq_span, restrictSupport_eq_span, Submodule.span_mul_span,
      Submodule.span_le, Set.mul_subset_iff]
    simp +contextual [Set.add_mem_add]

open scoped Pointwise in
/--
lemma `restrictSupport_zero` / 引理 `restrictSupport_zero`

English:
lemma restrictSupport_zero
  statement: restrictSupport R (0 : Set (σ ->₀ Nat)) = 1
  proof: by
  classical
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    simp only [monomial, AddMonoidAlgebra.lsingle_apply, zero_subset, mem_preimage,
      ← AddMonoidAlgebra.one_def, SetLike.mem_coe, Submodule.mem_one, algebraMap_eq]
    exact ⟨1, by simp⟩

中文:
引理 restrictSupport_zero
  结论: restrictSupport R (0 : Set (σ ->₀ 自然数)) = 1
  证明: by
  classical
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    simp only [monomial, AddMonoidAlgebra.lsingle_apply, zero_subset, mem_preimage,
      ← AddMonoidAlgebra.one_def, SetLike.mem_coe, Submodule.mem_one, algebraMap_eq]
    exact ⟨1, by simp⟩
-/
@[simp] lemma restrictSupport_zero : restrictSupport R (0 : Set (σ ->₀ Nat)) = 1 := by
  classical
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    simp only [monomial, AddMonoidAlgebra.lsingle_apply, zero_subset, mem_preimage,
      ← AddMonoidAlgebra.one_def, SetLike.mem_coe, Submodule.mem_one, algebraMap_eq]
    exact ⟨1, by simp⟩
  · rintro _ ⟨x, rfl⟩
    simp [mem_restrictSupport_iff, subset_def, coeff, AddMonoidAlgebra.one_def,
      Finsupp.single_apply]

@[simp]
/--
lemma `restrictSupport_univ` / 引理 `restrictSupport_univ`

English:
lemma restrictSupport_univ
  statement: restrictSupport R (.univ : Set (σ ->₀ Nat)) = ⊤
  proof: by
  ext; simp [mem_restrictSupport_iff]

中文:
引理 restrictSupport_univ
  结论: restrictSupport R (.univ : Set (σ ->₀ 自然数)) = ⊤
  证明: by
  ext; simp [mem_restrictSupport_iff]

Depends on / 依赖: mem_restrictSupport_iff
-/
lemma restrictSupport_univ : restrictSupport R (.univ : Set (σ ->₀ Nat)) = ⊤ := by
  ext; simp [mem_restrictSupport_iff]

open scoped Pointwise in
/--
lemma `restrictSupport_nsmul` / 引理 `restrictSupport_nsmul`

English:
lemma restrictSupport_nsmul
  given: (n : Nat) (s : Set (σ ->₀ Nat))
  proof: by
  induction n <;> simp [add_smul, restrictSupport_add, *, pow_succ]

中文:
引理 restrictSupport_nsmul
  条件: (n : 自然数) (s : Set (σ ->₀ 自然数))
  证明: by
  induction n <;> simp [add_smul, restrictSupport_add, *, pow_succ]

Depends on / 依赖: add_smul, pow_succ, restrictSupport_add
-/
lemma restrictSupport_nsmul (n : Nat) (s : Set (σ ->₀ Nat)) :
    restrictSupport R (n • s) = restrictSupport R s ^ n := by
  induction n <;> simp [add_smul, restrictSupport_add, *, pow_succ]

/--
Definition of `restrictSupportIdeal` / `restrictSupportIdeal` 的定义

English:
definition restrictSupportIdeal
  signature: (s : Set (σ ->₀ Nat)) (hs : IsUpperSet s)
  body: restrictSupport R s
  smul_mem' x y hy m (hm : m in (x * y).support) := by
    classical
    simp only [mem_support_iff, coeff_mul, ne_eq] at hm
    obtain ⟨⟨i, j⟩, hij, e⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    refine hs (by simp_all [eq_comm]) (hy (show j in y.support by aesop))

中文:
定义 restrictSupportIdeal
  签名: (s : Set (σ ->₀ 自然数)) (hs : IsUpperSet s)
  定义体: restrictSupport R s
  smul_mem' x y hy m (hm : m in (x * y).support) := by
    classical
    simp only [mem_support_iff, coeff_mul, ne_eq] at hm
    obtain ⟨⟨i, j⟩, hij, e⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    refine hs (by simp_all [eq_comm]) (hy (show j in y.support by aesop))

Depends on / 依赖: restrictSupport
-/
def restrictSupportIdeal (s : Set (σ ->₀ Nat)) (hs : IsUpperSet s) :
    Ideal (MvPolynomial σ R) where
  __ := restrictSupport R s
  smul_mem' x y hy m (hm : m in (x * y).support) := by
    classical
    simp only [mem_support_iff, coeff_mul, ne_eq] at hm
    obtain ⟨⟨i, j⟩, hij, e⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    refine hs (by simp_all [eq_comm]) (hy (show j in y.support by aesop))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `restrictScalars_restrictSupportIdeal` / 引理 `restrictScalars_restrictSupportIdeal`

English:
lemma restrictScalars_restrictSupportIdeal
  given: (s : Set (σ ->₀ Nat)) (hs)
  proof: rfl

中文:
引理 restrictScalars_restrictSupportIdeal
  条件: (s : Set (σ ->₀ 自然数)) (hs)
  证明: rfl

Depends on / 依赖: restrictScalars, restrictSupport
-/
lemma restrictScalars_restrictSupportIdeal (s : Set (σ ->₀ Nat)) (hs) :
    (restrictSupportIdeal (R := R) s hs).restrictScalars R = restrictSupport R s :=
  rfl

variable (σ)

/--
Definition of `restrictTotalDegree` / `restrictTotalDegree` 的定义

English:
definition restrictTotalDegree
  signature: (m : Nat)
  body: restrictSupport R { n | (n.sum fun _ e => e) <= m }

中文:
定义 restrictTotalDegree
  签名: (m : 自然数)
  定义体: restrictSupport R { n | (n.sum fun _ e => e) <= m }

Depends on / 依赖: n.sum, restrictSupport
-/
def restrictTotalDegree (m : Nat) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | (n.sum fun _ e => e) <= m }

/--
Definition of `restrictDegree` / `restrictDegree` 的定义

English:
definition restrictDegree
  signature: (m : Nat)
  body: restrictSupport R { n | forall i, n i <= m }

中文:
定义 restrictDegree
  签名: (m : 自然数)
  定义体: restrictSupport R { n | forall i, n i <= m }

Depends on / 依赖: restrictSupport
-/
def restrictDegree (m : Nat) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | forall i, n i <= m }

variable {R}

/--
theorem `mem_restrictTotalDegree` / 定理 `mem_restrictTotalDegree`

English:
theorem mem_restrictTotalDegree
  given: (p : MvPolynomial σ R)
  proof: by
  rw [totalDegree]; rw [Finset.sup_le_iff]
  rfl

中文:
定理 mem_restrictTotalDegree
  条件: (p : MvPolynomial σ R)
  证明: by
  rw [totalDegree]; rw [Finset.sup_le_iff]
  rfl

Depends on / 依赖: Finset, Finset.sup_le_iff, sup_le_iff, totalDegree
-/
theorem mem_restrictTotalDegree (p : MvPolynomial σ R) :
    p in restrictTotalDegree σ R m ↔ p.totalDegree <= m := by
  rw [totalDegree]; rw [Finset.sup_le_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_restrictDegree` / 定理 `mem_restrictDegree`

English:
theorem mem_restrictDegree
  given: (p : MvPolynomial σ R) (n : Nat)
  proof: by
  rw [restrictDegree]; rw [restrictSupport]; rw [AddMonoidAlgebra.mem_supported]
  rfl

中文:
定理 mem_restrictDegree
  条件: (p : MvPolynomial σ R) (n : 自然数)
  证明: by
  rw [restrictDegree]; rw [restrictSupport]; rw [AddMonoidAlgebra.mem_supported]
  rfl

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mem_supported, mem_supported, restrictDegree, restrictSupport
-/
theorem mem_restrictDegree (p : MvPolynomial σ R) (n : Nat) :
    p in restrictDegree σ R n ↔ forall s in p.support, forall i, (s : σ ->₀ Nat) i <= n := by
  rw [restrictDegree]; rw [restrictSupport]; rw [AddMonoidAlgebra.mem_supported]
  rfl

/--
theorem `mem_restrictDegree_iff_sup` / 定理 `mem_restrictDegree_iff_sup`

English:
theorem mem_restrictDegree_iff_sup
  given: [DecidableEq σ] (p : MvPolynomial σ R) (n : Nat)
  proof: by
  simp only [mem_restrictDegree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩

中文:
定理 mem_restrictDegree_iff_sup
  条件: [DecidableEq σ] (p : MvPolynomial σ R) (n : 自然数)
  证明: by
  simp only [mem_restrictDegree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩

Depends on / 依赖: Finset, Finset.sup_le_iff, Finsupp, Finsupp.count_toMultiset, Multiset, Multiset.count_finset_sup, count_finset_sup, count_toMultiset, degrees_def, mem_restrictDegree, sup_le_iff
-/
theorem mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : Nat) :
    p in restrictDegree σ R n ↔ forall i, p.degrees.count i <= n := by
  simp only [mem_restrictDegree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩

variable (R)

/--
theorem `restrictTotalDegree_le_restrictDegree` / 定理 `restrictTotalDegree_le_restrictDegree`

English:
theorem restrictTotalDegree_le_restrictDegree
  given: (m : Nat)
  proof: fun p hp => (mem_restrictDegree _ _ _).mpr fun s hs i => (degreeOf_le_iff.mp
    (degreeOf_le_totalDegree p i) s hs).trans ((mem_restrictTotalDegree _ _ _).mp hp)

中文:
定理 restrictTotalDegree_le_restrictDegree
  条件: (m : 自然数)
  证明: fun p hp => (mem_restrictDegree _ _ _).mpr fun s hs i => (degreeOf_le_iff.mp
    (degreeOf_le_totalDegree p i) s hs).trans ((mem_restrictTotalDegree _ _ _).mp hp)

Depends on / 依赖: degreeOf_le_iff, degreeOf_le_iff.mp, degreeOf_le_totalDegree, mem_restrictDegree, mem_restrictTotalDegree
-/
theorem restrictTotalDegree_le_restrictDegree (m : Nat) :
    restrictTotalDegree σ R m <= restrictDegree σ R m :=
  fun p hp => (mem_restrictDegree _ _ _).mpr fun s hs i => (degreeOf_le_iff.mp
    (degreeOf_le_totalDegree p i) s hs).trans ((mem_restrictTotalDegree _ _ _).mp hp)

/--
Definition of `basisMonomials` / `basisMonomials` 的定义

English:
definition basisMonomials
  signature: : Basis (σ ->₀ Nat) R (MvPolynomial σ R) where
  body: AddMonoidAlgebra.coeffLinearEquiv _

@[simp]

中文:
定义 basisMonomials
  签名: : Basis (σ ->₀ 自然数) R (MvPolynomial σ R) where
  定义体: AddMonoidAlgebra.coeffLinearEquiv _

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffLinearEquiv, coeffLinearEquiv
-/
def basisMonomials : Basis (σ ->₀ Nat) R (MvPolynomial σ R) where
  repr := AddMonoidAlgebra.coeffLinearEquiv _

@[simp]
/--
theorem `coe_basisMonomials` / 定理 `coe_basisMonomials`

English:
theorem coe_basisMonomials
  proof: rfl

中文:
定理 coe_basisMonomials
  证明: rfl
-/
theorem coe_basisMonomials :
    (basisMonomials σ R : (σ ->₀ Nat) -> MvPolynomial σ R) = fun s => monomial s 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R (MvPolynomial σ R)
  body: Module.Free.of_basis (MvPolynomial.basisMonomials σ R)

中文:
实例 :
  签名: Module.Free R (MvPolynomial σ R)
  定义体: Module.Free.of_basis (MvPolynomial.basisMonomials σ R)

Depends on / 依赖: Module, Module.Free.of_basis, MvPolynomial, MvPolynomial.basisMonomials, basisMonomials, of_basis
-/
instance : Module.Free R (MvPolynomial σ R) :=
  Module.Free.of_basis (MvPolynomial.basisMonomials σ R)

/--
theorem `linearIndependent_X` / 定理 `linearIndependent_X`

English:
theorem linearIndependent_X
  statement: LinearIndependent R (X : σ -> MvPolynomial σ R)
  proof: (basisMonomials σ R).linearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)

中文:
定理 linearIndependent_X
  结论: LinearIndependent R (X : σ -> MvPolynomial σ R)
  证明: (basisMonomials σ R).linearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.single_left_injective, basisMonomials, linearIndependent, linearIndependent.comp, one_ne_zero, single, single_left_injective
-/
theorem linearIndependent_X : LinearIndependent R (X : σ -> MvPolynomial σ R) :=
  (basisMonomials σ R).linearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)

/--
lemma `finite_setOfPred_bounded` / 引理 `finite_setOfPred_bounded`

English:
lemma finite_setOfPred_bounded
  given: (α) [Finite α] (n : Nat)
  proof: ((Set.Finite.pi' fun _ => Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype

中文:
引理 finite_setOfPred_bounded
  条件: (α) [Finite α] (n : 自然数)
  证明: ((Set.Finite.pi' fun _ => Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype
-/
private lemma finite_setOfPred_bounded (α) [Finite α] (n : Nat) :
    Finite {f : α ->₀ Nat | forall a, f a <= n} :=
  ((Set.Finite.pi' fun _ => Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: σ] (N
  body: have := finite_setOfPred_bounded σ N
  Module.Finite.of_basis (basisRestrictSupport R _)

中文:
实例 [Finite
  签名: σ] (N
  定义体: have := finite_setOfPred_bounded σ N
  Module.Finite.of_basis (basisRestrictSupport R _)

Depends on / 依赖: Finite, Module, Module.Finite.of_basis, basisRestrictSupport, finite_setOfPred_bounded, of_basis
-/
instance [Finite σ] (N : Nat) : Module.Finite R (restrictDegree σ R N) :=
  have := finite_setOfPred_bounded σ N
  Module.Finite.of_basis (basisRestrictSupport R _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: σ] (N
  body: have := finite_setOfPred_bounded σ N
  have : Finite {s : σ ->₀ Nat | s.sum (fun _ e => e) <= N} := by
    rw [Set.finite_coe_iff] at this ⊢
    exact this.subset fun n hn i => (eq_or_ne (n i) 0).elim
      (fun h => h.trans_le N.zero_le) fun h =>
        (Finset.single_le_sum (fun _ _ => Nat.zero_l

中文:
实例 [Finite
  签名: σ] (N
  定义体: have := finite_setOfPred_bounded σ N
  have : Finite {s : σ ->₀ Nat | s.sum (fun _ e => e) <= N} := by
    rw [Set.finite_coe_iff] at this ⊢
    exact this.subset fun n hn i => (eq_or_ne (n i) 0).elim
      (fun h => h.trans_le N.zero_le) fun h =>
        (Finset.single_le_sum (fun _ _ => Nat.zero_l

Depends on / 依赖: Finite, Finset, Finset.single_le_sum, Finsupp, Finsupp.mem_support_iff.mpr, Module, Module.Finite.of_basis, N.zero_le, Nat.zero_le, Set.finite_coe_iff, basisRestrictSupport, eq_or_ne, finite_coe_iff, finite_setOfPred_bounded, h.trans_le, mem_support_iff, of_basis, s.sum, single_le_sum, subset
-/
instance [Finite σ] (N : Nat) : Module.Finite R (restrictTotalDegree σ R N) :=
  have := finite_setOfPred_bounded σ N
  have : Finite {s : σ ->₀ Nat | s.sum (fun _ e => e) <= N} := by
    rw [Set.finite_coe_iff] at this ⊢
    exact this.subset fun n hn i => (eq_or_ne (n i) 0).elim
      (fun h => h.trans_le N.zero_le) fun h =>
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) <| Finsupp.mem_support_iff.mpr h).trans hn
  Module.Finite.of_basis (basisRestrictSupport R _)

end Degree

end MvPolynomial
