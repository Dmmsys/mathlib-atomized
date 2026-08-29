/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Polynomials supported by a set of variables

This file contains the definition and lemmas about `MvPolynomial.supported`.

## Main definitions

* `MvPolynomial.supported` : Given a set `s : Set σ`, `supported R s` is the subalgebra of
  `MvPolynomial σ R` consisting of polynomials whose set of variables is contained in `s`.
  This subalgebra is isomorphic to `MvPolynomial s R`.

## Tags
variables, polynomial, vars
-/

@[expose] public section


universe u v w

namespace MvPolynomial

variable {σ : Type*} {R : Type u}

section CommSemiring

variable [CommSemiring R] {p : MvPolynomial σ R}

variable (R) in
/--
Definition of `supported` / `supported` 的定义

English:
definition supported
  signature: (s : Set σ)
  body: Algebra.adjoin R (X '' s)

中文:
定义 supported
  签名: (s : 集合 σ)
  定义体: Algebra.adjoin R (X '' s)

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin
-/
noncomputable def supported (s : Set σ) : Subalgebra R (MvPolynomial σ R) :=
  Algebra.adjoin R (X '' s)

open Algebra

set_option backward.isDefEq.respectTransparency false in
/--
theorem `supported_eq_range_rename` / 定理 `supported_eq_range_rename`

English:
theorem supported_eq_range_rename
  given: (s : Set σ)
  statement: supported R s = (rename ((↑) : s -> σ)).range
  proof: by
  rw [supported]; rw [Set.image_eq_range]; rw [adjoin_range_eq_range_aeval]; rw [rename_eq_aeval]
  congr

中文:
定理 supported_eq_range_rename
  条件: (s : 集合 σ)
  结论: supported R s = (rename ((↑) : s -> σ)).range
  证明: by
  rw [supported]; rw [Set.image_eq_range]; rw [adjoin_range_eq_range_aeval]; rw [rename_eq_aeval]
  congr

Depends on / 依赖: Set.image_eq_range, adjoin_range_eq_range_aeval, image_eq_range, rename_eq_aeval, supported
-/
theorem supported_eq_range_rename (s : Set σ) : supported R s = (rename ((↑) : s -> σ)).range := by
  rw [supported]; rw [Set.image_eq_range]; rw [adjoin_range_eq_range_aeval]; rw [rename_eq_aeval]
  congr

/--
Definition of `supportedEquivMvPolynomial` / `supportedEquivMvPolynomial` 的定义

English:
definition supportedEquivMvPolynomial
  signature: (s : Set σ)
  body: (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename ((↑) : s -> σ)) (rename_injective _ Subtype.val_injective)).symm

@[simp]

中文:
定义 supportedEquivMvPolynomial
  签名: (s : 集合 σ)
  定义体: (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename ((↑) : s -> σ)) (rename_injective _ Subtype.val_injective)).symm

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Subalgebra, Subalgebra.equivOfEq, Subtype, Subtype.val_injective, equivOfEq, ofInjective, rename_injective, supported_eq_range_rename, val_injective
-/
noncomputable def supportedEquivMvPolynomial (s : Set σ) : supported R s ≃ₐ[R] MvPolynomial s R :=
  (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename ((↑) : s -> σ)) (rename_injective _ Subtype.val_injective)).symm

@[simp]
/--
theorem `supportedEquivMvPolynomial_symm_C` / 定理 `supportedEquivMvPolynomial_symm_C`

English:
theorem supportedEquivMvPolynomial_symm_C
  given: (s : Set σ) (x : R)
  proof: by
  ext1
  simp [supportedEquivMvPolynomial, MvPolynomial.algebraMap_eq]

@[simp]

中文:
定理 supportedEquivMvPolynomial_symm_C
  条件: (s : 集合 σ) (x : R)
  证明: by
  ext1
  simp [supportedEquivMvPolynomial, MvPolynomial.algebraMap_eq]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.algebraMap_eq, algebraMap_eq, supportedEquivMvPolynomial
-/
theorem supportedEquivMvPolynomial_symm_C (s : Set σ) (x : R) :
    (supportedEquivMvPolynomial s).symm (C x) = algebraMap R (supported R s) x := by
  ext1
  simp [supportedEquivMvPolynomial, MvPolynomial.algebraMap_eq]

@[simp]
/--
theorem `supportedEquivMvPolynomial_symm_X` / 定理 `supportedEquivMvPolynomial_symm_X`

English:
theorem supportedEquivMvPolynomial_symm_X
  given: (s : Set σ) (i : s)
  proof: by
  simp [supportedEquivMvPolynomial]

中文:
定理 supportedEquivMvPolynomial_symm_X
  条件: (s : 集合 σ) (i : s)
  证明: by
  simp [supportedEquivMvPolynomial]

Depends on / 依赖: supportedEquivMvPolynomial
-/
theorem supportedEquivMvPolynomial_symm_X (s : Set σ) (i : s) :
    (↑((supportedEquivMvPolynomial s).symm (X i : MvPolynomial s R)) : MvPolynomial σ R) =
      X ↑i := by
  simp [supportedEquivMvPolynomial]

variable {s t : Set σ}

/--
theorem `mem_supported` / 定理 `mem_supported`

English:
theorem mem_supported
  statement: p in supported R s ↔ ↑p.vars subseteq s
  proof: by
  classical
  rw [supported_eq_range_rename]; rw [AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine _root_.trans (Finset.coe_subset.2 (vars_rename _ _)) ?_
    simp
  · intro hs
    exact exists_rename_eq_of_vars_subset_range p ((↑) : s -> σ) Subtype.val_injective (by simpa)

中文:
定理 mem_supported
  结论: p in supported R s ↔ ↑p.vars subseteq s
  证明: by
  classical
  rw [supported_eq_range_rename]; rw [AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine _root_.trans (Finset.coe_subset.2 (vars_rename _ _)) ?_
    simp
  · intro hs
    exact exists_rename_eq_of_vars_subset_range p ((↑) : s -> σ) Subtype.val_injective (by simpa)

Depends on / 依赖: AlgHom, AlgHom.mem_range, Finset, Finset.coe_subset, Subtype, Subtype.val_injective, _root_, _root_.trans, classical, coe_subset, exists_rename_eq_of_vars_subset_range, mem_range, supported_eq_range_rename, val_injective, vars_rename
-/
theorem mem_supported : p in supported R s ↔ ↑p.vars subseteq s := by
  classical
  rw [supported_eq_range_rename]; rw [AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine _root_.trans (Finset.coe_subset.2 (vars_rename _ _)) ?_
    simp
  · intro hs
    exact exists_rename_eq_of_vars_subset_range p ((↑) : s -> σ) Subtype.val_injective (by simpa)

/--
theorem `supported_eq_vars_subset` / 定理 `supported_eq_vars_subset`

English:
theorem supported_eq_vars_subset
  statement: (supported R s : Set (MvPolynomial σ R)) = { p | ↑p.vars subseteq s }
  proof: Set.ext fun _ => mem_supported

@[simp]

中文:
定理 supported_eq_vars_subset
  结论: (supported R s : 集合 (多元多项式 σ R)) = { p | ↑p.vars subseteq s }
  证明: Set.ext fun _ => mem_supported

@[simp]

Depends on / 依赖: Set.ext, mem_supported
-/
theorem supported_eq_vars_subset : (supported R s : Set (MvPolynomial σ R)) = { p | ↑p.vars subseteq s } :=
  Set.ext fun _ => mem_supported

@[simp]
/--
theorem `mem_supported_vars` / 定理 `mem_supported_vars`

English:
theorem mem_supported_vars
  given: (p : MvPolynomial σ R)
  statement: p in supported R (↑p.vars : Set σ)
  proof: by
  rw [mem_supported]

中文:
定理 mem_supported_vars
  条件: (p : 多元多项式 σ R)
  结论: p in supported R (↑p.vars : 集合 σ)
  证明: by
  rw [mem_supported]

Depends on / 依赖: mem_supported
-/
theorem mem_supported_vars (p : MvPolynomial σ R) : p in supported R (↑p.vars : Set σ) := by
  rw [mem_supported]

variable (s)

/--
theorem `supported_eq_adjoin_X` / 定理 `supported_eq_adjoin_X`

English:
theorem supported_eq_adjoin_X
  statement: supported R s = Algebra.adjoin R (X '' s)
  proof: rfl

@[simp]

中文:
定理 supported_eq_adjoin_X
  结论: supported R s = 代数.adjoin R (X '' s)
  证明: rfl

@[simp]
-/
theorem supported_eq_adjoin_X : supported R s = Algebra.adjoin R (X '' s) := rfl

@[simp]
/--
theorem `supported_univ` / 定理 `supported_univ`

English:
theorem supported_univ
  statement: supported R (Set.univ : Set σ) = ⊤
  proof: by
  simp [Algebra.eq_top_iff, mem_supported]

@[simp]

中文:
定理 supported_univ
  结论: supported R (集合.univ : 集合 σ) = ⊤
  证明: by
  simp [Algebra.eq_top_iff, mem_supported]

@[simp]

Depends on / 依赖: Algebra, Algebra.eq_top_iff, eq_top_iff, mem_supported
-/
theorem supported_univ : supported R (Set.univ : Set σ) = ⊤ := by
  simp [Algebra.eq_top_iff, mem_supported]

@[simp]
/--
theorem `supported_empty` / 定理 `supported_empty`

English:
theorem supported_empty
  statement: supported R (∅ : Set σ) = ⊥
  proof: by simp [supported_eq_adjoin_X]

中文:
定理 supported_empty
  结论: supported R (∅ : 集合 σ) = ⊥
  证明: by simp [supported_eq_adjoin_X]

Depends on / 依赖: supported_eq_adjoin_X
-/
theorem supported_empty : supported R (∅ : Set σ) = ⊥ := by simp [supported_eq_adjoin_X]

variable {s}

/--
theorem `supported_mono` / 定理 `supported_mono`

English:
theorem supported_mono
  given: (st : s subseteq t)
  statement: supported R s <= supported R t
  proof: Algebra.adjoin_mono (Set.image_mono st)

@[simp]

中文:
定理 supported_mono
  条件: (st : s subseteq t)
  结论: supported R s <= supported R t
  证明: Algebra.adjoin_mono (Set.image_mono st)

@[simp]

Depends on / 依赖: Algebra, Algebra.adjoin_mono, Set.image_mono, adjoin_mono, image_mono
-/
theorem supported_mono (st : s subseteq t) : supported R s <= supported R t :=
  Algebra.adjoin_mono (Set.image_mono st)

@[simp]
/--
theorem `X_mem_supported` / 定理 `X_mem_supported`

English:
theorem X_mem_supported
  given: [Nontrivial R] {i : σ}
  statement: X i in supported R s ↔ i in s
  proof: by
  simp [mem_supported]

@[simp]

中文:
定理 X_mem_supported
  条件: [非平凡 R] {i : σ}
  结论: X i in supported R s ↔ i in s
  证明: by
  simp [mem_supported]

@[simp]

Depends on / 依赖: mem_supported
-/
theorem X_mem_supported [Nontrivial R] {i : σ} : X i in supported R s ↔ i in s := by
  simp [mem_supported]

@[simp]
/--
theorem `supported_le_supported_iff` / 定理 `supported_le_supported_iff`

English:
theorem supported_le_supported_iff
  given: [Nontrivial R]
  statement: supported R s <= supported R t ↔ s subseteq t
  proof: by
  constructor
  · intro h i
    simpa using @h (X i)
  · exact supported_mono

中文:
定理 supported_le_supported_iff
  条件: [非平凡 R]
  结论: supported R s <= supported R t ↔ s subseteq t
  证明: by
  constructor
  · intro h i
    simpa using @h (X i)
  · exact supported_mono

Depends on / 依赖: supported_mono
-/
theorem supported_le_supported_iff [Nontrivial R] : supported R s <= supported R t ↔ s subseteq t := by
  constructor
  · intro h i
    simpa using @h (X i)
  · exact supported_mono

/--
theorem `supported_strictMono` / 定理 `supported_strictMono`

English:
theorem supported_strictMono
  given: [Nontrivial R]
  proof: strictMono_of_le_iff_le fun _ _ => supported_le_supported_iff.symm

中文:
定理 supported_strictMono
  条件: [非平凡 R]
  证明: strictMono_of_le_iff_le fun _ _ => supported_le_supported_iff.symm

Depends on / 依赖: strictMono_of_le_iff_le, supported_le_supported_iff, supported_le_supported_iff.symm
-/
theorem supported_strictMono [Nontrivial R] :
    StrictMono (supported R : Set σ -> Subalgebra R (MvPolynomial σ R)) :=
  strictMono_of_le_iff_le fun _ _ => supported_le_supported_iff.symm

/--
theorem `exists_restrict_to_vars` / 定理 `exists_restrict_to_vars`

English:
theorem exists_restrict_to_vars
  statement: (R : Type*) [CommRing R] {F : MvPolynomial σ Int}
  proof: by
  rw [← mem_supported]; rw [supported_eq_range_rename]; rw [AlgHom.mem_range] at hF
  obtain ⟨F', hF'⟩ := hF
  use fun z => aeval z F'
  intro x
  simp only [← hF', aeval_rename]

中文:
定理 存在_restrict_to_vars
  结论: (R : 类型) [交换环 R] {F : 多元多项式 σ 整数}
  证明: by
  rw [← mem_supported]; rw [supported_eq_range_rename]; rw [AlgHom.mem_range] at hF
  obtain ⟨F', hF'⟩ := hF
  use fun z => aeval z F'
  intro x
  simp only [← hF', aeval_rename]

Depends on / 依赖: AlgHom, AlgHom.mem_range, aeval_rename, mem_range, mem_supported, supported_eq_range_rename
-/
theorem exists_restrict_to_vars (R : Type*) [CommRing R] {F : MvPolynomial σ Int}
    (hF : ↑F.vars subseteq s) : exists f : (s -> R) -> R, forall x : σ -> R, f (x ∘ (↑) : s -> R) = aeval x F := by
  rw [← mem_supported]; rw [supported_eq_range_rename]; rw [AlgHom.mem_range] at hF
  obtain ⟨F', hF'⟩ := hF
  use fun z => aeval z F'
  intro x
  simp only [← hF', aeval_rename]

end CommSemiring

end MvPolynomial
