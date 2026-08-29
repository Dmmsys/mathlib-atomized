/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Discriminant

/-!

# Field/algebra norm / trace and localization

This file contains results on the combination of `IsLocalization` and `Algebra.norm`,
`Algebra.trace` and `Algebra.discr`.

## Main results

* `Algebra.norm_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R`
  if `S` is free as `R`-module.

* `Algebra.trace_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the trace of `a : Sₘ` over `Rₘ` is the trace of `a : S` over `R`
  if `S` is free as `R`-module.

* `Algebra.discr_localizationLocalization`: let `S` be an extension of `R` and `Rₘ Sₘ` be
  localizations at `M` of `R S` respectively. Let `b` be an `R`-basis of `S`. Then discriminant of
  the `Rₘ`-basis of `Sₘ` induced by `b` is the discriminant of `b`.

## Tags

field norm, algebra norm, localization

-/

public section

open Module
open scoped nonZeroDivisors

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
variable (M : Submonoid R)
variable [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
include M
open Algebra

/--
theorem `Algebra.map_leftMulMatrix_localization` / 定理 `Algebra.map_leftMulMatrix_localization`

English:
theorem Algebra.map_leftMulMatrix_localization
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι]
  proof: by
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, leftMulMatrix_eq_repr_mul, ← map_mul,
    Basis.localizationLocalization_apply, Basis.localizationLocalization_repr_algebraMap]

中文:
定理 代数.map_leftMulMatrix_localization
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι]
  证明: by
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, leftMulMatrix_eq_repr_mul, ← map_mul,
    Basis.localizationLocalization_apply, Basis.localizationLocalization_repr_algebraMap]

Depends on / 依赖: Basis.localizationLocalization_apply, Basis.localizationLocalization_repr_algebraMap, Matrix, Matrix.map_apply, RingHom, RingHom.mapMatrix_apply, leftMulMatrix_eq_repr_mul, localizationLocalization_apply, localizationLocalization_repr_algebraMap, mapMatrix_apply, map_apply, map_mul
-/
theorem Algebra.map_leftMulMatrix_localization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) (a : S) :
    (algebraMap R Rₘ).mapMatrix (leftMulMatrix b a) =
    leftMulMatrix (b.localizationLocalization Rₘ M Sₘ) (algebraMap S Sₘ a) := by
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, leftMulMatrix_eq_repr_mul, ← map_mul,
    Basis.localizationLocalization_apply, Basis.localizationLocalization_repr_algebraMap]

/--
theorem `Algebra.norm_localization` / 定理 `Algebra.norm_localization`

English:
theorem Algebra.norm_localization
  given: [Module.Free R S] [Module.Finite R S] (a : S)
  proof: by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M S

中文:
定理 代数.norm_localization
  条件: [模.自由 R S] [模.有限 R S] (a : S)
  证明: by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M S

Depends on / 依赖: Algebra, Algebra.map_leftMulMatrix_localization, Algebra.norm_eq_matrix_det, ChooseBasisIndex, Classical, Classical.decEq, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Module.subsingleton, RingHom, RingHom.map_det, Subsingleton, b.localizationLocalization, chooseBasis, eq_iff_true_of_subsingleton, localizationLocalization, map_det, map_leftMulMatrix_localization, norm_eq_matrix_det
-/
theorem Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.norm R a) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M Sₘ)]; rw [Algebra.norm_eq_matrix_det b]; rw [RingHom.map_det]; rw [← Algebra.map_leftMulMatrix_localization]

variable {M} in
/--
lemma `Algebra.norm_eq_iff` / 引理 `Algebra.norm_eq_iff`

English:
lemma Algebra.norm_eq_iff
  statement: [Module.Free R S] [Module.Finite R S] {a : S} {b : R}
  proof: ⟨fun h => h.symm ▸ Algebra.norm_localization _ M _, fun h =>
IsLocalization.injective Rₘ hM h.symm ▸ (Algebra.norm_localization R M a).symm⟩

中文:
引理 代数.norm_eq_iff
  结论: [模.自由 R S] [模.有限 R S] {a : S} {b : R}
  证明: ⟨fun h => h.symm ▸ Algebra.norm_localization _ M _, fun h =>
IsLocalization.injective Rₘ hM h.symm ▸ (Algebra.norm_localization R M a).symm⟩

Depends on / 依赖: Algebra, Algebra.norm_localization, IsLocalization, IsLocalization.injective, h.symm, injective, norm_localization
-/
lemma Algebra.norm_eq_iff [Module.Free R S] [Module.Finite R S] {a : S} {b : R}
    (hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔
      (Algebra.norm Rₘ) ((algebraMap S Sₘ) a) = algebraMap R Rₘ b :=
  ⟨fun h => h.symm ▸ Algebra.norm_localization _ M _, fun h =>
IsLocalization.injective Rₘ hM h.symm ▸ (Algebra.norm_localization R M a).symm⟩

/--
theorem `Algebra.trace_localization` / 定理 `Algebra.trace_localization`

English:
theorem Algebra.trace_localization
  given: [Module.Free R S] [Module.Finite R S] (a : S)
  proof: by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.trace_eq_matrix_trace (b.localizationLocalization Rₘ 

中文:
定理 代数.trace_localization
  条件: [模.自由 R S] [模.有限 R S] (a : S)
  证明: by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.trace_eq_matrix_trace (b.localizationLocalization Rₘ 

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_trace, Algebra, Algebra.map_leftMulMatrix_localization, Algebra.trace_eq_matrix_trace, ChooseBasisIndex, Classical, Classical.decEq, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Module.subsingleton, Subsingleton, algebraMap, b.localizationLocalization, chooseBasis, eq_iff_true_of_subsingleton, localizationLocalization, map_leftMulMatrix_localization, map_trace
-/
theorem Algebra.trace_localization [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.trace R S a) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  let := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.trace_eq_matrix_trace (b.localizationLocalization Rₘ M Sₘ)]; rw [Algebra.trace_eq_matrix_trace b]; rw [← Algebra.map_leftMulMatrix_localization]
  exact (AddMonoidHom.map_trace (algebraMap R Rₘ).toAddMonoidHom _).symm

section LocalizationLocalization

variable (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
theorem `Algebra.traceMatrix_localizationLocalization` / 定理 `Algebra.traceMatrix_localizationLocalization`

English:
theorem Algebra.traceMatrix_localizationLocalization
  given: (b : Basis ι R S)
  proof: by
  have : Module.Finite R S := Module.Finite.of_basis b
  have : Module.Free R S := Module.Free.of_basis b
  ext i j : 2
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, traceMatrix_apply, traceForm_apply,
    Basis.localizationLocalization_apply, ← map_mul]
  exact Algebra.trace_localization

中文:
定理 代数.traceMatrix_localizationLocalization
  条件: (b : 基 ι R S)
  证明: by
  have : Module.Finite R S := Module.Finite.of_basis b
  have : Module.Free R S := Module.Free.of_basis b
  ext i j : 2
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, traceMatrix_apply, traceForm_apply,
    Basis.localizationLocalization_apply, ← map_mul]
  exact Algebra.trace_localization

Depends on / 依赖: Algebra, Algebra.trace_localization, Basis.localizationLocalization_apply, Finite, Matrix, Matrix.map_apply, Module, Module.Finite, Module.Finite.of_basis, Module.Free, Module.Free.of_basis, RingHom, RingHom.mapMatrix_apply, localizationLocalization_apply, mapMatrix_apply, map_apply, map_mul, of_basis, simp_rw, traceForm_apply
-/
theorem Algebra.traceMatrix_localizationLocalization (b : Basis ι R S) :
    Algebra.traceMatrix Rₘ (b.localizationLocalization Rₘ M Sₘ) =
      (algebraMap R Rₘ).mapMatrix (Algebra.traceMatrix R b) := by
  have : Module.Finite R S := Module.Finite.of_basis b
  have : Module.Free R S := Module.Free.of_basis b
  ext i j : 2
  simp_rw [RingHom.mapMatrix_apply, Matrix.map_apply, traceMatrix_apply, traceForm_apply,
    Basis.localizationLocalization_apply, ← map_mul]
  exact Algebra.trace_localization R M _

/--
theorem `Algebra.discr_localizationLocalization` / 定理 `Algebra.discr_localizationLocalization`

English:
theorem Algebra.discr_localizationLocalization
  given: (b : Basis ι R S)
  proof: by
  rw [Algebra.discr_def]; rw [Algebra.discr_def]; rw [RingHom.map_det]; rw [Algebra.traceMatrix_localizationLocalization]

中文:
定理 代数.discr_localizationLocalization
  条件: (b : 基 ι R S)
  证明: by
  rw [Algebra.discr_def]; rw [Algebra.discr_def]; rw [RingHom.map_det]; rw [Algebra.traceMatrix_localizationLocalization]

Depends on / 依赖: Algebra, Algebra.discr_def, Algebra.traceMatrix_localizationLocalization, RingHom, RingHom.map_det, discr_def, map_det, traceMatrix_localizationLocalization
-/
theorem Algebra.discr_localizationLocalization (b : Basis ι R S) :
    Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ) =
    algebraMap R Rₘ (Algebra.discr R b) := by
  rw [Algebra.discr_def]; rw [Algebra.discr_def]; rw [RingHom.map_det]; rw [Algebra.traceMatrix_localizationLocalization]

end LocalizationLocalization
