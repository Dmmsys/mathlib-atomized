/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Ext
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Schur's lemma

We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite-dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category* C]
variable [Preadditive C]

-- See also `epi_of_nonzero_to_simple`, which does not require `Preadditive C`.
/--
theorem `mono_of_nonzero_from_simple` / 定理 `mono_of_nonzero_from_simple`

English:
theorem mono_of_nonzero_from_simple
  given: [HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y} (w : f != 0)
  proof: Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)

中文:
定理 mono_of_nonzero_from_simple
  条件: [有Kernels C] {X Y : C} [单 X] {f : X ⟶ Y} (w : f != 0)
  证明: Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)

Depends on / 依赖: Preadditive, Preadditive.mono_of_kernel_zero, kernel_zero_of_nonzero_from_simple, mono_of_kernel_zero
-/
theorem mono_of_nonzero_from_simple [HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y} (w : f != 0) :
    Mono f :=
  Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)

/--
theorem `isIso_of_hom_simple` / 定理 `isIso_of_hom_simple`

English:
theorem isIso_of_hom_simple
  proof: haveI := mono_of_nonzero_from_simple w
  isIso_of_mono_of_nonzero w

中文:
定理 isIso_of_hom_simple
  证明: haveI := mono_of_nonzero_from_simple w
  isIso_of_mono_of_nonzero w

Depends on / 依赖: isIso_of_mono_of_nonzero, mono_of_nonzero_from_simple
-/
theorem isIso_of_hom_simple
    [HasKernels C] {X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f != 0) : IsIso f :=
  haveI := mono_of_nonzero_from_simple w
  isIso_of_mono_of_nonzero w

/--
theorem `isIso_iff_nonzero` / 定理 `isIso_iff_nonzero`

English:
theorem isIso_iff_nonzero
  given: [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X ⟶ Y)
  proof: ⟨fun I => by
    intro h
    apply id_nonzero X
    simp only [← IsIso.hom_inv_id f, h, zero_comp],
   fun w => isIso_of_hom_simple w⟩

中文:
定理 isIso_iff_nonzero
  条件: [有Kernels C] {X Y : C} [单 X] [单 Y] (f : X ⟶ Y)
  证明: ⟨fun I => by
    intro h
    apply id_nonzero X
    simp only [← IsIso.hom_inv_id f, h, zero_comp],
   fun w => isIso_of_hom_simple w⟩

Depends on / 依赖: IsIso.hom_inv_id, hom_inv_id, id_nonzero, isIso_of_hom_simple, zero_comp
-/
theorem isIso_iff_nonzero [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X ⟶ Y) :
    IsIso f ↔ f != 0 :=
  ⟨fun I => by
    intro h
    apply id_nonzero X
    simp only [← IsIso.hom_inv_id f, h, zero_comp],
   fun w => isIso_of_hom_simple w⟩

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasKernels
  signature: C] {X
  body: if h : f = 0 then 0 else haveI := isIso_of_hom_simple h; inv f
  exists_pair_ne := ⟨𝟙 X, 0, id_nonzero _⟩
  inv_zero := dif_pos rfl
  mul_inv_cancel f hf := by
    dsimp
    rw [dif_neg hf]
    have := isIso_of_hom_simple hf
    exact IsIso.inv_hom_id f
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

中文:
实例 [有Kernels
  签名: C] {X
  定义体: if h : f = 0 then 0 else haveI := isIso_of_hom_simple h; inv f
  exists_pair_ne := ⟨𝟙 X, 0, id_nonzero _⟩
  inv_zero := dif_pos rfl
  mul_inv_cancel f hf := by
    dsimp
    rw [dif_neg hf]
    have := isIso_of_hom_simple hf
    exact IsIso.inv_hom_id f
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

Depends on / 依赖: isIso_of_hom_simple
-/
noncomputable instance [HasKernels C] {X : C} [Simple X] : DivisionRing (End X) where
  inv f := if h : f = 0 then 0 else haveI := isIso_of_hom_simple h; inv f
  exists_pair_ne := ⟨𝟙 X, 0, id_nonzero _⟩
  inv_zero := dif_pos rfl
  mul_inv_cancel f hf := by
    dsimp
    rw [dif_neg hf]
    have := isIso_of_hom_simple hf
    exact IsIso.inv_hom_id f
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

open Module

section

variable (𝕜 : Type*) [DivisionRing 𝕜]

/--
theorem `finrank_hom_simple_simple_eq_zero_of_not_iso` / 定理 `finrank_hom_simple_simple_eq_zero_of_not_iso`

English:
theorem finrank_hom_simple_simple_eq_zero_of_not_iso
  statement: [HasKernels C] [Linear 𝕜 C] {X Y : C}
  proof: haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (isIso_iff_nonzero f)
      simp only [Classical.not_not, Ne] at p
      exact p.mp fun _ => h (asIso f)
  finrank_zero_of_subsingleton

中文:
定理 finrank_hom_simple_simple_eq_zero_of_not_iso
  结论: [有Kernels C] [线性 𝕜 C] {X Y : C}
  证明: haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (isIso_iff_nonzero f)
      simp only [Classical.not_not, Ne] at p
      exact p.mp fun _ => h (asIso f)
  finrank_zero_of_subsingleton

Depends on / 依赖: Classical, Classical.not_not, finrank_zero_of_subsingleton, isIso_iff_nonzero, not_congr, not_not, p.mp, subsingleton_of_forall_eq
-/
theorem finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear 𝕜 C] {X Y : C}
    [Simple X] [Simple Y] (h : (X ≅ Y) -> False) : finrank 𝕜 (X ⟶ Y) = 0 :=
  haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (isIso_iff_nonzero f)
      simp only [Classical.not_not, Ne] at p
      exact p.mp fun _ => h (asIso f)
  finrank_zero_of_subsingleton

end

variable (𝕜 : Type*) [Field 𝕜]
variable [IsAlgClosed 𝕜] [Linear 𝕜 C]

set_option backward.isDefEq.respectTransparency false in
-- We prove this with the explicit `isIso_iff_nonzero` assumption,
-- rather than just `[Simple X]`, as this form is useful for
-- Müger's formulation of semisimplicity.
/--
theorem `finrank_endomorphism_eq_one` / 定理 `finrank_endomorphism_eq_one`

English:
theorem finrank_endomorphism_eq_one
  statement: {X : C} (isIso_iff_nonzero : forall f : X ⟶ X, IsIso f ↔ f != 0)
  proof: by
  have id_nonzero := (isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
  refine finrank_eq_one (𝟙 X) id_nonzero ?_
  intro f
  have : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
  have : FiniteDimensional 𝕜 (End X) := I
  obtain ⟨c, nu⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimens

中文:
定理 finrank_endomorphism_eq_one
  结论: {X : C} (isIso_iff_nonzero : 对任意 f : X ⟶ X, 是同构 f ↔ f != 0)
  证明: by
  have id_nonzero := (isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
  refine finrank_eq_one (𝟙 X) id_nonzero ?_
  intro f
  have : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
  have : FiniteDimensional 𝕜 (End X) := I
  obtain ⟨c, nu⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimens

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Classical, Classical.not_not, End.of, FiniteDimensional, IsUnit, IsUnit.sub_iff, Nontrivial, algebraMap_eq_smul_one, finrank_eq_one, id_nonzero, infer_instance, isIso_iff_nonzero, isUnit_iff_isIso, mem_iff, nonempty_of_isAlgClosed_of_finiteDimensional, nontrivial_of_ne, not_not, spectrum
-/
theorem finrank_endomorphism_eq_one {X : C} (isIso_iff_nonzero : forall f : X ⟶ X, IsIso f ↔ f != 0)
    [I : FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ X) = 1 := by
  have id_nonzero := (isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
  refine finrank_eq_one (𝟙 X) id_nonzero ?_
  intro f
  have : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
  have : FiniteDimensional 𝕜 (End X) := I
  obtain ⟨c, nu⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional 𝕜 (End.of f)
  use c
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [isUnit_iff_isIso]; rw [isIso_iff_nonzero]; rw [Ne]; rw [Classical.not_not]; rw [sub_eq_zero]; rw [Algebra.algebraMap_eq_smul_one] at nu
  exact nu.symm

variable [HasKernels C]

/--
theorem `finrank_endomorphism_simple_eq_one` / 定理 `finrank_endomorphism_simple_eq_one`

English:
theorem finrank_endomorphism_simple_eq_one
  given: (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)]
  proof: finrank_endomorphism_eq_one 𝕜 isIso_iff_nonzero

中文:
定理 finrank_endomorphism_simple_eq_one
  条件: (X : C) [单 X] [有限维 𝕜 (X ⟶ X)]
  证明: finrank_endomorphism_eq_one 𝕜 isIso_iff_nonzero

Depends on / 依赖: finrank_endomorphism_eq_one, isIso_iff_nonzero
-/
theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] :
    finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_eq_one 𝕜 isIso_iff_nonzero

/--
theorem `endomorphism_simple_eq_smul_id` / 定理 `endomorphism_simple_eq_smul_id`

English:
theorem endomorphism_simple_eq_smul_id
  statement: {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)]
  proof: (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X)
    f

中文:
定理 endomorphism_simple_eq_smul_id
  结论: {X : C} [单 X] [有限维 𝕜 (X ⟶ X)]
  证明: (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X)
    f

Depends on / 依赖: finrank_endomorphism_simple_eq_one, finrank_eq_one_iff_of_nonzero, id_nonzero
-/
theorem endomorphism_simple_eq_smul_id {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)]
    (f : X ⟶ X) : exists c : 𝕜, c • 𝟙 X = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X)
    f

/-- Endomorphisms of a simple object form a field if they are finite dimensional.
This can't be an instance as `𝕜` would be undetermined.
-/
@[instance_reducible]
/--
Definition of `fieldEndOfFiniteDimensional` / `fieldEndOfFiniteDimensional` 的定义

English:
definition fieldEndOfFiniteDimensional
  signature: (X : C) [Simple X] [I : FiniteDimensional 𝕜 (X ⟶ X)]
  body: by
  exact
    { (inferInstance : DivisionRing (End X)) with
      mul_comm := fun f g => by
        obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 f
        obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 g
        simp [← mul_smul, mul_comm c d] }

中文:
定义 fieldEndOfFiniteDimensional
  签名: (X : C) [单 X] [I : 有限维 𝕜 (X ⟶ X)]
  定义体: by
  exact
    { (inferInstance : DivisionRing (End X)) with
      mul_comm := fun f g => by
        obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 f
        obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 g
        simp [← mul_smul, mul_comm c d] }

Depends on / 依赖: DivisionRing, endomorphism_simple_eq_smul_id, mul_comm, mul_smul
-/
noncomputable def fieldEndOfFiniteDimensional (X : C) [Simple X] [I : FiniteDimensional 𝕜 (X ⟶ X)] :
    Field (End X) := by
  exact
    { (inferInstance : DivisionRing (End X)) with
      mul_comm := fun f g => by
        obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 f
        obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 g
        simp [← mul_smul, mul_comm c d] }

-- There is a symmetric argument that uses `[FiniteDimensional 𝕜 (Y ⟶ Y)]` instead,
-- but we don't bother proving that here.
/--
theorem `finrank_hom_simple_simple_le_one` / 定理 `finrank_hom_simple_simple_le_one`

English:
theorem finrank_hom_simple_simple_le_one
  statement: (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X]
  proof: by
  obtain (h | h) := subsingleton_or_nontrivial (X ⟶ Y)
  · rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h
    have fi := (isIso_iff_nonzero f).mpr nz
    refine finrank_le_one f ?_
    intro g
    obtain ⟨c, w⟩ := endomorphism_simpl

中文:
定理 finrank_hom_simple_simple_le_one
  结论: (X Y : C) [有限维 𝕜 (X ⟶ X)] [单 X]
  证明: by
  obtain (h | h) := subsingleton_or_nontrivial (X ⟶ Y)
  · rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h
    have fi := (isIso_iff_nonzero f).mpr nz
    refine finrank_le_one f ?_
    intro g
    obtain ⟨c, w⟩ := endomorphism_simpl

Depends on / 依赖: endomorphism_simple_eq_smul_id, finrank_le_one, finrank_zero_of_subsingleton, isIso_iff_nonzero, nontrivial_iff_exists_ne, subsingleton_or_nontrivial, zero_le_one
-/
theorem finrank_hom_simple_simple_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X]
    [Simple Y] : finrank 𝕜 (X ⟶ Y) <= 1 := by
  obtain (h | h) := subsingleton_or_nontrivial (X ⟶ Y)
  · rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h
    have fi := (isIso_iff_nonzero f).mpr nz
    refine finrank_le_one f ?_
    intro g
    obtain ⟨c, w⟩ := endomorphism_simple_eq_smul_id 𝕜 (g ≫ inv f)
    exact ⟨c, by simpa using w =≫ f⟩

/--
theorem `finrank_hom_simple_simple_eq_one_iff` / 定理 `finrank_hom_simple_simple_eq_one_iff`

English:
theorem finrank_hom_simple_simple_eq_one_iff
  statement: (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
  proof: by
  fconstructor
  · intro h
    rw [finrank_eq_one_iff'] at h
    obtain ⟨f, nz, -⟩ := h
    rw [← isIso_iff_nonzero] at nz
    exact ⟨asIso f⟩
  · rintro ⟨f⟩
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.

中文:
定理 finrank_hom_simple_simple_eq_one_iff
  结论: (X Y : C) [有限维 𝕜 (X ⟶ X)]
  证明: by
  fconstructor
  · intro h
    rw [finrank_eq_one_iff'] at h
    obtain ⟨f, nz, -⟩ := h
    rw [← isIso_iff_nonzero] at nz
    exact ⟨asIso f⟩
  · rintro ⟨f⟩
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.

Depends on / 依赖: f.hom, fconstructor, finrank, finrank_eq_one_iff, finrank_hom_simple_simple_le_one, finrank_pos_iff_exists_ne_zero, finrank_pos_iff_exists_ne_zero.mpr, isIso_iff_nonzero, le_one, zero_lt
-/
theorem finrank_hom_simple_simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
    [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = 1 ↔ Nonempty (X ≅ Y) := by
  fconstructor
  · intro h
    rw [finrank_eq_one_iff'] at h
    obtain ⟨f, nz, -⟩ := h
    rw [← isIso_iff_nonzero] at nz
    exact ⟨asIso f⟩
  · rintro ⟨f⟩
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (isIso_iff_nonzero f.hom).mp inferInstance⟩
    lia

/--
theorem `finrank_hom_simple_simple_eq_zero_iff` / 定理 `finrank_hom_simple_simple_eq_zero_iff`

English:
theorem finrank_hom_simple_simple_eq_zero_iff
  statement: (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
  proof: by
  rw [← not_nonempty_iff]; rw [← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)]
  have := finrank_hom_simple_simple_le_one 𝕜 X Y
  lia

中文:
定理 finrank_hom_simple_simple_eq_zero_iff
  结论: (X Y : C) [有限维 𝕜 (X ⟶ X)]
  证明: by
  rw [← not_nonempty_iff]; rw [← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)]
  have := finrank_hom_simple_simple_le_one 𝕜 X Y
  lia

Depends on / 依赖: finrank_hom_simple_simple_eq_one_iff, finrank_hom_simple_simple_le_one, not_congr, not_nonempty_iff
-/
theorem finrank_hom_simple_simple_eq_zero_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
    [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = 0 ↔ IsEmpty (X ≅ Y) := by
  rw [← not_nonempty_iff]; rw [← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)]
  have := finrank_hom_simple_simple_le_one 𝕜 X Y
  lia

open scoped Classical in
/--
theorem `finrank_hom_simple_simple` / 定理 `finrank_hom_simple_simple`

English:
theorem finrank_hom_simple_simple
  statement: (X Y : C) [forall X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X]
  proof: by
  split_ifs with h
  · exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h
  · exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h)

中文:
定理 finrank_hom_simple_simple
  结论: (X Y : C) [对任意 X Y : C, 有限维 𝕜 (X ⟶ Y)] [单 X]
  证明: by
  split_ifs with h
  · exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h
  · exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h)

Depends on / 依赖: finrank_hom_simple_simple_eq_one_iff, finrank_hom_simple_simple_eq_zero_iff, not_nonempty_iff, not_nonempty_iff.mp, split_ifs
-/
theorem finrank_hom_simple_simple (X Y : C) [forall X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X]
    [Simple Y] : finrank 𝕜 (X ⟶ Y) = if Nonempty (X ≅ Y) then 1 else 0 := by
  split_ifs with h
  · exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h
  · exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h)

end CategoryTheory
