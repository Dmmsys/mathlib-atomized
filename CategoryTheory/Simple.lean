/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.Atoms

/-!
# Simple objects

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop`-valued typeclass `Simple X`.

In some contexts, especially representation theory, simple objects are called "irreducibles".

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.

We show that any simple object is indecomposable.
-/

public section


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/--
Definition of `Simple` / `Simple` 的定义

English:
class Simple
  parameters: (X : C)
  axioms and operations (1):
    - mono_isIso_iff_nonzero : forall {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f != 0

中文:
类 单
  参数: (X : C)
  公理与运算 (1 个):
    - mono_isIso_iff_nonzero : 对任意 {Y : C} (f : Y ⟶ X) [单态射 f], 是同构 f ↔ f != 0
-/
class Simple (X : C) : Prop where
  mono_isIso_iff_nonzero : forall {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f != 0

/--
theorem `isIso_of_mono_of_nonzero` / 定理 `isIso_of_mono_of_nonzero`

English:
theorem isIso_of_mono_of_nonzero
  given: {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0)
  statement: IsIso f
  proof: (Simple.mono_isIso_iff_nonzero f).mpr w

中文:
定理 isIso_of_mono_of_nonzero
  条件: {X Y : C} [单 Y] {f : X ⟶ Y} [单态射 f] (w : f != 0)
  结论: 是同构 f
  证明: (Simple.mono_isIso_iff_nonzero f).mpr w

Depends on / 依赖: Simple, Simple.mono_isIso_iff_nonzero, mono_isIso_iff_nonzero
-/
theorem isIso_of_mono_of_nonzero {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f != 0) : IsIso f :=
  (Simple.mono_isIso_iff_nonzero f).mpr w

/--
theorem `Functor.simple_of_simple_obj` / 定理 `Functor.simple_of_simple_obj`

English:
theorem Functor.simple_of_simple_obj
  statement: {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
  proof: .mk fun {Y} g _ => by
    rw [← isIso_iff_of_reflects_iso g F]; rw [Simple.mono_isIso_iff_nonzero (F.map g)]; rw [ne_eq]; rw [ne_eq]; rw [not_iff_not]; rw [F.map_eq_zero_iff]

中文:
定理 函子.simple_of_simple_obj
  结论: {D : 类型} [范畴* D] [有ZeroMorphisms D] (F : C ⥤ D)
  证明: .mk fun {Y} g _ => by
    rw [← isIso_iff_of_reflects_iso g F]; rw [Simple.mono_isIso_iff_nonzero (F.map g)]; rw [ne_eq]; rw [ne_eq]; rw [not_iff_not]; rw [F.map_eq_zero_iff]

Depends on / 依赖: F.map, F.map_eq_zero_iff, Simple, Simple.mono_isIso_iff_nonzero, isIso_iff_of_reflects_iso, map_eq_zero_iff, mono_isIso_iff_nonzero, ne_eq, not_iff_not
-/
theorem Functor.simple_of_simple_obj {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesMonomorphisms] [F.PreservesZeroMorphisms] [F.ReflectsIsomorphisms] [F.Faithful]
    (X : C) [Simple (F.obj X)] : Simple X :=
  .mk fun {Y} g _ => by
    rw [← isIso_iff_of_reflects_iso g F]; rw [Simple.mono_isIso_iff_nonzero (F.map g)]; rw [ne_eq]; rw [ne_eq]; rw [not_iff_not]; rw [F.map_eq_zero_iff]

/--
theorem `Simple.of_iso` / 定理 `Simple.of_iso`

English:
theorem Simple.of_iso
  given: {X Y : C} [Simple Y] (i : X ≅ Y)
  statement: Simple X
  proof: { mono_isIso_iff_nonzero := fun f m => by
      constructor
      · intro h w
        have j : IsIso (f ≫ i.hom) := by infer_instance
        rw [Simple.mono_isIso_iff_nonzero] at j
        subst w
        simp at j
      · intro h
        have j : IsIso (f ≫ i.hom) := by
          apply isIso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← Category.comp_id f]; rw [← i.hom_inv_id]; rw [← Category.assoc]
        infer_instance }

中文:
定理 单.of_iso
  条件: {X Y : C} [单 Y] (i : X ≅ Y)
  结论: 单 X
  证明: { mono_isIso_iff_nonzero := fun f m => by
      constructor
      · intro h w
        have j : IsIso (f ≫ i.hom) := by infer_instance
        rw [Simple.mono_isIso_iff_nonzero] at j
        subst w
        simp at j
      · intro h
        have j : IsIso (f ≫ i.hom) := by
          apply isIso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← Category.comp_id f]; rw [← i.hom_inv_id]; rw [← Category.assoc]
        infer_instance }

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Simple, Simple.mono_isIso_iff_nonzero, cancel_mono, comp_id, hom_inv_id, i.hom, i.hom_inv_id, i.inv, infer_instance, isIso_of_mono_of_nonzero, mono_isIso_iff_nonzero
-/
theorem Simple.of_iso {X Y : C} [Simple Y] (i : X ≅ Y) : Simple X :=
  { mono_isIso_iff_nonzero := fun f m => by
      constructor
      · intro h w
        have j : IsIso (f ≫ i.hom) := by infer_instance
        rw [Simple.mono_isIso_iff_nonzero] at j
        subst w
        simp at j
      · intro h
        have j : IsIso (f ≫ i.hom) := by
          apply isIso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← Category.comp_id f]; rw [← i.hom_inv_id]; rw [← Category.assoc]
        infer_instance }

/--
theorem `Simple.iff_of_iso` / 定理 `Simple.iff_of_iso`

English:
theorem Simple.iff_of_iso
  given: {X Y : C} (i : X ≅ Y)
  statement: Simple X ↔ Simple Y
  proof: ⟨fun _ => Simple.of_iso i.symm, fun _ => Simple.of_iso i⟩

中文:
定理 单.iff_of_iso
  条件: {X Y : C} (i : X ≅ Y)
  结论: 单 X ↔ 单 Y
  证明: ⟨fun _ => Simple.of_iso i.symm, fun _ => Simple.of_iso i⟩

Depends on / 依赖: Simple, Simple.of_iso, i.symm, of_iso
-/
theorem Simple.iff_of_iso {X Y : C} (i : X ≅ Y) : Simple X ↔ Simple Y :=
  ⟨fun _ => Simple.of_iso i.symm, fun _ => Simple.of_iso i⟩

/--
theorem `simple_obj` / 定理 `simple_obj`

English:
theorem simple_obj
  statement: {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
  proof: by
  rw [← F.asEquivalence_functor]
  have := F.asEquivalence.counitIso.app (F.asEquivalence.functor.obj X)
  rw [Functor.comp_obj]; rw [Functor.id_obj] at this
have := Simple.of_iso Functor.preimageIso _ this
  exact Functor.simple_of_simple_obj F.asEquivalence.inverse _

中文:
定理 simple_obj
  结论: {D : 类型} [范畴* D] [有ZeroMorphisms D] (F : C ⥤ D)
  证明: by
  rw [← F.asEquivalence_functor]
  have := F.asEquivalence.counitIso.app (F.asEquivalence.functor.obj X)
  rw [Functor.comp_obj]; rw [Functor.id_obj] at this
have := Simple.of_iso Functor.preimageIso _ this
  exact Functor.simple_of_simple_obj F.asEquivalence.inverse _

Depends on / 依赖: F.asEquivalence.counitIso.app, F.asEquivalence.functor.obj, F.asEquivalence.inverse, F.asEquivalence_functor, Functor, Functor.comp_obj, Functor.id_obj, Functor.preimageIso, Functor.simple_of_simple_obj, Simple, Simple.of_iso, asEquivalence, asEquivalence_functor, comp_obj, counitIso, functor, id_obj, inverse, of_iso, preimageIso
-/
theorem simple_obj {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] (X : C) [Simple X] : Simple (F.obj X) := by
  rw [← F.asEquivalence_functor]
  have := F.asEquivalence.counitIso.app (F.asEquivalence.functor.obj X)
  rw [Functor.comp_obj]; rw [Functor.id_obj] at this
have := Simple.of_iso Functor.preimageIso _ this
  exact Functor.simple_of_simple_obj F.asEquivalence.inverse _

/--
theorem `simple_obj_iff` / 定理 `simple_obj_iff`

English:
theorem simple_obj_iff
  statement: {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
  proof: ⟨fun _ => Functor.simple_of_simple_obj F X, fun _ => simple_obj F X⟩

中文:
定理 simple_obj_iff
  结论: {D : 类型} [范畴* D] [有ZeroMorphisms D] (F : C ⥤ D)
  证明: ⟨fun _ => Functor.simple_of_simple_obj F X, fun _ => simple_obj F X⟩

Depends on / 依赖: Functor, Functor.simple_of_simple_obj, simple_obj, simple_of_simple_obj
-/
theorem simple_obj_iff {D : Type*} [Category* D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] (X : C) :
    Simple (F.obj X) ↔ Simple X :=
  ⟨fun _ => Functor.simple_of_simple_obj F X, fun _ => simple_obj F X⟩

/--
theorem `kernel_zero_of_nonzero_from_simple` / 定理 `kernel_zero_of_nonzero_from_simple`

English:
theorem kernel_zero_of_nonzero_from_simple
  statement: {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f]
  proof: by
  by_contra h
  have := isIso_of_mono_of_nonzero h
  exact w (eq_zero_of_epi_kernel f)

中文:
定理 kernel_zero_of_nonzero_from_simple
  结论: {X Y : C} [单 X] {f : X ⟶ Y} [HasKernel f]
  证明: by
  by_contra h
  have := isIso_of_mono_of_nonzero h
  exact w (eq_zero_of_epi_kernel f)

Depends on / 依赖: eq_zero_of_epi_kernel, isIso_of_mono_of_nonzero
-/
theorem kernel_zero_of_nonzero_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f]
    (w : f != 0) : kernel.ι f = 0 := by
  by_contra h
  have := isIso_of_mono_of_nonzero h
  exact w (eq_zero_of_epi_kernel f)

-- See also `mono_of_nonzero_from_simple`, which requires `Preadditive C`.
/--
theorem `epi_of_nonzero_to_simple` / 定理 `epi_of_nonzero_to_simple`

English:
theorem epi_of_nonzero_to_simple
  statement: [HasEqualizers C] {X Y : C} [Simple Y] {f : X ⟶ Y} [HasImage f]
  proof: by
  rw [← image.fac f]
  have : IsIso (image.ι f) := isIso_of_mono_of_nonzero fun h => w (eq_zero_of_image_eq_zero h)
  apply epi_comp

中文:
定理 epi_of_nonzero_to_simple
  结论: [HasEqualizers C] {X Y : C} [单 Y] {f : X ⟶ Y} [有像 f]
  证明: by
  rw [← image.fac f]
  have : IsIso (image.ι f) := isIso_of_mono_of_nonzero fun h => w (eq_zero_of_image_eq_zero h)
  apply epi_comp

Depends on / 依赖: epi_comp, eq_zero_of_image_eq_zero, image.fac, isIso_of_mono_of_nonzero
-/
theorem epi_of_nonzero_to_simple [HasEqualizers C] {X Y : C} [Simple Y] {f : X ⟶ Y} [HasImage f]
    (w : f != 0) : Epi f := by
  rw [← image.fac f]
  have : IsIso (image.ι f) := isIso_of_mono_of_nonzero fun h => w (eq_zero_of_image_eq_zero h)
  apply epi_comp

/--
theorem `mono_to_simple_zero_of_not_iso` / 定理 `mono_to_simple_zero_of_not_iso`

English:
theorem mono_to_simple_zero_of_not_iso
  statement: {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f]
  proof: by
  by_contra h
  exact w (isIso_of_mono_of_nonzero h)

中文:
定理 mono_to_simple_zero_of_not_iso
  结论: {X Y : C} [单 Y] {f : X ⟶ Y} [单态射 f]
  证明: by
  by_contra h
  exact w (isIso_of_mono_of_nonzero h)

Depends on / 依赖: isIso_of_mono_of_nonzero
-/
theorem mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f]
    (w : IsIso f -> False) : f = 0 := by
  by_contra h
  exact w (isIso_of_mono_of_nonzero h)

/--
theorem `id_nonzero` / 定理 `id_nonzero`

English:
theorem id_nonzero
  given: (X : C) [Simple.{v} X]
  statement: 𝟙 X != 0
  proof: (Simple.mono_isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)

中文:
定理 id_nonzero
  条件: (X : C) [单.{v} X]
  结论: 𝟙 X != 0
  证明: (Simple.mono_isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)

Depends on / 依赖: Simple, Simple.mono_isIso_iff_nonzero, infer_instance, mono_isIso_iff_nonzero
-/
theorem id_nonzero (X : C) [Simple.{v} X] : 𝟙 X != 0 :=
  (Simple.mono_isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)

instance (X : C) [Simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 _ (id_nonzero X)

section

/--
theorem `Simple.not_isZero` / 定理 `Simple.not_isZero`

English:
theorem Simple.not_isZero
  given: (X : C) [Simple X]
  statement: ¬IsZero X
  proof: by
  simpa [Limits.IsZero.iff_id_eq_zero] using id_nonzero X

中文:
定理 单.not_isZero
  条件: (X : C) [单 X]
  结论: ¬是零 X
  证明: by
  simpa [Limits.IsZero.iff_id_eq_zero] using id_nonzero X

Depends on / 依赖: IsZero, Limits, Limits.IsZero.iff_id_eq_zero, id_nonzero, iff_id_eq_zero
-/
theorem Simple.not_isZero (X : C) [Simple X] : ¬IsZero X := by
  simpa [Limits.IsZero.iff_id_eq_zero] using id_nonzero X

variable [HasZeroObject C]

open ZeroObject

variable (C)

/--
theorem `zero_not_simple` / 定理 `zero_not_simple`

English:
theorem zero_not_simple
  given: [Simple (0 : C)]
  statement: False
  proof: (Simple.mono_isIso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by simp⟩⟩ rfl

中文:
定理 zero_not_simple
  条件: [单 (0 : C)]
  结论: 假
  证明: (Simple.mono_isIso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by simp⟩⟩ rfl

Depends on / 依赖: Simple, Simple.mono_isIso_iff_nonzero, mono_isIso_iff_nonzero
-/
theorem zero_not_simple [Simple (0 : C)] : False :=
  (Simple.mono_isIso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by simp⟩⟩ rfl

end

end

-- We next make the dual arguments, but for this we must be in an abelian category.
section Abelian

variable [Abelian C]

/--
theorem `simple_of_cosimple` / 定理 `simple_of_cosimple`

English:
theorem simple_of_cosimple
  given: (X : C) (h : forall {Z : C} (f : X ⟶ Z) [Epi f], IsIso f ↔ f != 0)
  proof: ⟨fun {Y} f I => by
    fconstructor
    · intros
      have hx := cokernel.π_of_epi f
      by_contra h
      subst h
      exact (h _).mp inferInstance hx
    · intro hf
      suffices Epi f by exact isIso_of_mono_of_epi _
      apply Preadditive.epi_of_cokernel_zero
      by_contra h'
      exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')⟩

中文:
定理 simple_of_cosimple
  条件: (X : C) (h : 对任意 {Z : C} (f : X ⟶ Z) [满态射 f], 是同构 f ↔ f != 0)
  证明: ⟨fun {Y} f I => by
    fconstructor
    · intros
      have hx := cokernel.π_of_epi f
      by_contra h
      subst h
      exact (h _).mp inferInstance hx
    · intro hf
      suffices Epi f by exact isIso_of_mono_of_epi _
      apply Preadditive.epi_of_cokernel_zero
      by_contra h'
      exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')⟩

Depends on / 依赖: Preadditive, Preadditive.epi_of_cokernel_zero, cokernel, cokernel_not_iso_of_nonzero, epi_of_cokernel_zero, fconstructor, intros, isIso_of_mono_of_epi
-/
theorem simple_of_cosimple (X : C) (h : forall {Z : C} (f : X ⟶ Z) [Epi f], IsIso f ↔ f != 0) :
    Simple X :=
  ⟨fun {Y} f I => by
    fconstructor
    · intros
      have hx := cokernel.π_of_epi f
      by_contra h
      subst h
      exact (h _).mp inferInstance hx
    · intro hf
      suffices Epi f by exact isIso_of_mono_of_epi _
      apply Preadditive.epi_of_cokernel_zero
      by_contra h'
      exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')⟩

/--
theorem `isIso_of_epi_of_nonzero` / 定理 `isIso_of_epi_of_nonzero`

English:
theorem isIso_of_epi_of_nonzero
  given: {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f != 0)
  statement: IsIso f
  proof: -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  haveI : Mono f :=
    Preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  isIso_of_mono_of_epi f

中文:
定理 isIso_of_epi_of_nonzero
  条件: {X Y : C} [单 X] {f : X ⟶ Y} [满态射 f] (w : f != 0)
  结论: 是同构 f
  证明: -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  haveI : Mono f :=
    Preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  isIso_of_mono_of_epi f
-/
theorem isIso_of_epi_of_nonzero {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f != 0) : IsIso f :=
  -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  haveI : Mono f :=
    Preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  isIso_of_mono_of_epi f

/--
theorem `cokernel_zero_of_nonzero_to_simple` / 定理 `cokernel_zero_of_nonzero_to_simple`

English:
theorem cokernel_zero_of_nonzero_to_simple
  given: {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f != 0)
  proof: by
  by_contra h
  have := isIso_of_epi_of_nonzero h
  exact w (eq_zero_of_mono_cokernel f)

中文:
定理 cokernel_zero_of_nonzero_to_simple
  条件: {X Y : C} [单 Y] {f : X ⟶ Y} (w : f != 0)
  证明: by
  by_contra h
  have := isIso_of_epi_of_nonzero h
  exact w (eq_zero_of_mono_cokernel f)

Depends on / 依赖: eq_zero_of_mono_cokernel, isIso_of_epi_of_nonzero
-/
theorem cokernel_zero_of_nonzero_to_simple {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f != 0) :
    cokernel.π f = 0 := by
  by_contra h
  have := isIso_of_epi_of_nonzero h
  exact w (eq_zero_of_mono_cokernel f)

/--
theorem `epi_from_simple_zero_of_not_iso` / 定理 `epi_from_simple_zero_of_not_iso`

English:
theorem epi_from_simple_zero_of_not_iso
  statement: {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f]
  proof: by
  by_contra h
  exact w (isIso_of_epi_of_nonzero h)

中文:
定理 epi_from_simple_zero_of_not_iso
  结论: {X Y : C} [单 X] {f : X ⟶ Y} [满态射 f]
  证明: by
  by_contra h
  exact w (isIso_of_epi_of_nonzero h)

Depends on / 依赖: isIso_of_epi_of_nonzero
-/
theorem epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f]
    (w : IsIso f -> False) : f = 0 := by
  by_contra h
  exact w (isIso_of_epi_of_nonzero h)

end Abelian

section Indecomposable

variable [Preadditive C] [HasBinaryBiproducts C]

-- There are another three potential variations of this lemma,
-- but as any one suffices to prove `indecomposable_of_simple` we will not give them all.
/--
theorem `Biprod.isIso_inl_iff_isZero` / 定理 `Biprod.isIso_inl_iff_isZero`

English:
theorem Biprod.isIso_inl_iff_isZero
  given: (X Y : C)
  statement: IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y
  proof: by
  rw [biprod.isIso_inl_iff_id_eq_fst_comp_inl]; rw [← biprod.total]; rw [add_eq_left]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [← IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
  · intro h
    rw [IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h]; rw [zero_comp]

中文:
定理 Biprod.isIso_inl_iff_isZero
  条件: (X Y : C)
  结论: 是同构 (biprod.inl : X ⟶ X ⊞ Y) ↔ 是零 Y
  证明: by
  rw [biprod.isIso_inl_iff_id_eq_fst_comp_inl]; rw [← biprod.total]; rw [add_eq_left]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [← IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
  · intro h
    rw [IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h]; rw [zero_comp]

Depends on / 依赖: IsZero, IsZero.iff_isSplitEpi_eq_zero, add_eq_left, biprod, biprod.isIso_inl_iff_id_eq_fst_comp_inl, biprod.snd, biprod.total, iff_isSplitEpi_eq_zero, isIso_inl_iff_id_eq_fst_comp_inl, replace, zero_comp
-/
theorem Biprod.isIso_inl_iff_isZero (X Y : C) : IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y := by
  rw [biprod.isIso_inl_iff_id_eq_fst_comp_inl]; rw [← biprod.total]; rw [add_eq_left]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [← IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
  · intro h
    rw [IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h]; rw [zero_comp]

/--
theorem `indecomposable_of_simple` / 定理 `indecomposable_of_simple`

English:
theorem indecomposable_of_simple
  given: (X : C) [Simple X]
  statement: Indecomposable X
  proof: ⟨Simple.not_isZero X, fun Y Z i => by
    refine or_iff_not_imp_left.mpr fun h => ?_
    rw [IsZero.iff_isSplitMono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl != 0 at h
    have : Simple (Y ⊞ Z) := Simple.of_iso i.symm
    rw [← Simple.mono_isIso_iff_nonzero biprod.inl] at h
    rwa [Biprod.isIso_inl_iff_isZero] at h⟩

中文:
定理 indecomposable_of_simple
  条件: (X : C) [单 X]
  结论: Indecomposable X
  证明: ⟨Simple.not_isZero X, fun Y Z i => by
    refine or_iff_not_imp_left.mpr fun h => ?_
    rw [IsZero.iff_isSplitMono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl != 0 at h
    have : Simple (Y ⊞ Z) := Simple.of_iso i.symm
    rw [← Simple.mono_isIso_iff_nonzero biprod.inl] at h
    rwa [Biprod.isIso_inl_iff_isZero] at h⟩

Depends on / 依赖: Biprod, Biprod.isIso_inl_iff_isZero, IsZero, IsZero.iff_isSplitMono_eq_zero, Simple, Simple.mono_isIso_iff_nonzero, Simple.not_isZero, Simple.of_iso, biprod, biprod.inl, i.symm, iff_isSplitMono_eq_zero, isIso_inl_iff_isZero, mono_isIso_iff_nonzero, not_isZero, of_iso, or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
theorem indecomposable_of_simple (X : C) [Simple X] : Indecomposable X :=
  ⟨Simple.not_isZero X, fun Y Z i => by
    refine or_iff_not_imp_left.mpr fun h => ?_
    rw [IsZero.iff_isSplitMono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl != 0 at h
    have : Simple (Y ⊞ Z) := Simple.of_iso i.symm
    rw [← Simple.mono_isIso_iff_nonzero biprod.inl] at h
    rwa [Biprod.isIso_inl_iff_isZero] at h⟩

end Indecomposable

section Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

open Subobject

instance {X : C} [Simple X] : Nontrivial (Subobject X) :=
  nontrivial_of_not_isZero (Simple.not_isZero X)

instance {X : C} [Simple X] : IsSimpleOrder (Subobject X) where
  eq_bot_or_eq_top a := by
    obtain ⟨Y, i, _, rfl⟩ := Subobject.mk_surjective a
    by_cases h : i = 0
    · exact Or.inl (mk_eq_bot_iff_zero.mpr h)
    · exact Or.inr ((isIso_iff_mk_eq_top _).mp ((Simple.mono_isIso_iff_nonzero i).mpr h))

/--
theorem `simple_of_isSimpleOrder_subobject` / 定理 `simple_of_isSimpleOrder_subobject`

English:
theorem simple_of_isSimpleOrder_subobject
  given: (X : C) [IsSimpleOrder (Subobject X)]
  statement: Simple X
  proof: by
  constructor; intro Y f hf; constructor
  · intro i
    rw [Subobject.isIso_iff_mk_eq_top] at i
    intro w
    rw [← Subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (Subobject.mk f) with (h | h)
    · rw [Subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
    · exact (Subobject.isIso_iff_mk_eq_top _).mpr h

中文:
定理 simple_of_isSimpleOrder_subobject
  条件: (X : C) [是单序 (Subobject X)]
  结论: 单 X
  证明: by
  constructor; intro Y f hf; constructor
  · intro i
    rw [Subobject.isIso_iff_mk_eq_top] at i
    intro w
    rw [← Subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (Subobject.mk f) with (h | h)
    · rw [Subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
    · exact (Subobject.isIso_iff_mk_eq_top _).mpr h

Depends on / 依赖: False.elim, IsSimpleOrder, IsSimpleOrder.bot_ne_top, IsSimpleOrder.eq_bot_or_eq_top, Subobject, Subobject.isIso_iff_mk_eq_top, Subobject.mk, Subobject.mk_eq_bot_iff_zero, bot_ne_top, eq_bot_or_eq_top, isIso_iff_mk_eq_top, mk_eq_bot_iff_zero, w.symm.trans
-/
theorem simple_of_isSimpleOrder_subobject (X : C) [IsSimpleOrder (Subobject X)] : Simple X := by
  constructor; intro Y f hf; constructor
  · intro i
    rw [Subobject.isIso_iff_mk_eq_top] at i
    intro w
    rw [← Subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (Subobject.mk f) with (h | h)
    · rw [Subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
    · exact (Subobject.isIso_iff_mk_eq_top _).mpr h

/--
theorem `simple_iff_subobject_isSimpleOrder` / 定理 `simple_iff_subobject_isSimpleOrder`

English:
theorem simple_iff_subobject_isSimpleOrder
  given: (X : C)
  statement: Simple X ↔ IsSimpleOrder (Subobject X)
  proof: ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_isSimpleOrder_subobject X⟩

中文:
定理 simple_iff_subobject_isSimpleOrder
  条件: (X : C)
  结论: 单 X ↔ 是单序 (Subobject X)
  证明: ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_isSimpleOrder_subobject X⟩

Depends on / 依赖: infer_instance, simple_of_isSimpleOrder_subobject
-/
theorem simple_iff_subobject_isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Subobject X) :=
  ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_isSimpleOrder_subobject X⟩

/--
theorem `subobject_simple_iff_isAtom` / 定理 `subobject_simple_iff_isAtom`

English:
theorem subobject_simple_iff_isAtom
  given: {X : C} (Y : Subobject X)
  statement: Simple (Y : C) ↔ IsAtom Y
  proof: (simple_iff_subobject_isSimpleOrder _).trans
    ((OrderIso.isSimpleOrder_iff (subobjectOrderIso Y)).trans Set.isSimpleOrder_Iic_iff_isAtom)

中文:
定理 subobject_simple_iff_isAtom
  条件: {X : C} (Y : Subobject X)
  结论: 单 (Y : C) ↔ IsAtom Y
  证明: (simple_iff_subobject_isSimpleOrder _).trans
    ((OrderIso.isSimpleOrder_iff (subobjectOrderIso Y)).trans Set.isSimpleOrder_Iic_iff_isAtom)

Depends on / 依赖: OrderIso, OrderIso.isSimpleOrder_iff, Set.isSimpleOrder_Iic_iff_isAtom, isSimpleOrder_Iic_iff_isAtom, isSimpleOrder_iff, simple_iff_subobject_isSimpleOrder, subobjectOrderIso
-/
theorem subobject_simple_iff_isAtom {X : C} (Y : Subobject X) : Simple (Y : C) ↔ IsAtom Y :=
  (simple_iff_subobject_isSimpleOrder _).trans
    ((OrderIso.isSimpleOrder_iff (subobjectOrderIso Y)).trans Set.isSimpleOrder_Iic_iff_isAtom)

end Subobject

end CategoryTheory
