/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Ext

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` for any `R`-linear abelian category `C`
by (left) deriving in the first argument of the bifunctor `(X, Y) ↦ ModuleCat.of R (unop X ⟶ Y)`.

## Implementation

TODO (@joelriou): When the derived category enters mathlib, the Ext groups shall be
redefined using morphisms in the derived category, and then it will be possible to
compute `Ext` using both projective or injective resolutions.

-/

@[expose] public section


noncomputable section

open CategoryTheory Limits

variable (R : Type*) [Ring R] (C : Type*) [Category* C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

/--
Definition of `Ext` / `Ext` 的定义

English:
definition Ext
  signature: (n : Nat)
  body: Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      map := fun f => ((((linearYoneda R C).map f).rightOp).leftDerived n).leftOp }

中文:
定义 Ext
  签名: (n : 自然数)
  定义体: Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      map := fun f => ((((linearYoneda R C).map f).rightOp).leftDerived n).leftOp }

Depends on / 依赖: Functor, Functor.flip, leftDerived, leftOp, linearYoneda, rightOp, rightOp.leftDerived
-/
def Ext (n : Nat) : Cᵒᵖ ⥤ C ⥤ ModuleCat R :=
  Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      map := fun f => ((((linearYoneda R C).map f).rightOp).leftDerived n).leftOp }

open ZeroObject

variable {R C}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given a chain complex `X` and an object `Y`, this is the cochain complex
which in degree `i` consists of the module of morphisms `X.X i ⟶ Y`. -/
@[simps! X d]
/--
Definition of `ChainComplex.linearYonedaObj` / `ChainComplex.linearYonedaObj` 的定义

English:
definition ChainComplex.linearYonedaObj
  signature: {α : Type*} [AddRightCancelSemigroup α] [One α]
  body: ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj X).unop

中文:
定义 链复形.linearYonedaObj
  签名: {α : 类型} [加法右消去半群 α] [幺 α]
  定义体: ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj X).unop

Depends on / 依赖: linearYoneda, mapHomologicalComplex, rightOp, rightOp.mapHomologicalComplex
-/
def ChainComplex.linearYonedaObj {α : Type*} [AddRightCancelSemigroup α] [One α]
    (X : ChainComplex C α) (A : Type*) [Ring A] [Linear A C] (Y : C) :
    CochainComplex (ModuleCat A) α :=
  ((((linearYoneda A C).obj Y).rightOp.mapHomologicalComplex _).obj X).unop

namespace CategoryTheory

namespace ProjectiveResolution

variable {X : C} (P : ProjectiveResolution X)

/--
Definition of `isoExt` / `isoExt` 的定义

English:
definition isoExt
  signature: (n : Nat) (Y : C)
  body: (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).unop.symm ≪≫
    (HomologicalComplex.homologyUnop _ _).symm

中文:
定义 isoExt
  签名: (n : 自然数) (Y : C)
  定义体: (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).unop.symm ≪≫
    (HomologicalComplex.homologyUnop _ _).symm

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyUnop, P.isoLeftDerivedObj, homologyUnop, isoLeftDerivedObj, linearYoneda, rightOp, unop.symm
-/
def isoExt (n : Nat) (Y : C) : ((Ext R C n).obj (Opposite.op X)).obj Y ≅
    (P.complex.linearYonedaObj R Y).homology n :=
  (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).unop.symm ≪≫
    (HomologicalComplex.homologyUnop _ _).symm

end ProjectiveResolution

end CategoryTheory

/--
lemma `isZero_Ext_succ_of_projective` / 引理 `isZero_Ext_succ_of_projective`

English:
lemma isZero_Ext_succ_of_projective
  given: (X Y : C) [Projective X] (n : Nat)
  proof: by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoExt (n + 1) Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]; rw [HomologicalComplex.exactAt_iff]
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  rw [IsZero.iff_id_eq_zero]
  ext (x : _ ⟶ _)
  obtain rfl : x = 0 := (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down Nat) 0 X (n + 1) (by simp)).eq_of_src _ _
  rfl

中文:
引理 isZero_Ext_succ_of_projective
  条件: (X Y : C) [投射 X] (n : 自然数)
  证明: by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoExt (n + 1) Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]; rw [HomologicalComplex.exactAt_iff]
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  rw [IsZero.iff_id_eq_zero]
  ext (x : _ ⟶ _)
  obtain rfl : x = 0 := (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down Nat) 0 X (n + 1) (by simp)).eq_of_src _ _
  rfl

Depends on / 依赖: ComplexShape, ComplexShape.down, HomologicalComplex, HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.isZero_single_obj_X, IsZero, IsZero.iff_id_eq_zero, IsZero.of_iso, ProjectiveResolution, ProjectiveResolution.self, ShortComplex, ShortComplex.exact_of_isZero_X, eq_of_src, exactAt_iff, exactAt_iff_isZero_homology, iff_id_eq_zero, isZero_single_obj_X, isoExt, of_iso
-/
lemma isZero_Ext_succ_of_projective (X Y : C) [Projective X] (n : Nat) :
    IsZero (((Ext R C (n + 1)).obj (Opposite.op X)).obj Y) := by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoExt (n + 1) Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]; rw [HomologicalComplex.exactAt_iff]
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  rw [IsZero.iff_id_eq_zero]
  ext (x : _ ⟶ _)
  obtain rfl : x = 0 := (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down Nat) 0 X (n + 1) (by simp)).eq_of_src _ _
  rfl
