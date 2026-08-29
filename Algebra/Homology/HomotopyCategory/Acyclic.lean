/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Localization

/-!
# The triangulated subcategory of acyclic complex in the homotopy category

In this file, we define the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of the homotopy category of
cochain complexes in an abelian category `C`.
In the lemma `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W` we obtain
that the class of quasiisomorphisms `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes.

-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

/--
Definition of `subcategoryAcyclic` / `subcategoryAcyclic` 的定义

English:
definition subcategoryAcyclic
  signature: : ObjectProperty (HomotopyCategory C (ComplexShape.up Int))
  body: (homologyFunctor C (ComplexShape.up Int) 0).homologicalKernel

中文:
定义 subcategoryAcyclic
  签名: : ObjectProperty (HomotopyCategory C (余mplexShape.up 整数))
  定义体: (homologyFunctor C (ComplexShape.up Int) 0).homologicalKernel

Depends on / 依赖: ComplexShape, ComplexShape.up, homologicalKernel, homologyFunctor
-/
def subcategoryAcyclic : ObjectProperty (HomotopyCategory C (ComplexShape.up Int)) :=
  (homologyFunctor C (ComplexShape.up Int) 0).homologicalKernel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (subcategoryAcyclic C).IsTriangulated
  body: by
  dsimp [subcategoryAcyclic]
  infer_instance

中文:
实例 :
  签名: (subcategoryAcyclic C).是三角
  定义体: by
  dsimp [subcategoryAcyclic]
  infer_instance

Depends on / 依赖: infer_instance, subcategoryAcyclic
-/
instance : (subcategoryAcyclic C).IsTriangulated := by
  dsimp [subcategoryAcyclic]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (subcategoryAcyclic C).IsClosedUnderIsomorphisms
  body: by
  dsimp [subcategoryAcyclic]
  infer_instance

中文:
实例 :
  签名: (subcategoryAcyclic C).在同构下封闭
  定义体: by
  dsimp [subcategoryAcyclic]
  infer_instance

Depends on / 依赖: infer_instance, subcategoryAcyclic
-/
instance : (subcategoryAcyclic C).IsClosedUnderIsomorphisms := by
  dsimp [subcategoryAcyclic]
  infer_instance

variable {C}

/--
lemma `mem_subcategoryAcyclic_iff` / 引理 `mem_subcategoryAcyclic_iff`

English:
lemma mem_subcategoryAcyclic_iff
  given: (X : HomotopyCategory C (ComplexShape.up Int))
  proof: Functor.mem_homologicalKernel_iff _ X

中文:
引理 mem_subcategoryAcyclic_iff
  条件: (X : HomotopyCategory C (余mplexShape.up 整数))
  证明: Functor.mem_homologicalKernel_iff _ X

Depends on / 依赖: Functor, Functor.mem_homologicalKernel_iff, mem_homologicalKernel_iff
-/
lemma mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up Int)) :
    subcategoryAcyclic C X ↔ forall (n : Int), IsZero ((homologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X

/--
lemma `quotient_obj_mem_subcategoryAcyclic_iff_exactAt` / 引理 `quotient_obj_mem_subcategoryAcyclic_iff_exactAt`

English:
lemma quotient_obj_mem_subcategoryAcyclic_iff_exactAt
  given: (K : CochainComplex C Int)
  proof: by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up Int) n).app K).isZero_iff

中文:
引理 quotient_obj_mem_subcategoryAcyclic_iff_exactAt
  条件: (K : 上链复形 C 整数)
  证明: by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up Int) n).app K).isZero_iff

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, exactAt_iff_isZero_homology, forall_congr, homologyFunctorFactors, isZero_iff, mem_subcategoryAcyclic_iff
-/
lemma quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C Int) :
    subcategoryAcyclic C ((quotient _ _).obj K) ↔ forall (n : Int), K.ExactAt n := by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up Int) n).app K).isZero_iff

/--
lemma `quotient_obj_mem_subcategoryAcyclic_iff_acyclic` / 引理 `quotient_obj_mem_subcategoryAcyclic_iff_acyclic`

English:
lemma quotient_obj_mem_subcategoryAcyclic_iff_acyclic
  given: (K : CochainComplex C Int)
  proof: quotient_obj_mem_subcategoryAcyclic_iff_exactAt _

中文:
引理 quotient_obj_mem_subcategoryAcyclic_iff_acyclic
  条件: (K : 上链复形 C 整数)
  证明: quotient_obj_mem_subcategoryAcyclic_iff_exactAt _

Depends on / 依赖: quotient_obj_mem_subcategoryAcyclic_iff_exactAt
-/
lemma quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C Int) :
    subcategoryAcyclic C ((quotient _ _).obj K) ↔ K.Acyclic :=
  quotient_obj_mem_subcategoryAcyclic_iff_exactAt _

variable (C)

/--
lemma `quasiIso_eq_trW_subcategoryAcyclic` / 引理 `quasiIso_eq_trW_subcategoryAcyclic`

English:
lemma quasiIso_eq_trW_subcategoryAcyclic
  proof: by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up Int) 0).mem_homologicalKernel_trW_iff f).symm

@[deprecated (since := "2026-05-06")] alias quasiIso_eq_subcategoryAcyclic_W :=
  quasiIso_eq_trW_subcategoryAcyclic

中文:
引理 quasiIso_eq_trW_subcategoryAcyclic
  证明: by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up Int) 0).mem_homologicalKernel_trW_iff f).symm

@[deprecated (since := "2026-05-06")] alias quasiIso_eq_subcategoryAcyclic_W :=
  quasiIso_eq_trW_subcategoryAcyclic

Depends on / 依赖: ComplexShape, ComplexShape.up, homologyFunctor, mem_homologicalKernel_trW_iff
-/
lemma quasiIso_eq_trW_subcategoryAcyclic :
    quasiIso C (ComplexShape.up Int) = (subcategoryAcyclic C).trW := by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up Int) 0).mem_homologicalKernel_trW_iff f).symm

@[deprecated (since := "2026-05-06")] alias quasiIso_eq_subcategoryAcyclic_W :=
  quasiIso_eq_trW_subcategoryAcyclic

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso C (ComplexShape.up Int)).IsCompatibleWithShift Int
  body: by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

中文:
实例 :
  签名: (quasiIso C (余mplexShape.up 整数)).是余mpatibleWithShift 整数
  定义体: by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

Depends on / 依赖: infer_instance, quasiIso_eq_trW_subcategoryAcyclic
-/
instance : (quasiIso C (ComplexShape.up Int)).IsCompatibleWithShift Int := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

end HomotopyCategory
