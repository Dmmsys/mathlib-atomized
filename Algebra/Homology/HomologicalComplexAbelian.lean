/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # THe category of homological complexes is abelian

If `C` is an abelian category, then `HomologicalComplex C c` is an abelian
category for any complex shape `c : ComplexShape ι`.

We also obtain that a short complex in `HomologicalComplex C c`
is exact (resp. short exact) iff degreewise it is so.

-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι : Type*} {c : ComplexShape ι} [Category* C]

section

variable [Abelian C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNormalEpiCategory (HomologicalComplex C c)
  body: ⟨fun p _ =>
  ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩⟩

中文:
实例 :
  签名: 是正规满态射范畴 (同调复形 C c)
  定义体: ⟨fun p _ =>
  ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩⟩
-/
noncomputable instance : IsNormalEpiCategory (HomologicalComplex C c) := ⟨fun p _ =>
  ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNormalMonoCategory (HomologicalComplex C c)
  body: ⟨fun p _ =>
  ⟨NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩⟩

中文:
实例 :
  签名: 是正规单态射范畴 (同调复形 C c)
  定义体: ⟨fun p _ =>
  ⟨NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩⟩
-/
noncomputable instance : IsNormalMonoCategory (HomologicalComplex C c) := ⟨fun p _ =>
  ⟨NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (HomologicalComplex C c)

中文:
实例 :
  签名: 交换 (同调复形 C c)
-/
noncomputable instance : Abelian (HomologicalComplex C c) where

variable (S : ShortComplex (HomologicalComplex C c))

/--
lemma `exact_of_degreewise_exact` / 引理 `exact_of_degreewise_exact`

English:
lemma exact_of_degreewise_exact
  given: (hS : forall (i : ι), (S.map (eval C c i)).Exact)
  proof: by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src

中文:
引理 exact_of_degreewise_exact
  条件: (hS : 对任意 (i : ι), (S.map (eval C c i)).正合)
  证明: by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, IsZero.of_iso, S.mapHomologyIso, ShortComplex, ShortComplex.exact_iff_isZero_homology, eq_of_src, exact_iff_isZero_homology, iff_id_eq_zero, infer_instance, mapHomologyIso, of_iso, quasiIso_shift_iff
-/
lemma exact_of_degreewise_exact (hS : forall (i : ι), (S.map (eval C c i)).Exact) :
    S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src

/--
lemma `shortExact_of_degreewise_shortExact` / 引理 `shortExact_of_degreewise_shortExact`

English:
lemma shortExact_of_degreewise_shortExact
  proof: mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)

中文:
引理 shortExact_of_degreewise_shortExact
  证明: mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)

Depends on / 依赖: mono_f, mono_of_mono_f
-/
lemma shortExact_of_degreewise_shortExact
    (hS : forall (i : ι), (S.map (eval C c i)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)

/--
lemma `exact_iff_degreewise_exact` / 引理 `exact_iff_degreewise_exact`

English:
lemma exact_iff_degreewise_exact
  proof: by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact exact_of_degreewise_exact S

中文:
引理 exact_iff_degreewise_exact
  证明: by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact exact_of_degreewise_exact S

Depends on / 依赖: exact_of_degreewise_exact, hS.map
-/
lemma exact_iff_degreewise_exact :
    S.Exact ↔ forall (i : ι), (S.map (eval C c i)).Exact := by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact exact_of_degreewise_exact S

/--
lemma `shortExact_iff_degreewise_shortExact` / 引理 `shortExact_iff_degreewise_shortExact`

English:
lemma shortExact_iff_degreewise_shortExact
  proof: by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact shortExact_of_degreewise_shortExact S

中文:
引理 shortExact_iff_degreewise_shortExact
  证明: by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact shortExact_of_degreewise_shortExact S

Depends on / 依赖: epi_g, hS.epi_g, hS.map, hS.mono_f, mono_f, shortExact_of_degreewise_shortExact
-/
lemma shortExact_iff_degreewise_shortExact :
    S.ShortExact ↔ forall (i : ι), (S.map (eval C c i)).ShortExact := by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact shortExact_of_degreewise_shortExact S

end

section

variable [HasZeroMorphisms C] [HasZeroObject C] [DecidableEq ι]

instance (i j : ι) (I : C) [Injective I] :
    Injective (((single C c i).obj I).X j) := by
  by_cases hij : j = i
  · subst hij
    simp only [single_obj_X_self]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hij).injective

instance (i j : ι) (P : C) [Projective P] :
    Projective (((single C c i).obj P).X j) := by
  by_cases hij : j = i
  · subst hij
    simp only [single_obj_X_self]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hij).projective

end

end HomologicalComplex

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
variable {D : Type*} [Category* D] [HasZeroMorphisms D]

variable (F : C ⥤ D) {ι : Type*} (c : ComplexShape ι)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.PreservesZeroMorphisms]
  signature: {J : Type*} [Category* J] [HasLimitsOfShape J C]
  body: HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i =>
inferInstanceAs PreservesLimitsOfShape J HomologicalComplex.eval C c i ⋙ F)

中文:
实例 [F.保持ZeroMorphisms]
  签名: {J : 类型} [范畴* J] [有形状极限 J C]
  定义体: HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i =>
inferInstanceAs PreservesLimitsOfShape J HomologicalComplex.eval C c i ⋙ F)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, HomologicalComplex.preservesLimitsOfShape_of_eval, PreservesLimitsOfShape, preservesLimitsOfShape_of_eval
-/
instance [F.PreservesZeroMorphisms] {J : Type*} [Category* J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i =>
inferInstanceAs PreservesLimitsOfShape J HomologicalComplex.eval C c i ⋙ F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.PreservesZeroMorphisms]
  signature: {J : Type*} [Category* J] [HasColimitsOfShape J C]
  body: HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i =>
inferInstanceAs PreservesColimitsOfShape J HomologicalComplex.eval C c i ⋙ F)

中文:
实例 [F.保持ZeroMorphisms]
  签名: {J : 类型} [范畴* J] [有形状余极限 J C]
  定义体: HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i =>
inferInstanceAs PreservesColimitsOfShape J HomologicalComplex.eval C c i ⋙ F)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, HomologicalComplex.preservesColimitsOfShape_of_eval, PreservesColimitsOfShape, preservesColimitsOfShape_of_eval
-/
instance [F.PreservesZeroMorphisms] {J : Type*} [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i =>
inferInstanceAs PreservesColimitsOfShape J HomologicalComplex.eval C c i ⋙ F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
  body: ⟨by intros; infer_instance⟩

中文:
实例 [有有限极限
  签名: C] [F.保持ZeroMorphisms] [保持FiniteLimits F] :
  定义体: ⟨by intros; infer_instance⟩

Depends on / 依赖: infer_instance, intros
-/
instance [HasFiniteLimits C] [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
    PreservesFiniteLimits (F.mapHomologicalComplex c) :=
  ⟨by intros; infer_instance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] :
  body: ⟨by intros; infer_instance⟩

中文:
实例 [有有限余极限
  签名: C] [F.保持ZeroMorphisms] [保持FiniteColimits F] :
  定义体: ⟨by intros; infer_instance⟩

Depends on / 依赖: infer_instance, intros
-/
instance [HasFiniteColimits C] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] :
    PreservesFiniteColimits (F.mapHomologicalComplex c) :=
  ⟨by intros; infer_instance⟩

end CategoryTheory
