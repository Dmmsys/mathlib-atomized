/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaves over Abelian categories

We provide instances for categories of sheaves over Abelian categories.

## Main Results

* `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`: A complex of sheaves over a concrete abelian
  category is exact if and only if it is exact on stalks.

-/

public section

universe u v v₁ v₂

open TopologicalSpace CategoryTheory Limits

namespace TopCat

variable {X : TopCat.{u}}

section

variable {C : Type v₁} [Category.{v₂} C] [HasSheafify (Opens.grothendieckTopology X) C] [Abelian C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (Presheaf C X)
  body: inferInstanceAs (Abelian (_ ⥤ _))

中文:
实例 :
  签名: 交换 (预层 C X)
  定义体: inferInstanceAs (Abelian (_ ⥤ _))

Depends on / 依赖: Abelian
-/
noncomputable instance : Abelian (Presheaf C X) := inferInstanceAs (Abelian (_ ⥤ _))

namespace Sheaf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (Sheaf C X)
  body: inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

中文:
实例 :
  签名: 交换 (层 C X)
  定义体: inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

Depends on / 依赖: Abelian, CategoryTheory, CategoryTheory.Sheaf
-/
noncomputable instance : Abelian (Sheaf C X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Sheaf.forget C X).Additive

中文:
实例 :
  签名: (层.forget C X).加性
-/
instance : (Sheaf.forget C X).Additive where

instance {D : Type*} [Category.{u} D] [Abelian D] [IsGrothendieckAbelian.{u} D]
    [HasSheafify (Opens.grothendieckTopology X) D] : IsGrothendieckAbelian.{u} (Sheaf D X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

end Sheaf

end

set_option backward.isDefEq.respectTransparency false in
/-- The stalk functor is additive -/
instance (p₀ : X) {C : Type v} [Category.{u} C] [Abelian C] [HasColimits C] :
    (Presheaf.stalkFunctor C p₀).Additive := by
  dsimp [Presheaf.stalkFunctor]
  have : ((Functor.whiskeringLeft _ _ C).obj (OpenNhds.inclusion p₀).op).Additive := ⟨by cat_disch⟩
  infer_instance

namespace Sheaf

open Presheaf

variable {C : Type v} [Category.{u} C] [HasColimits C] [HasLimits C]
  {FC : C -> C -> Type*} {CC : C -> Type u} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [instCC : ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
  [PreservesLimits (CategoryTheory.forget C)] [Abelian C]
  {X : TopCat.{u}} (p₀ : X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesFiniteLimits (forget C X ⋙ stalkFunctor C p₀)
  body: have : (forget C X ⋙ stalkFunctor C p₀).PreservesHomology := by
    simp only [(forget C X ⋙ stalkFunctor C p₀).exact_tfae.out 2 0]
    intro S h
    have := ((forget C X ⋙ stalkFunctor C p₀).preservesFiniteColimits_tfae.out 3 0).mp
      (inferInstance : (PreservesFiniteColimits _))
    refine ShortComplex.ShortExact.mk' (this S h).left ?_ (this S h).right
    have := h.2
    exact Functor.map_mono (forget C X ⋙ stalkFunctor C p₀) _
  (forget C X ⋙ stalkFunctor C p₀).preservesFiniteLimits_of_preservesHomology

中文:
实例 :
  签名: Limits.保持FiniteLimits (forget C X ⋙ stalkFunctor C p₀)
  定义体: have : (forget C X ⋙ stalkFunctor C p₀).PreservesHomology := by
    simp only [(forget C X ⋙ stalkFunctor C p₀).exact_tfae.out 2 0]
    intro S h
    have := ((forget C X ⋙ stalkFunctor C p₀).preservesFiniteColimits_tfae.out 3 0).mp
      (inferInstance : (PreservesFiniteColimits _))
    refine ShortComplex.ShortExact.mk' (this S h).left ?_ (this S h).right
    have := h.2
    exact Functor.map_mono (forget C X ⋙ stalkFunctor C p₀) _
  (forget C X ⋙ stalkFunctor C p₀).preservesFiniteLimits_of_preservesHomology

Depends on / 依赖: Functor, Functor.map_mono, PreservesFiniteColimits, PreservesHomology, ShortComplex, ShortComplex.ShortExact.mk, ShortExact, exact_tfae, exact_tfae.out, forget, map_mono, preservesFiniteColimits_tfae, preservesFiniteColimits_tfae.out, preservesFiniteLimits_of_preservesHomology, stalkFunctor
-/
instance : Limits.PreservesFiniteLimits (forget C X ⋙ stalkFunctor C p₀) :=
  have : (forget C X ⋙ stalkFunctor C p₀).PreservesHomology := by
    simp only [(forget C X ⋙ stalkFunctor C p₀).exact_tfae.out 2 0]
    intro S h
    have := ((forget C X ⋙ stalkFunctor C p₀).preservesFiniteColimits_tfae.out 3 0).mp
      (inferInstance : (PreservesFiniteColimits _))
    refine ShortComplex.ShortExact.mk' (this S h).left ?_ (this S h).right
    have := h.2
    exact Functor.map_mono (forget C X ⋙ stalkFunctor C p₀) _
  (forget C X ⋙ stalkFunctor C p₀).preservesFiniteLimits_of_preservesHomology

open ZeroObject

include instCC in
/--
lemma `isZero_iff_stalkFunctor_obj_isZero` / 引理 `isZero_iff_stalkFunctor_obj_isZero`

English:
lemma isZero_iff_stalkFunctor_obj_isZero
  given: (F : Sheaf C X)
  proof: by
  refine ⟨fun h _ => Functor.map_isZero _ h, ?_⟩
  intro h
  let f : F ⟶ 0 := (isZero_zero (Sheaf C X)).from_ F
  have : IsIso f := by
    rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
    exact fun x => isIso_of_source_target_iso_zero _ (h x).isoZero
      ((forget C X ⋙ stalkFunctor C x).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso f)

include instCC in

中文:
引理 isZero_iff_stalkFunctor_obj_isZero
  条件: (F : 层 C X)
  证明: by
  refine ⟨fun h _ => Functor.map_isZero _ h, ?_⟩
  intro h
  let f : F ⟶ 0 := (isZero_zero (Sheaf C X)).from_ F
  have : IsIso f := by
    rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
    exact fun x => isIso_of_source_target_iso_zero _ (h x).isoZero
      ((forget C X ⋙ stalkFunctor C x).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso f)

include instCC in

Depends on / 依赖: Functor, Functor.map_isZero, Presheaf, Presheaf.isIso_iff_stalkFunctor_map_iso, forget, from_, isIso_iff_stalkFunctor_map_iso, isIso_of_source_target_iso_zero, isZero_zero, isoZero, map_isZero, of_iso, stalkFunctor
-/
lemma isZero_iff_stalkFunctor_obj_isZero (F : Sheaf C X) :
    IsZero F ↔ forall x : X, IsZero ((forget C X ⋙ stalkFunctor C x).obj F) := by
  refine ⟨fun h _ => Functor.map_isZero _ h, ?_⟩
  intro h
  let f : F ⟶ 0 := (isZero_zero (Sheaf C X)).from_ F
  have : IsIso f := by
    rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
    exact fun x => isIso_of_source_target_iso_zero _ (h x).isoZero
      ((forget C X ⋙ stalkFunctor C x).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso f)

include instCC in
/--
theorem `exact_iff_stalkFunctor_map_exact` / 定理 `exact_iff_stalkFunctor_map_exact`

English:
theorem exact_iff_stalkFunctor_map_exact
  given: (S : ShortComplex (Sheaf C X))
  proof: by
  constructor
  · intro h x
    have := (forget C X ⋙ stalkFunctor C x).exact_tfae.out 2 1
    exact this.mp inferInstance S h
  intro h
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw [ShortComplex.exact_iff_isZero_homology]; rw [isZero_iff_stalkFunctor_obj_isZero S.homology]
  exact fun x => (h x).of_iso
    (ShortComplex.mapHomologyIso S (forget C X ⋙ stalkFunctor C x)).symm

中文:
定理 exact_iff_stalkFunctor_map_exact
  条件: (S : 短复形 (层 C X))
  证明: by
  constructor
  · intro h x
    have := (forget C X ⋙ stalkFunctor C x).exact_tfae.out 2 1
    exact this.mp inferInstance S h
  intro h
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw [ShortComplex.exact_iff_isZero_homology]; rw [isZero_iff_stalkFunctor_obj_isZero S.homology]
  exact fun x => (h x).of_iso
    (ShortComplex.mapHomologyIso S (forget C X ⋙ stalkFunctor C x)).symm

Depends on / 依赖: S.homology, ShortComplex, ShortComplex.exact_iff_isZero_homology, ShortComplex.mapHomologyIso, exact_iff_isZero_homology, exact_tfae, exact_tfae.out, forget, homology, isZero_iff_stalkFunctor_obj_isZero, mapHomologyIso, of_iso, simp_rw, stalkFunctor, this.mp
-/
theorem exact_iff_stalkFunctor_map_exact (S : ShortComplex (Sheaf C X)) :
    S.Exact ↔ forall x : X, (S.map (forget C X ⋙ stalkFunctor C x)).Exact := by
  constructor
  · intro h x
    have := (forget C X ⋙ stalkFunctor C x).exact_tfae.out 2 1
    exact this.mp inferInstance S h
  intro h
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw [ShortComplex.exact_iff_isZero_homology]; rw [isZero_iff_stalkFunctor_obj_isZero S.homology]
  exact fun x => (h x).of_iso
    (ShortComplex.mapHomologyIso S (forget C X ⋙ stalkFunctor C x)).symm

end Sheaf

end TopCat
