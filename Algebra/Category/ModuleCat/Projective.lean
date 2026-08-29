/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The category of `R`-modules has enough projectives.
-/

public section

universe v u w

open CategoryTheory Module ModuleCat

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

/--
Instance `ModuleCat.projective_of_categoryTheory_projective` / 实例 `ModuleCat.projective_of_categoryTheory_projective`

English:
instance ModuleCat.projective_of_categoryTheory_projective
  signature: [Module.Projective R P]
  body: by
  refine ⟨fun E X epi => ?_⟩
  obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
    ((ModuleCat.epi_iff_surjective _).mp epi)
  exact ⟨ofHom f, hom_ext h⟩

中文:
实例 模范畴.projective_of_categoryTheory_projective
  签名: [模.投射 R P]
  定义体: by
  refine ⟨fun E X epi => ?_⟩
  obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
    ((ModuleCat.epi_iff_surjective _).mp epi)
  exact ⟨ofHom f, hom_ext h⟩

Depends on / 依赖: E.hom, Module, Module.projective_lifting_property, ModuleCat, ModuleCat.epi_iff_surjective, X.hom, epi_iff_surjective, hom_ext, projective_lifting_property
-/
instance ModuleCat.projective_of_categoryTheory_projective [Module.Projective R P] :
    CategoryTheory.Projective P := by
  refine ⟨fun E X epi => ?_⟩
  obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
    ((ModuleCat.epi_iff_surjective _).mp epi)
  exact ⟨ofHom f, hom_ext h⟩

/--
Instance `ModuleCat.projective_of_module_projective` / 实例 `ModuleCat.projective_of_module_projective`

English:
instance ModuleCat.projective_of_module_projective
  signature: [Small.{v} R] [Projective P]
  body: by
  refine Module.Projective.of_lifting_property ?_
  intro _ _ _ _ _ _ f g s
  have : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
  exact ⟨(Projective.factorThru (↟g) (↟f)).hom,
ModuleCat.hom_ext_iff.mp Projective.factorThru_comp (↟g) (↟f)⟩

中文:
实例 模范畴.projective_of_module_projective
  签名: [Small.{v} R] [投射 P]
  定义体: by
  refine Module.Projective.of_lifting_property ?_
  intro _ _ _ _ _ _ f g s
  have : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
  exact ⟨(Projective.factorThru (↟g) (↟f)).hom,
ModuleCat.hom_ext_iff.mp Projective.factorThru_comp (↟g) (↟f)⟩

Depends on / 依赖: Module, Module.Projective.of_lifting_property, ModuleCat, ModuleCat.epi_iff_surjective, ModuleCat.hom_ext_iff.mp, Projective, Projective.factorThru, Projective.factorThru_comp, epi_iff_surjective, factorThru, factorThru_comp, hom_ext_iff, of_lifting_property
-/
instance ModuleCat.projective_of_module_projective [Small.{v} R] [Projective P] :
    Module.Projective R P := by
  refine Module.Projective.of_lifting_property ?_
  intro _ _ _ _ _ _ f g s
  have : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
  exact ⟨(Projective.factorThru (↟g) (↟f)).hom,
ModuleCat.hom_ext_iff.mp Projective.factorThru_comp (↟g) (↟f)⟩

/--
theorem `IsProjective.iff_projective` / 定理 `IsProjective.iff_projective`

English:
theorem IsProjective.iff_projective
  given: [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P]
  proof: ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

中文:
定理 IsProjective.iff_projective
  条件: [Small.{v} R] (P : 类型v) [加法交换群 P] [模 R P]
  证明: ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

Depends on / 依赖: projective_of_categoryTheory_projective, projective_of_module_projective
-/
theorem IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔ Projective (of R P) :=
  ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

namespace ModuleCat

variable {M : ModuleCat.{v} R}

-- We transport the corresponding result from `Module.Projective`.
/--
theorem `projective_of_free` / 定理 `projective_of_free`

English:
theorem projective_of_free
  given: {ι : Type w} (b : Basis ι R M)
  statement: Projective M
  proof: have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

中文:
定理 projective_of_free
  条件: {ι : 类型 w} (b : 基 ι R M)
  结论: 投射 M
  证明: have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

Depends on / 依赖: M.projective_of_categoryTheory_projective, Module, Module.Projective, Module.Projective.of_basis, Projective, of_basis, projective_of_categoryTheory_projective
-/
theorem projective_of_free {ι : Type w} (b : Basis ι R M) : Projective M :=
  have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

/--
Instance `enoughProjectives` / 实例 `enoughProjectives`

English:
instance enoughProjectives
  signature: [Small.{v} R]
  body: let e : Basis M R (M ->₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    ⟨{p := ModuleCat.of R (M ->₀ Shrink.{v} R)
      projective := projective_of_free e
f := ofHom e.constr Nat _root_.id
      epi := by
        rw [epi_iff_range_eq_top]; rw [LinearMap.range_eq_top]
        refine fun m => ⟨Finsupp.single m 1, ?_⟩
        simp [e, Basis.constr_apply] }⟩

中文:
实例 enoughProjectives
  签名: [Small.{v} R]
  定义体: let e : Basis M R (M ->₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    ⟨{p := ModuleCat.of R (M ->₀ Shrink.{v} R)
      projective := projective_of_free e
f := ofHom e.constr Nat _root_.id
      epi := by
        rw [epi_iff_range_eq_top]; rw [LinearMap.range_eq_top]
        refine fun m => ⟨Finsupp.single m 1, ?_⟩
        simp [e, Basis.constr_apply] }⟩

Depends on / 依赖: Basis.constr_apply, Finsupp, Finsupp.mapRange.linearEquiv, Finsupp.single, LinearMap, LinearMap.range_eq_top, ModuleCat, ModuleCat.of, Shrink, Shrink.linearEquiv, _root_, _root_.id, constr, constr_apply, e.constr, epi_iff_range_eq_top, linearEquiv, mapRange, projective, projective_of_free
-/
instance enoughProjectives [Small.{v} R] : EnoughProjectives (ModuleCat.{v} R) where
  presentation M :=
    let e : Basis M R (M ->₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    ⟨{p := ModuleCat.of R (M ->₀ Shrink.{v} R)
      projective := projective_of_free e
f := ofHom e.constr Nat _root_.id
      epi := by
        rw [epi_iff_range_eq_top]; rw [LinearMap.range_eq_top]
        refine fun m => ⟨Finsupp.single m 1, ?_⟩
        simp [e, Basis.constr_apply] }⟩

end ModuleCat
