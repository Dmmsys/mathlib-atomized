/-
Copyright (c) 2024 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Extension of Scalars for Algebra Extensions

This file provides APIs for extending the base ring of an algebra extension `P : Extension R S`
to its own extension ring `P.Ring`. We introduce canonical maps and isomorphisms between
the cotangent spaces and the first homology of naive cotangent complex associated with
`P.extendScalars` and `P`. We provide commutativity results of these maps and ismorphisms
(See https://github.com/leanprover-community/mathlib4/pull/39520 for an image of the full diagram).
In particular, we show the boundary map of the Jacobi-Zariski sequence of `R → P.Ring → S`
coincides with `P.cotangentComplex` via a canonical isomorphism `P.h1CotangentEquivCotangent`.

## Main definitions and results

- `extendScalars`: Views `P : Extension R S` as `Extension P.Ring S`.
- `toExtendScalars`: The canonical homomorphism from `P` to `P.extendScalars` induced by
  the identity map on the underlying extension rings.
- `cotangentExtendScalarsEquiv` : The linear equivalence between the cotangent spaces of
  `P.extensScalars` and `P` induced by the identity map.
- `h1CotangentExtendScalarsEquiv`: `P.extensScalars` can be used to compute the first homology of
  the naive cotangent complex of `S` over `P.Ring`.
- `h1CotangentEquivOfSurjective`: If `R → P.Ring` is surjective, this is the linear isomorphism
  induced by `P.h1Cotangentι`.
- `h1CotangentEquivCotangent`: This is the linear equivalence between `H1Cotangent P.Ring S` and
  `P.Cotangent` defined by the composition of `h1CotangentExtendScalarsEquiv.symm`,
  `h1CotangentEquivOfSurjective` and `cotangentExtendScalarsEquiv`.
- `cotangentComplex_comp_h1CotangentEquivCotangent`,
  `h1CotangentEquivCotangent_comp_map`: commutativity results.

-/

@[expose] public section

open KaehlerDifferential

namespace Algebra.Extension

universe w v u

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Given an extension `P` of `S` over `R`, `P.extendScalars` is the same extension
but viewed as an extension of `S` over `P.Ring`. -/
@[simps]
/--
Definition of `extendScalars` / `extendScalars` 的定义

English:
definition extendScalars
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  body: P.Ring
  σ := P.σ
  algebraMap_σ := P.algebraMap_σ

中文:
定义 extendScalars
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S] [代数 R S]
  定义体: P.Ring
  σ := P.σ
  algebraMap_σ := P.algebraMap_σ

Depends on / 依赖: P.Ring
-/
def extendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : Extension P.Ring S where
  Ring := P.Ring
  σ := P.σ
  algebraMap_σ := P.algebraMap_σ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homomorphism from `P` to `P.extendScalars` induced by the identity map
on the underlying extension rings. -/
@[simps!]
noncomputable
/--
Definition of `toExtendScalars` / `toExtendScalars` 的定义

English:
definition toExtendScalars
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  body: .ofAlgHom (IsScalarTower.toAlgHom R P.Ring P.extendScalars.Ring)
    (by dsimp; ext; simp)

中文:
定义 toExtendScalars
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S] [代数 R S]
  定义体: .ofAlgHom (IsScalarTower.toAlgHom R P.Ring P.extendScalars.Ring)
    (by dsimp; ext; simp)

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, P.Ring, P.extendScalars.Ring, extendScalars, ofAlgHom, toAlgHom
-/
def toExtendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : P.Hom P.extendScalars :=
  .ofAlgHom (IsScalarTower.toAlgHom R P.Ring P.extendScalars.Ring)
    (by dsimp; ext; simp)

/-- `Extension.extendScalars` does not change the cotangent space of an extension. -/
noncomputable
/--
Definition of `cotangentExtendScalarsEquiv` / `cotangentExtendScalarsEquiv` 的定义

English:
definition cotangentExtendScalarsEquiv
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  body: LinearEquiv.refl _ _

@[simp]

中文:
定义 cotangentExtendScalarsEquiv
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S]
  定义体: LinearEquiv.refl _ _

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def cotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.Cotangent ≃ₗ[S] P.Cotangent :=
  LinearEquiv.refl _ _

@[simp]
/--
lemma `cotangentExtendScalarsEquiv_symm_toLinearMap` / 引理 `cotangentExtendScalarsEquiv_symm_toLinearMap`

English:
lemma cotangentExtendScalarsEquiv_symm_toLinearMap
  given: (P : Extension.{w} R S)
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rfl

中文:
引理 cotangentExtendScalarsEquiv_symm_toLinearMap
  条件: (P : 扩张.{w} R S)
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rfl

Depends on / 依赖: Cotangent, Cotangent.mk_surjective, mk_surjective
-/
lemma cotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) :
    P.cotangentExtendScalarsEquiv.symm.toLinearMap = Cotangent.map P.toExtendScalars := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `H1Cotangent.map_toExtendScalars_injective` / 定理 `H1Cotangent.map_toExtendScalars_injective`

English:
theorem H1Cotangent.map_toExtendScalars_injective
  given: (P : Extension.{w} R S)
  proof: by
  rw [← LinearMap.ker_eq_bot]; rw [H1Cotangent.map]; rw [LinearMap.ker_restrict]; rw [← cotangentExtendScalarsEquiv_symm_toLinearMap]; rw [LinearEquiv.ker]; rw [Submodule.comap_bot]; rw [Submodule.ker_subtype]

中文:
定理 H1Cotangent.map_toExtendScalars_injective
  条件: (P : 扩张.{w} R S)
  证明: by
  rw [← LinearMap.ker_eq_bot]; rw [H1Cotangent.map]; rw [LinearMap.ker_restrict]; rw [← cotangentExtendScalarsEquiv_symm_toLinearMap]; rw [LinearEquiv.ker]; rw [Submodule.comap_bot]; rw [Submodule.ker_subtype]

Depends on / 依赖: H1Cotangent, H1Cotangent.map, LinearEquiv, LinearEquiv.ker, LinearMap, LinearMap.ker_eq_bot, LinearMap.ker_restrict, Submodule, Submodule.comap_bot, Submodule.ker_subtype, comap_bot, cotangentExtendScalarsEquiv_symm_toLinearMap, ker_eq_bot, ker_restrict, ker_subtype
-/
theorem H1Cotangent.map_toExtendScalars_injective (P : Extension.{w} R S) :
    Function.Injective (H1Cotangent.map P.toExtendScalars) := by
  rw [← LinearMap.ker_eq_bot]; rw [H1Cotangent.map]; rw [LinearMap.ker_restrict]; rw [← cotangentExtendScalarsEquiv_symm_toLinearMap]; rw [LinearEquiv.ker]; rw [Submodule.comap_bot]; rw [Submodule.ker_subtype]

/-- The first homology of the naive cotangent complex of `P.extendScalars` is
linearly equivalent to that of `S` over `P.Ring`. -/
@[simps! toLinearMap]
noncomputable
/--
Definition of `h1CotangentExtendScalarsEquiv` / `h1CotangentExtendScalarsEquiv` 的定义

English:
definition h1CotangentExtendScalarsEquiv
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  body: Extension.H1Cotangent.equiv
    (.ofAlgHom (Algebra.ofId _ _) (by ext)) P.extendScalars.defaultHom

@[simp]

中文:
定义 h1CotangentExtendScalarsEquiv
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S]
  定义体: Extension.H1Cotangent.equiv
    (.ofAlgHom (Algebra.ofId _ _) (by ext)) P.extendScalars.defaultHom

@[simp]

Depends on / 依赖: Algebra, Algebra.ofId, Extension, Extension.H1Cotangent.equiv, H1Cotangent, P.extendScalars.defaultHom, defaultHom, extendScalars, ofAlgHom
-/
def h1CotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.H1Cotangent ≃ₗ[S] H1Cotangent P.Ring S :=
  Extension.H1Cotangent.equiv
    (.ofAlgHom (Algebra.ofId _ _) (by ext)) P.extendScalars.defaultHom

@[simp]
/--
lemma `h1CotangentExtendScalarsEquiv_symm_toLinearMap` / 引理 `h1CotangentExtendScalarsEquiv_symm_toLinearMap`

English:
lemma h1CotangentExtendScalarsEquiv_symm_toLinearMap
  given: (P : Extension.{w} R S)
  proof: rfl

中文:
引理 h1CotangentExtendScalarsEquiv_symm_toLinearMap
  条件: (P : 扩张.{w} R S)
  证明: rfl
-/
lemma h1CotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) :
  P.h1CotangentExtendScalarsEquiv.symm = H1Cotangent.map P.extendScalars.defaultHom := rfl

/-- Given an extension `P` of `S` over `R` such that `algebraMap R P.Ring` is surjective,
this is the equivalence induced by `P.h1Cotangentι`. -/
@[simps! toLinearMap]
noncomputable
/--
Definition of `h1CotangentEquivOfSurjective` / `h1CotangentEquivOfSurjective` 的定义

English:
definition h1CotangentEquivOfSurjective
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  body: P.h1Cotangentι
  invFun x := ⟨x, by
    have : Subsingleton Ω[P.Ring⁄R] := subsingleton_of_surjective R P.Ring h
    exact Subsingleton.elim _ _⟩

中文:
定义 h1CotangentEquivOfSurjective
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S]
  定义体: P.h1Cotangentι
  invFun x := ⟨x, by
    have : Subsingleton Ω[P.Ring⁄R] := subsingleton_of_surjective R P.Ring h
    exact Subsingleton.elim _ _⟩

Depends on / 依赖: P.h1Cotangent
-/
def h1CotangentEquivOfSurjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) (h : Function.Surjective (algebraMap R P.Ring)) :
    P.H1Cotangent ≃ₗ[S] P.Cotangent where
  __ := P.h1Cotangentι
  invFun x := ⟨x, by
    have : Subsingleton Ω[P.Ring⁄R] := subsingleton_of_surjective R P.Ring h
    exact Subsingleton.elim _ _⟩

/-- Given an extension `P : Extension R S`, this is the linear equivalence between
the first homology of the naive cotangent complex of `S` over `P.Ring` and
the cotangent space of `P`. -/
noncomputable
/--
Definition of `h1CotangentEquivCotangent` / `h1CotangentEquivCotangent` 的定义

English:
definition h1CotangentEquivCotangent
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  body: P.h1CotangentExtendScalarsEquiv.symm ≪≫ₗ
    P.extendScalars.h1CotangentEquivOfSurjective Function.surjective_id ≪≫ₗ
    P.cotangentExtendScalarsEquiv

中文:
定义 h1CotangentEquivCotangent
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S]
  定义体: P.h1CotangentExtendScalarsEquiv.symm ≪≫ₗ
    P.extendScalars.h1CotangentEquivOfSurjective Function.surjective_id ≪≫ₗ
    P.cotangentExtendScalarsEquiv

Depends on / 依赖: Function, Function.surjective_id, P.cotangentExtendScalarsEquiv, P.extendScalars.h1CotangentEquivOfSurjective, P.h1CotangentExtendScalarsEquiv.symm, cotangentExtendScalarsEquiv, extendScalars, h1CotangentEquivOfSurjective, h1CotangentExtendScalarsEquiv, surjective_id
-/
def h1CotangentEquivCotangent {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    H1Cotangent P.Ring S ≃ₗ[S] P.Cotangent :=
  P.h1CotangentExtendScalarsEquiv.symm ≪≫ₗ
    P.extendScalars.h1CotangentEquivOfSurjective Function.surjective_id ≪≫ₗ
    P.cotangentExtendScalarsEquiv

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cotangentComplex_comp_h1CotangentEquivCotangent` / 定理 `cotangentComplex_comp_h1CotangentEquivCotangent`

English:
theorem cotangentComplex_comp_h1CotangentEquivCotangent
  given: (P : Extension.{w} R S)
  proof: by
  rw [h1CotangentEquivCotangent]; rw [LinearEquiv.coe_trans]; rw [LinearEquiv.coe_trans]; rw [h1CotangentEquivOfSurjective_toLinearMap]; rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [LinearMap.comp_assoc]; rw [h1CotangentExtendScalarsEquiv_toLinearMap]
  ext ⟨x, _⟩
  obtain ⟨⟨x : P.Ring, x_in : x in P.ker⟩, rfl⟩ := Cotangent.mk_surjective x
  trans 1 otimesₜ[P.Ring] D R P.Ring x; · exact cotangentComplex_mk P ⟨x, x_in⟩
  let u : (Generators.self P.Ring S).toExtension.ker :=
    ⟨algebraMap P.Ring (Generators.self P.Ring S).toExtension.Ring x, by
      rwa [← Ideal.mem_comap, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]⟩
  rw [← Generators.H1Cotangent.δ_C _ _ u.prop]
  congr

中文:
定理 cotangentComplex_comp_h1CotangentEquivCotangent
  条件: (P : 扩张.{w} R S)
  证明: by
  rw [h1CotangentEquivCotangent]; rw [LinearEquiv.coe_trans]; rw [LinearEquiv.coe_trans]; rw [h1CotangentEquivOfSurjective_toLinearMap]; rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [LinearMap.comp_assoc]; rw [h1CotangentExtendScalarsEquiv_toLinearMap]
  ext ⟨x, _⟩
  obtain ⟨⟨x : P.Ring, x_in : x in P.ker⟩, rfl⟩ := Cotangent.mk_surjective x
  trans 1 otimesₜ[P.Ring] D R P.Ring x; · exact cotangentComplex_mk P ⟨x, x_in⟩
  let u : (Generators.self P.Ring S).toExtension.ker :=
    ⟨algebraMap P.Ring (Generators.self P.Ring S).toExtension.Ring x, by
      rwa [← Ideal.mem_comap, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]⟩
  rw [← Generators.H1Cotangent.δ_C _ _ u.prop]
  congr

Depends on / 依赖: Cotangent, Cotangent.mk_surjective, Generators, Generators.sel, LinearEquiv, LinearEquiv.coe_trans, LinearEquiv.comp_toLinearMap_symm_eq, LinearMap, LinearMap.comp_assoc, P.Ring, P.ker, coe_trans, comp_assoc, comp_toLinearMap_symm_eq, cotangentComplex_mk, h1CotangentEquivCotangent, h1CotangentEquivOfSurjective_toLinearMap, h1CotangentExtendScalarsEquiv_toLinearMap, mk_surjective, x_in
-/
theorem cotangentComplex_comp_h1CotangentEquivCotangent (P : Extension.{w} R S) :
    P.cotangentComplex.comp P.h1CotangentEquivCotangent.toLinearMap =
      H1Cotangent.δ R P.Ring S := by
  rw [h1CotangentEquivCotangent]; rw [LinearEquiv.coe_trans]; rw [LinearEquiv.coe_trans]; rw [h1CotangentEquivOfSurjective_toLinearMap]; rw [← LinearMap.comp_assoc]; rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [LinearMap.comp_assoc]; rw [h1CotangentExtendScalarsEquiv_toLinearMap]
  ext ⟨x, _⟩
  obtain ⟨⟨x : P.Ring, x_in : x in P.ker⟩, rfl⟩ := Cotangent.mk_surjective x
  trans 1 otimesₜ[P.Ring] D R P.Ring x; · exact cotangentComplex_mk P ⟨x, x_in⟩
  let u : (Generators.self P.Ring S).toExtension.ker :=
    ⟨algebraMap P.Ring (Generators.self P.Ring S).toExtension.Ring x, by
      rwa [← Ideal.mem_comap, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]⟩
  rw [← Generators.H1Cotangent.δ_C _ _ u.prop]
  congr

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `h1CotangentEquivCotangent_comp_map` / 定理 `h1CotangentEquivCotangent_comp_map`

English:
theorem h1CotangentEquivCotangent_comp_map
  given: (P : Extension.{w} R S)
  proof: by
  rw [h1CotangentEquivCotangent]; rw [LinearEquiv.coe_trans]; rw [LinearEquiv.coe_trans]; rw [h1CotangentExtendScalarsEquiv_symm_toLinearMap]; rw [h1CotangentEquivOfSurjective_toLinearMap]; rw [LinearMap.comp_assoc]; rw [LinearMap.comp_assoc]; rw [Algebra.H1Cotangent.map]; rw [← (H1Cotangent.map P.extendScalars.defaultHom).restrictScalars_self]; rw [← H1Cotangent.map_comp]; rw [eq_comm]; rw [← LinearEquiv.toLinearMap_symm_comp_eq]; rw [cotangentExtendScalarsEquiv_symm_toLinearMap]; rw [← LinearMap.comp_assoc]; rw [Cotangent.map_comp_h1Cotangentι]; rw [LinearMap.restrictScalars_self]; rw [LinearMap.comp_assoc]; rw [← (H1Cotangent.map P.toExtendScalars).restrictScalars_self]; rw [← H1Cotangent.map_comp]; rw [H1Cotangent.map_eq]

中文:
定理 h1CotangentEquivCotangent_comp_map
  条件: (P : 扩张.{w} R S)
  证明: by
  rw [h1CotangentEquivCotangent]; rw [LinearEquiv.coe_trans]; rw [LinearEquiv.coe_trans]; rw [h1CotangentExtendScalarsEquiv_symm_toLinearMap]; rw [h1CotangentEquivOfSurjective_toLinearMap]; rw [LinearMap.comp_assoc]; rw [LinearMap.comp_assoc]; rw [Algebra.H1Cotangent.map]; rw [← (H1Cotangent.map P.extendScalars.defaultHom).restrictScalars_self]; rw [← H1Cotangent.map_comp]; rw [eq_comm]; rw [← LinearEquiv.toLinearMap_symm_comp_eq]; rw [cotangentExtendScalarsEquiv_symm_toLinearMap]; rw [← LinearMap.comp_assoc]; rw [Cotangent.map_comp_h1Cotangentι]; rw [LinearMap.restrictScalars_self]; rw [LinearMap.comp_assoc]; rw [← (H1Cotangent.map P.toExtendScalars).restrictScalars_self]; rw [← H1Cotangent.map_comp]; rw [H1Cotangent.map_eq]

Depends on / 依赖: Algebra, Algebra.H1Cotangent.map, H1Cotangent, H1Cotangent.map, H1Cotangent.map_comp, Linear, LinearEquiv, LinearEquiv.coe_trans, LinearEquiv.toLinearMap_symm_comp_eq, LinearMap, LinearMap.comp_assoc, P.extendScalars.defaultHom, coe_trans, comp_assoc, cotangentExtendScalarsEquiv_symm_toLinearMap, defaultHom, eq_comm, extendScalars, h1CotangentEquivCotangent, h1CotangentEquivOfSurjective_toLinearMap
-/
theorem h1CotangentEquivCotangent_comp_map (P : Extension.{w} R S) :
    P.h1CotangentEquivCotangent.toLinearMap.comp (Algebra.H1Cotangent.map R P.Ring S S) =
      h1Cotangentι.comp (H1Cotangent.map P.defaultHom) := by
  rw [h1CotangentEquivCotangent]; rw [LinearEquiv.coe_trans]; rw [LinearEquiv.coe_trans]; rw [h1CotangentExtendScalarsEquiv_symm_toLinearMap]; rw [h1CotangentEquivOfSurjective_toLinearMap]; rw [LinearMap.comp_assoc]; rw [LinearMap.comp_assoc]; rw [Algebra.H1Cotangent.map]; rw [← (H1Cotangent.map P.extendScalars.defaultHom).restrictScalars_self]; rw [← H1Cotangent.map_comp]; rw [eq_comm]; rw [← LinearEquiv.toLinearMap_symm_comp_eq]; rw [cotangentExtendScalarsEquiv_symm_toLinearMap]; rw [← LinearMap.comp_assoc]; rw [Cotangent.map_comp_h1Cotangentι]; rw [LinearMap.restrictScalars_self]; rw [LinearMap.comp_assoc]; rw [← (H1Cotangent.map P.toExtendScalars).restrictScalars_self]; rw [← H1Cotangent.map_comp]; rw [H1Cotangent.map_eq]

/--
theorem `H1Cotangent.map_defaultHom_surjective` / 定理 `H1Cotangent.map_defaultHom_surjective`

English:
theorem H1Cotangent.map_defaultHom_surjective
  given: (P : Extension.{w} R S)
  proof: by
  rw [← LinearMap.range_eq_top]; rw [← (Submodule.map_injective_of_injective h1Cotangentι_injective).eq_iff]; rw [← LinearMap.range_comp]; rw [← P.h1CotangentEquivCotangent_comp_map]; rw [LinearMap.range_comp]; rw [← (Algebra.H1Cotangent.exact_map_δ R P.Ring S).linearMap_ker_eq]; rw [Submodule.map_top]; rw [← exact_hCotangentι_cotangentComplex.linearMap_ker_eq]; rw [Submodule.map_equiv_eq_comap_symm]; rw [LinearMap.ker]; rw [LinearMap.ker]; rw [← Submodule.comap_comp]
  congr
  rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [P.cotangentComplex_comp_h1CotangentEquivCotangent]

中文:
定理 H1Cotangent.map_defaultHom_surjective
  条件: (P : 扩张.{w} R S)
  证明: by
  rw [← LinearMap.range_eq_top]; rw [← (Submodule.map_injective_of_injective h1Cotangentι_injective).eq_iff]; rw [← LinearMap.range_comp]; rw [← P.h1CotangentEquivCotangent_comp_map]; rw [LinearMap.range_comp]; rw [← (Algebra.H1Cotangent.exact_map_δ R P.Ring S).linearMap_ker_eq]; rw [Submodule.map_top]; rw [← exact_hCotangentι_cotangentComplex.linearMap_ker_eq]; rw [Submodule.map_equiv_eq_comap_symm]; rw [LinearMap.ker]; rw [LinearMap.ker]; rw [← Submodule.comap_comp]
  congr
  rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [P.cotangentComplex_comp_h1CotangentEquivCotangent]

Depends on / 依赖: Algebra, Algebra.H1Cotangent.exact_map_, H1Cotangent, LinearEquiv, LinearEquiv.comp, LinearMap, LinearMap.ker, LinearMap.range_comp, LinearMap.range_eq_top, P.Ring, P.h1CotangentEquivCotangent_comp_map, Submodule, Submodule.comap_comp, Submodule.map_equiv_eq_comap_symm, Submodule.map_injective_of_injective, Submodule.map_top, _cotangentComplex.linearMap_ker_eq, comap_comp, eq_iff, h1CotangentEquivCotangent_comp_map
-/
theorem H1Cotangent.map_defaultHom_surjective (P : Extension.{w} R S) :
    Function.Surjective (H1Cotangent.map P.defaultHom) := by
  rw [← LinearMap.range_eq_top]; rw [← (Submodule.map_injective_of_injective h1Cotangentι_injective).eq_iff]; rw [← LinearMap.range_comp]; rw [← P.h1CotangentEquivCotangent_comp_map]; rw [LinearMap.range_comp]; rw [← (Algebra.H1Cotangent.exact_map_δ R P.Ring S).linearMap_ker_eq]; rw [Submodule.map_top]; rw [← exact_hCotangentι_cotangentComplex.linearMap_ker_eq]; rw [Submodule.map_equiv_eq_comap_symm]; rw [LinearMap.ker]; rw [LinearMap.ker]; rw [← Submodule.comap_comp]
  congr
  rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [P.cotangentComplex_comp_h1CotangentEquivCotangent]

end Algebra.Extension
