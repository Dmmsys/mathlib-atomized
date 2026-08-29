/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
public import Mathlib.Topology.Category.CompHaus.EffectiveEpi
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.Topology.Category.Stonean.Basic
/-!

# Effective epimorphisms in `Profinite`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `Profinite`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `Profinite` is `Preregular`
and `Precoherent`.

We also prove that for a finite family of morphisms in `Profinite` with fixed
target, the conditions jointly surjective, jointly epimorphic and effective epimorphic are all
equivalent.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Profinite

open List in
/--
theorem `effectiveEpi_tfae` / 定理 `effectiveEpi_tfae`

English:
theorem effectiveEpi_tfae
  proof: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 -> 1 := fun hπ => ⟨⟨CompHausLike.effectiveEpiStruct π hπ⟩⟩
  tfae_finish

中文:
定理 effectiveEpi_tfae
  证明: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 -> 1 := fun hπ => ⟨⟨CompHausLike.effectiveEpiStruct π hπ⟩⟩
  tfae_finish

Depends on / 依赖: CompHausLike, CompHausLike.effectiveEpiStruct, effectiveEpiStruct, epi_iff_surjective, tfae_finish, tfae_have
-/
theorem effectiveEpi_tfae
    {B X : Profinite.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 -> 1 := fun hπ => ⟨⟨CompHausLike.effectiveEpiStruct π hπ⟩⟩
  tfae_finish

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: profiniteToCompHaus.PreservesEffectiveEpis
  body: ((CompHaus.effectiveEpi_tfae _).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

中文:
实例 :
  签名: profiniteToCompHaus.保持EffectiveEpis
  定义体: ((CompHaus.effectiveEpi_tfae _).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, Profinite, Profinite.effectiveEpi_tfae, effectiveEpi_tfae
-/
instance : profiniteToCompHaus.PreservesEffectiveEpis where
  preserves f h :=
    ((CompHaus.effectiveEpi_tfae _).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: profiniteToCompHaus.ReflectsEffectiveEpis
  body: ((Profinite.effectiveEpi_tfae f).out 0 2).mpr (((CompHaus.effectiveEpi_tfae _).out 0 2).mp h)

中文:
实例 :
  签名: profiniteToCompHaus.ReflectsEffectiveEpis
  定义体: ((Profinite.effectiveEpi_tfae f).out 0 2).mpr (((CompHaus.effectiveEpi_tfae _).out 0 2).mp h)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, Profinite, Profinite.effectiveEpi_tfae, effectiveEpi_tfae
-/
instance : profiniteToCompHaus.ReflectsEffectiveEpis where
  reflects f h :=
    ((Profinite.effectiveEpi_tfae f).out 0 2).mpr (((CompHaus.effectiveEpi_tfae _).out 0 2).mp h)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `profiniteToCompHausEffectivePresentation` / `profiniteToCompHausEffectivePresentation` 的定义

English:
definition profiniteToCompHausEffectivePresentation
  signature: (X : CompHaus)
  body: Stonean.toProfinite.obj X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

中文:
定义 profiniteToCompHausEffectivePresentation
  签名: (X : CompHaus)
  定义体: Stonean.toProfinite.obj X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

Depends on / 依赖: Stonean, Stonean.toProfinite.obj, X.presentation, presentation, toProfinite
-/
noncomputable def profiniteToCompHausEffectivePresentation (X : CompHaus) :
    profiniteToCompHaus.EffectivePresentation X where
  p := Stonean.toProfinite.obj X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: profiniteToCompHaus.EffectivelyEnough
  body: ⟨profiniteToCompHausEffectivePresentation X⟩

中文:
实例 :
  签名: profiniteToCompHaus.EffectivelyEnough
  定义体: ⟨profiniteToCompHausEffectivePresentation X⟩

Depends on / 依赖: profiniteToCompHausEffectivePresentation
-/
instance : profiniteToCompHaus.EffectivelyEnough where
  presentation X := ⟨profiniteToCompHausEffectivePresentation X⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preregular Profinite.{u}
  body: profiniteToCompHaus.reflects_preregular

example : Precoherent Profinite.{u} := inferInstance

中文:
实例 :
  签名: Preregular Profinite.{u}
  定义体: profiniteToCompHaus.reflects_preregular

example : Precoherent Profinite.{u} := inferInstance

Depends on / 依赖: profiniteToCompHaus, profiniteToCompHaus.reflects_preregular, reflects_preregular
-/
instance : Preregular Profinite.{u} := profiniteToCompHaus.reflects_preregular

example : Precoherent Profinite.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
/--
theorem `effectiveEpiFamily_tfae` / 定理 `effectiveEpiFamily_tfae`

English:
theorem effectiveEpiFamily_tfae
  proof: by
  tfae_have 2 -> 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 3 ↔ 1 := by
    erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a => profiniteToCompHaus.obj (X a)) (fun a 

中文:
定理 effectiveEpiFamily_tfae
  证明: by
  tfae_have 2 -> 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 3 ↔ 1 := by
    erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a => profiniteToCompHaus.obj (X a)) (fun a 

Depends on / 依赖: CompHaus, CompHaus.effectiveEpiFamily_tfae, Sigma.desc, effectiveEpiFamily_tfae, effectiveEpi_desc_iff_effectiveEpiFamily, effectiveEpi_tfae, finite_effectiveEpiFamily_of_map, profiniteToCompHaus, profiniteToCompHaus.finite_effectiveEpiFamily_of_map, profiniteToCompHaus.map, profiniteToCompHaus.obj, tfae_finish, tfae_have
-/
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : Profinite.{u}}
    (X : α -> Profinite.{u}) (π : (a : α) -> (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , forall b : B, exists (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 -> 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 3 ↔ 1 := by
    erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a => profiniteToCompHaus.obj (X a)) (fun a => profiniteToCompHaus.map (π a))).out 2 0 :)]
    exact ⟨fun h => profiniteToCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
      fun _ => inferInstance⟩
  tfae_finish

/--
theorem `effectiveEpiFamily_of_jointly_surjective` / 定理 `effectiveEpiFamily_of_jointly_surjective`

English:
theorem effectiveEpiFamily_of_jointly_surjective
  proof: ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

中文:
定理 effectiveEpiFamily_of_jointly_surjective
  证明: ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

Depends on / 依赖: effectiveEpiFamily_tfae
-/
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : Profinite.{u}}
    (X : α -> Profinite.{u}) (π : (a : α) -> (X a ⟶ B))
    (surj : forall b : B, exists (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end Profinite
