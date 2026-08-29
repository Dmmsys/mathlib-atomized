/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour, Nima Rasekh
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
public import Mathlib.Topology.Category.CompHaus.EffectiveEpi
public import Mathlib.Topology.Category.Stonean.Limits
/-!

# Effective epimorphisms in `Stonean`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `Stonean`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `Stonean` is `Preregular`
and `Precoherent`.

We also prove that for a finite family of morphisms in `Stonean` with fixed
target, the conditions jointly surjective, jointly epimorphic and effective epimorphic are all
equivalent.
-/

@[expose] public section

universe u

open CategoryTheory Limits CompHausLike

namespace Stonean

open List in
/--
theorem `effectiveEpi_tfae` / 定理 `effectiveEpi_tfae`

English:
theorem effectiveEpi_tfae
  proof: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 -> 1 := fun hπ => ⟨⟨effectiveEpiStruct π hπ⟩⟩
  tfae_finish

中文:
定理 effectiveEpi_tfae
  证明: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 -> 1 := fun hπ => ⟨⟨effectiveEpiStruct π hπ⟩⟩
  tfae_finish

Depends on / 依赖: effectiveEpiStruct, epi_iff_surjective, tfae_finish, tfae_have
-/
theorem effectiveEpi_tfae
    {B X : Stonean.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 -> 1 := fun hπ => ⟨⟨effectiveEpiStruct π hπ⟩⟩
  tfae_finish

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Stonean.toCompHaus.PreservesEffectiveEpis
  body: ((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mpr
      (((Stonean.effectiveEpi_tfae f).out 0 2).mp h)

中文:
实例 :
  签名: Stonean.toCompHaus.保持EffectiveEpis
  定义体: ((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mpr
      (((Stonean.effectiveEpi_tfae f).out 0 2).mp h)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, Stonean, Stonean.effectiveEpi_tfae, Stonean.toCompHaus.map, effectiveEpi_tfae, toCompHaus
-/
instance : Stonean.toCompHaus.PreservesEffectiveEpis where
  preserves f h :=
    ((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mpr
      (((Stonean.effectiveEpi_tfae f).out 0 2).mp h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Stonean.toCompHaus.ReflectsEffectiveEpis
  body: ((Stonean.effectiveEpi_tfae f).out 0 2).mpr
      (((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mp h)

中文:
实例 :
  签名: Stonean.toCompHaus.ReflectsEffectiveEpis
  定义体: ((Stonean.effectiveEpi_tfae f).out 0 2).mpr
      (((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mp h)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, Stonean, Stonean.effectiveEpi_tfae, Stonean.toCompHaus.map, effectiveEpi_tfae, toCompHaus
-/
instance : Stonean.toCompHaus.ReflectsEffectiveEpis where
  reflects f h :=
    ((Stonean.effectiveEpi_tfae f).out 0 2).mpr
      (((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mp h)

/--
Definition of `stoneanToCompHausEffectivePresentation` / `stoneanToCompHausEffectivePresentation` 的定义

English:
definition stoneanToCompHausEffectivePresentation
  signature: (X : CompHaus)
  body: X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

中文:
定义 stoneanToCompHausEffectivePresentation
  签名: (X : CompHaus)
  定义体: X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

Depends on / 依赖: X.presentation, presentation
-/
noncomputable def stoneanToCompHausEffectivePresentation (X : CompHaus) :
    Stonean.toCompHaus.EffectivePresentation X where
  p := X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Stonean.toCompHaus.EffectivelyEnough
  body: ⟨stoneanToCompHausEffectivePresentation X⟩

中文:
实例 :
  签名: Stonean.toCompHaus.EffectivelyEnough
  定义体: ⟨stoneanToCompHausEffectivePresentation X⟩

Depends on / 依赖: stoneanToCompHausEffectivePresentation
-/
instance : Stonean.toCompHaus.EffectivelyEnough where
  presentation X := ⟨stoneanToCompHausEffectivePresentation X⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preregular Stonean
  body: Stonean.toCompHaus.reflects_preregular

example : Precoherent Stonean.{u} := inferInstance

中文:
实例 :
  签名: Preregular Stonean
  定义体: Stonean.toCompHaus.reflects_preregular

example : Precoherent Stonean.{u} := inferInstance

Depends on / 依赖: Stonean, Stonean.toCompHaus.reflects_preregular, reflects_preregular, toCompHaus
-/
instance : Preregular Stonean := Stonean.toCompHaus.reflects_preregular

example : Precoherent Stonean.{u} := inferInstance

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
      (fun a => Stonean.toCompHaus.obj (X a)) (fun a => Stonean.toCompHaus.map (π a))).out 2 0 :)]
    exact ⟨fun h => Stonean.toCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
      fun _ => inferInstance⟩
  tfae_finish

中文:
定理 effectiveEpiFamily_tfae
  证明: by
  tfae_have 2 -> 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 3 ↔ 1 := by
    erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a => Stonean.toCompHaus.obj (X a)) (fun a => Stonean.toCompHaus.map (π a))).out 2 0 :)]
    exact ⟨fun h => Stonean.toCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
      fun _ => inferInstance⟩
  tfae_finish

Depends on / 依赖: CompHaus, CompHaus.effectiveEpiFamily_tfae, Sigma.desc, Stonean, Stonean.toCompHaus.finite_effectiveEpiFamily_of_map, Stonean.toCompHaus.map, Stonean.toCompHaus.obj, effectiveEpiFamily_tfae, effectiveEpi_desc_iff_effectiveEpiFamily, effectiveEpi_tfae, finite_effectiveEpiFamily_of_map, tfae_finish, tfae_have, toCompHaus
-/
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : Stonean.{u}}
    (X : α -> Stonean.{u}) (π : (a : α) -> (X a ⟶ B)) :
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
      (fun a => Stonean.toCompHaus.obj (X a)) (fun a => Stonean.toCompHaus.map (π a))).out 2 0 :)]
    exact ⟨fun h => Stonean.toCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
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
    {α : Type} [Finite α] {B : Stonean.{u}}
    (X : α -> Stonean.{u}) (π : (a : α) -> (X a ⟶ B))
    (surj : forall b : B, exists (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end Stonean
