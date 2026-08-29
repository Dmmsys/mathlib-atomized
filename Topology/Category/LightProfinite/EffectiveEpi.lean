/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
public import Mathlib.Topology.Category.LightProfinite.Limits
/-!

# Effective epimorphisms in `LightProfinite`

This file proves that `EffectiveEpi` and `Surjective` are equivalent in `LightProfinite`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `LightProfinite` is `Preregular`
and `Precoherent`.
-/

public section

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

/--
theorem `effectiveEpi_iff_surjective` / 定理 `effectiveEpi_iff_surjective`

English:
theorem effectiveEpi_iff_surjective
  given: {X Y : LightProfinite.{u}} (f : X ⟶ Y)
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨⟨effectiveEpiStruct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

中文:
定理 effectiveEpi_iff_surjective
  条件: {X Y : LightProfinite.{u}} (f : X ⟶ Y)
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨⟨effectiveEpiStruct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

Depends on / 依赖: effectiveEpiStruct, epi_iff_surjective, infer_instance
-/
theorem effectiveEpi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h => ?_, fun h => ⟨⟨effectiveEpiStruct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preregular LightProfinite.{u}
  body: by
  apply CompHausLike.preregular
  intro _ _ f
  exact (effectiveEpi_iff_surjective f).mp

example : Precoherent LightProfinite.{u} := inferInstance

中文:
实例 :
  签名: Preregular LightProfinite.{u}
  定义体: by
  apply CompHausLike.preregular
  intro _ _ f
  exact (effectiveEpi_iff_surjective f).mp

example : Precoherent LightProfinite.{u} := inferInstance

Depends on / 依赖: CompHausLike, CompHausLike.preregular, effectiveEpi_iff_surjective, preregular
-/
instance : Preregular LightProfinite.{u} := by
  apply CompHausLike.preregular
  intro _ _ f
  exact (effectiveEpi_iff_surjective f).mp

example : Precoherent LightProfinite.{u} := inferInstance

end LightProfinite
