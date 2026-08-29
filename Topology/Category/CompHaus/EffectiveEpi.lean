/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHaus.Limits
public import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
/-!

# Effective epimorphisms in `CompHaus`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `CompHaus`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `CompHaus` is `Preregular`
and `Precoherent`.

We also prove that for a finite family of morphisms in `CompHaus` with fixed
target, the conditions jointly surjective, jointly epimorphic and effective epimorphic are all
equivalent.

## Projects

- Define regular categories, and show that `CompHaus` is regular.
- Define coherent categories, and show that `CompHaus` is actually coherent.

-/

public section

universe u

open CategoryTheory Limits CompHausLike

namespace CompHaus

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
    {B X : CompHaus.{u}} (π : X ⟶ B) :
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
  signature: Preregular CompHaus
  body: preregular fun _ _ _ => ((effectiveEpi_tfae _).out 0 2).mp

example : Precoherent CompHaus.{u} := inferInstance

中文:
实例 :
  签名: Preregular CompHaus
  定义体: preregular fun _ _ _ => ((effectiveEpi_tfae _).out 0 2).mp

example : Precoherent CompHaus.{u} := inferInstance

Depends on / 依赖: effectiveEpi_tfae, preregular
-/
instance : Preregular CompHaus :=
  preregular fun _ _ _ => ((effectiveEpi_tfae _).out 0 2).mp

example : Precoherent CompHaus.{u} := inferInstance

set_option backward.isDefEq.respectTransparency false in
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
  tfae_have 1 -> 2
  | _ => inferInstance
  tfae_have 3 -> 2
  | e => by
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 -> 3
  | e => by
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    change _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish

中文:
定理 effectiveEpiFamily_tfae
  证明: by
  tfae_have 2 -> 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 -> 2
  | _ => inferInstance
  tfae_have 3 -> 2
  | e => by
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 -> 3
  | e => by
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    change _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish

Depends on / 依赖: Sigma.desc, coconePointUniqueUpToIso, colimit, colimit.isColimit, effectiveEpi_desc_iff_effectiveEpiFamily, effectiveEpi_tfae, epi_iff_surjective, finiteCoproduct, finiteCoproduct.isColimit, isColimit, tfae_have
-/
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α -> CompHaus.{u}) (π : (a : α) -> (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , forall b : B, exists (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 -> 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 -> 2
  | _ => inferInstance
  tfae_have 3 -> 2
  | e => by
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 -> 3
  | e => by
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    change _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
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
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α -> CompHaus.{u}) (π : (a : α) -> (X a ⟶ B))
    (surj : forall b : B, exists (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end CompHaus
