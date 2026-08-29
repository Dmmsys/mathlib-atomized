/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.DiscreteQuotient

/-!
# Profinite sets as limits of finite sets.

We show that any profinite set is isomorphic to the limit of its
discrete (hence finite) quotients.

## Definitions

There are a handful of definitions in this file, given `X : Profinite`:
1. `X.fintypeDiagram` is the functor `DiscreteQuotient X ⥤ FintypeCat` whose limit
  is isomorphic to `X` (the limit taking place in `Profinite` via `FintypeCat.toProfinite`, see 2).
2. `X.diagram` is an abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`.
3. `X.asLimitCone` is the cone over `X.diagram` whose cone point is `X`.
4. `X.isoAsLimitConeLift` is the isomorphism `X ≅ (Profinite.limitCone X.diagram).X` induced
  by lifting `X.asLimitCone`.
5. `X.asLimitConeIso` is the isomorphism `X.asLimitCone ≅ (Profinite.limitCone X.diagram)`
  induced by `X.isoAsLimitConeLift`.
6. `X.asLimit` is a term of type `IsLimit X.asLimitCone`.
7. `X.lim : CategoryTheory.Limits.LimitCone X.asLimitCone` is a bundled combination of 3 and 6.

-/

@[expose] public section


noncomputable section

open CategoryTheory

namespace Profinite

universe u

variable (X : Profinite.{u})

/--
Definition of `fintypeDiagram` / `fintypeDiagram` 的定义

English:
definition fintypeDiagram
  signature: : DiscreteQuotient X ⥤ FintypeCat where
  body: FintypeCat.of S
  map f := FintypeCat.homMk (DiscreteQuotient.ofLE f.le)

中文:
定义 fintypeDiagram
  签名: : DiscreteQuotient X ⥤ FintypeCat where
  定义体: FintypeCat.of S
  map f := FintypeCat.homMk (DiscreteQuotient.ofLE f.le)

Depends on / 依赖: FintypeCat, FintypeCat.of
-/
def fintypeDiagram : DiscreteQuotient X ⥤ FintypeCat where
  obj S := FintypeCat.of S
  map f := FintypeCat.homMk (DiscreteQuotient.ofLE f.le)

/--
Definition of `diagram` / `diagram` 的定义

English:
abbreviation diagram
  signature: : DiscreteQuotient X ⥤ Profinite
  body: X.fintypeDiagram ⋙ FintypeCat.toProfinite

中文:
缩写 diagram
  签名: : DiscreteQuotient X ⥤ Profinite
  定义体: X.fintypeDiagram ⋙ FintypeCat.toProfinite

Depends on / 依赖: FintypeCat, FintypeCat.toProfinite, X.fintypeDiagram, fintypeDiagram, toProfinite
-/
abbrev diagram : DiscreteQuotient X ⥤ Profinite :=
  X.fintypeDiagram ⋙ FintypeCat.toProfinite

/--
Definition of `asLimitCone` / `asLimitCone` 的定义

English:
definition asLimitCone
  signature: : CategoryTheory.Limits.Cone X.diagram
  body: { pt := X
    π := { app := fun S => CompHausLike.ofHom (Y := X.diagram.obj S) _
            ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }

中文:
定义 asLimitCone
  签名: : 范畴论.Limits.锥 X.diagram
  定义体: { pt := X
    π := { app := fun S => CompHausLike.ofHom (Y := X.diagram.obj S) _
            ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }

Depends on / 依赖: CompHausLike, CompHausLike.ofHom, IsLocallyConstant, IsLocallyConstant.continuous, S.proj, S.proj_isLocallyConstant, X.diagram.obj, continuous, diagram, proj_isLocallyConstant
-/
def asLimitCone : CategoryTheory.Limits.Cone X.diagram :=
  { pt := X
    π := { app := fun S => CompHausLike.ofHom (Y := X.diagram.obj S) _
            ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_asLimitCone_lift` / 实例 `isIso_asLimitCone_lift`

English:
instance isIso_asLimitCone_lift
  signature: : IsIso ((limitConeIsLimit.{u, u} X.diagram).lift X.asLimitCone)
  body: CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine DiscreteQuotient.eq_of_forall_proj_eq fun S => ?_
        apply_fun fun f : (limitCone.{u, u} X.diagram).pt => f.val S at h
        exact h
      · obtain ⟨b, hb⟩ :=
          DiscreteQuotient.exists

中文:
实例 isIso_asLimitCone_lift
  签名: : 是同构 ((limitConeIsLimit.{u, u} X.diagram).lift X.asLimitCone)
  定义体: CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine DiscreteQuotient.eq_of_forall_proj_eq fun S => ?_
        apply_fun fun f : (limitCone.{u, u} X.diagram).pt => f.val S at h
        exact h
      · obtain ⟨b, hb⟩ :=
          DiscreteQuotient.exists

Depends on / 依赖: CompHausLike, CompHausLike.isIso_of_bijective, DiscreteQuotient, DiscreteQuotient.eq_of_forall_proj_eq, DiscreteQuotient.exists_of_compat, X.diagram, a.prop, a.val, apply_fun, diagram, eq_of_forall_proj_eq, exists_of_compat, f.val, homOfLE, isIso_of_bijective, limitCone
-/
instance isIso_asLimitCone_lift : IsIso ((limitConeIsLimit.{u, u} X.diagram).lift X.asLimitCone) :=
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine DiscreteQuotient.eq_of_forall_proj_eq fun S => ?_
        apply_fun fun f : (limitCone.{u, u} X.diagram).pt => f.val S at h
        exact h
      · obtain ⟨b, hb⟩ :=
          DiscreteQuotient.exists_of_compat (fun S => a.val S) fun _ _ h => a.prop (homOfLE h)
        use b
        -- ext S : 3 -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` does not work, replaced with following
        -- three lines.
        apply Subtype.ext
        apply funext
        rintro S
        -- Porting note: end replacement block
        apply hb)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoAsLimitConeLift` / `isoAsLimitConeLift` 的定义

English:
definition isoAsLimitConeLift
  signature: : X ≅ (limitCone.{u, u} X.diagram).pt
  body: asIso (limitConeIsLimit.{u, u} _).lift X.asLimitCone

中文:
定义 isoAsLimitConeLift
  签名: : X ≅ (limitCone.{u, u} X.diagram).pt
  定义体: asIso (limitConeIsLimit.{u, u} _).lift X.asLimitCone

Depends on / 依赖: X.asLimitCone, asLimitCone, limitConeIsLimit
-/
def isoAsLimitConeLift : X ≅ (limitCone.{u, u} X.diagram).pt :=
asIso (limitConeIsLimit.{u, u} _).lift X.asLimitCone

/--
Definition of `asLimitConeIso` / `asLimitConeIso` 的定义

English:
definition asLimitConeIso
  signature: : X.asLimitCone ≅ limitCone.{u, u} _
  body: Limits.Cone.ext (isoAsLimitConeLift _) fun _ => rfl

中文:
定义 asLimitConeIso
  签名: : X.asLimitCone ≅ limitCone.{u, u} _
  定义体: Limits.Cone.ext (isoAsLimitConeLift _) fun _ => rfl

Depends on / 依赖: Limits, Limits.Cone.ext, isoAsLimitConeLift
-/
def asLimitConeIso : X.asLimitCone ≅ limitCone.{u, u} _ :=
  Limits.Cone.ext (isoAsLimitConeLift _) fun _ => rfl

/--
Definition of `asLimit` / `asLimit` 的定义

English:
definition asLimit
  signature: : CategoryTheory.Limits.IsLimit X.asLimitCone
  body: Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm

中文:
定义 asLimit
  签名: : 范畴论.Limits.是极限 X.asLimitCone
  定义体: Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm

Depends on / 依赖: IsLimit, Limits, Limits.IsLimit.ofIsoLimit, X.asLimitConeIso.symm, asLimitConeIso, limitConeIsLimit, ofIsoLimit
-/
def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm

/--
Definition of `lim` / `lim` 的定义

English:
definition lim
  signature: : Limits.LimitCone X.diagram
  body: ⟨X.asLimitCone, X.asLimit⟩

中文:
定义 lim
  签名: : Limits.极限锥 X.diagram
  定义体: ⟨X.asLimitCone, X.asLimit⟩

Depends on / 依赖: X.asLimit, X.asLimitCone, asLimit, asLimitCone
-/
def lim : Limits.LimitCone X.diagram :=
  ⟨X.asLimitCone, X.asLimit⟩

end Profinite
