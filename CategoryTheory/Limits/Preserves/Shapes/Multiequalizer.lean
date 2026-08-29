/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Preservation of multicoequalizers

Let `J : MultispanShape` and `d : MultispanIndex J C`.
If `F : C ⥤ D`, we define `d.map F : MultispanIndex J D` and
an isomorphism of functors `(d.map F).multispan ≅ d.multispan ⋙ F`
(see `MultispanIndex.multispanMapIso`).
If `c : Multicofork d`, we define `c.map F : Multicofork (d.map F)` and
obtain a bijection `IsColimit (F.mapCocone c) ≃ IsColimit (c.map F)`
(see `Multicofork.isColimitMapEquiv`). As a result, if `F` preserves
the colimit of `d.multispan`, we deduce that if `c` is a colimit,
then `c.map F` also is (see `Multicofork.isColimitMapOfPreserves`).

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

namespace Limits

section Multifork

variable {J : MulticospanShape.{w, w'}} (d : MulticospanIndex J C)
  (c : Multifork d) (F : C ⥤ D)

/-- The multicospan index obtained by applying a functor. -/
@[simps]
/--
Definition of `MulticospanIndex.map` / `MulticospanIndex.map` 的定义

English:
definition MulticospanIndex.map
  signature: : MulticospanIndex J D where
  body: F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

中文:
定义 MulticospanIndex.map
  签名: : MulticospanIndex J D where
  定义体: F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

Depends on / 依赖: F.obj, d.left
-/
def MulticospanIndex.map : MulticospanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MulticospanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multicospan ≅ d.multicospan ⋙ F`. -/
@[simps!]
/--
Definition of `MulticospanIndex.multicospanMapIso` / `MulticospanIndex.multicospanMapIso` 的定义

English:
definition MulticospanIndex.multicospanMapIso
  signature: : (d.map F).multicospan ≅ d.multicospan ⋙ F
  body: NatIso.ofComponents
    (fun i => match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro a b (_ | _) <;> simp)

中文:
定义 MulticospanIndex.multicospanMapIso
  签名: : (d.map F).multicospan ≅ d.multicospan ⋙ F
  定义体: NatIso.ofComponents
    (fun i => match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro a b (_ | _) <;> simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def MulticospanIndex.multicospanMapIso : (d.map F).multicospan ≅ d.multicospan ⋙ F :=
  NatIso.ofComponents
    (fun i => match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro a b (_ | _) <;> simp)

variable {d}

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
this is the induced multifork of `d.map F`. -/
@[simps!]
/--
Definition of `Multifork.map` / `Multifork.map` 的定义

English:
definition Multifork.map
  signature: : Multifork (d.map F)
  body: Multifork.ofι _ (F.obj c.pt) (fun i => F.map (c.ι i)) (fun j => by
    dsimp
    rw [← F.map_comp]; rw [← F.map_comp]; rw [condition])

中文:
定义 Multifork.map
  签名: : Multifork (d.map F)
  定义体: Multifork.ofι _ (F.obj c.pt) (fun i => F.map (c.ι i)) (fun j => by
    dsimp
    rw [← F.map_comp]; rw [← F.map_comp]; rw [condition])

Depends on / 依赖: F.map, F.map_comp, F.obj, Multifork, Multifork.of, c.pt, condition, map_comp
-/
def Multifork.map : Multifork (d.map F) :=
  Multifork.ofι _ (F.obj c.pt) (fun i => F.map (c.ι i)) (fun j => by
    dsimp
    rw [← F.map_comp]; rw [← F.map_comp]; rw [condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Multifork.isLimitMapEquiv` / `Multifork.isLimitMapEquiv` 的定义

English:
definition Multifork.isLimitMapEquiv
  signature: :
  body: Equiv.trans (IsLimit.postcomposeInvEquiv (d.multicospanMapIso F) (F.mapCone c)).symm
    (IsLimit.equivIsoLimit
      (Multifork.ext (Iso.refl _) (fun i => by dsimp only [Multifork.ι]; simp)))

中文:
定义 Multifork.isLimitMapEquiv
  签名: :
  定义体: Equiv.trans (IsLimit.postcomposeInvEquiv (d.multicospanMapIso F) (F.mapCone c)).symm
    (IsLimit.equivIsoLimit
      (Multifork.ext (Iso.refl _) (fun i => by dsimp only [Multifork.ι]; simp)))

Depends on / 依赖: Equiv.trans, F.mapCone, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeInvEquiv, Iso.refl, Multifork, Multifork.ext, d.multicospanMapIso, equivIsoLimit, mapCone, multicospanMapIso, postcomposeInvEquiv
-/
def Multifork.isLimitMapEquiv :
    IsLimit (F.mapCone c) ≃ IsLimit (c.map F) :=
  Equiv.trans (IsLimit.postcomposeInvEquiv (d.multicospanMapIso F) (F.mapCone c)).symm
    (IsLimit.equivIsoLimit
      (Multifork.ext (Iso.refl _) (fun i => by dsimp only [Multifork.ι]; simp)))

/--
Definition of `Multifork.isLimitMapOfPreserves` / `Multifork.isLimitMapOfPreserves` 的定义

English:
definition Multifork.isLimitMapOfPreserves
  body: (isLimitMapEquiv c F) (isLimitOfPreserves F hc)

中文:
定义 Multifork.isLimitMapOfPreserves
  定义体: (isLimitMapEquiv c F) (isLimitOfPreserves F hc)

Depends on / 依赖: isLimitMapEquiv, isLimitOfPreserves
-/
noncomputable def Multifork.isLimitMapOfPreserves
    [PreservesLimit d.multicospan F] (hc : IsLimit c) : IsLimit (c.map F) :=
  (isLimitMapEquiv c F) (isLimitOfPreserves F hc)

end Multifork

section Multicofork

variable {J : MultispanShape.{w, w'}} (d : MultispanIndex J C)
  (c : Multicofork d) (F : C ⥤ D)

/-- The multispan index obtained by applying a functor. -/
@[simps]
/--
Definition of `MultispanIndex.map` / `MultispanIndex.map` 的定义

English:
definition MultispanIndex.map
  signature: : MultispanIndex J D where
  body: F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

中文:
定义 MultispanIndex.map
  签名: : MultispanIndex J D where
  定义体: F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

Depends on / 依赖: F.obj, d.left
-/
def MultispanIndex.map : MultispanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MultispanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multispan ≅ d.multispan ⋙ F`. -/
@[simps!]
/--
Definition of `MultispanIndex.multispanMapIso` / `MultispanIndex.multispanMapIso` 的定义

English:
definition MultispanIndex.multispanMapIso
  signature: : (d.map F).multispan ≅ d.multispan ⋙ F
  body: NatIso.ofComponents
    (fun i => match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

中文:
定义 MultispanIndex.multispanMapIso
  签名: : (d.map F).multispan ≅ d.multispan ⋙ F
  定义体: NatIso.ofComponents
    (fun i => match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def MultispanIndex.multispanMapIso : (d.map F).multispan ≅ d.multispan ⋙ F :=
  NatIso.ofComponents
    (fun i => match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

variable {d}

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
this is the induced multicofork of `d.map F`. -/
@[simps!]
/--
Definition of `Multicofork.map` / `Multicofork.map` 的定义

English:
definition Multicofork.map
  signature: : Multicofork (d.map F)
  body: Multicofork.ofπ _ (F.obj c.pt) (fun i => F.map (c.π i)) (fun j => by
    dsimp
    rw [← F.map_comp]; rw [← F.map_comp]; rw [condition])

中文:
定义 Multicofork.map
  签名: : Multicofork (d.map F)
  定义体: Multicofork.ofπ _ (F.obj c.pt) (fun i => F.map (c.π i)) (fun j => by
    dsimp
    rw [← F.map_comp]; rw [← F.map_comp]; rw [condition])

Depends on / 依赖: F.map, F.map_comp, F.obj, Multicofork, Multicofork.of, c.pt, condition, map_comp
-/
def Multicofork.map : Multicofork (d.map F) :=
  Multicofork.ofπ _ (F.obj c.pt) (fun i => F.map (c.π i)) (fun j => by
    dsimp
    rw [← F.map_comp]; rw [← F.map_comp]; rw [condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Multicofork.isColimitMapEquiv` / `Multicofork.isColimitMapEquiv` 的定义

English:
definition Multicofork.isColimitMapEquiv
  signature: :
  body: (IsColimit.precomposeInvEquiv (d.multispanMapIso F).symm (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i => by dsimp only [Multicofork.π]; simp)))

中文:
定义 Multicofork.isColimitMapEquiv
  签名: :
  定义体: (IsColimit.precomposeInvEquiv (d.multispanMapIso F).symm (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i => by dsimp only [Multicofork.π]; simp)))

Depends on / 依赖: F.mapCocone, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeInvEquiv, Iso.refl, Multicofork, Multicofork.ext, d.multispanMapIso, equivIsoColimit, mapCocone, multispanMapIso, precomposeInvEquiv, symm.trans
-/
def Multicofork.isColimitMapEquiv :
    IsColimit (F.mapCocone c) ≃ IsColimit (c.map F) :=
  (IsColimit.precomposeInvEquiv (d.multispanMapIso F).symm (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i => by dsimp only [Multicofork.π]; simp)))

/--
Definition of `Multicofork.isColimitMapOfPreserves` / `Multicofork.isColimitMapOfPreserves` 的定义

English:
definition Multicofork.isColimitMapOfPreserves
  body: (isColimitMapEquiv c F) (isColimitOfPreserves F hc)

中文:
定义 Multicofork.isColimitMapOfPreserves
  定义体: (isColimitMapEquiv c F) (isColimitOfPreserves F hc)

Depends on / 依赖: isColimitMapEquiv, isColimitOfPreserves
-/
noncomputable def Multicofork.isColimitMapOfPreserves
    [PreservesColimit d.multispan F] (hc : IsColimit c) : IsColimit (c.map F) :=
  (isColimitMapEquiv c F) (isColimitOfPreserves F hc)

end Multicofork

end Limits

end CategoryTheory
