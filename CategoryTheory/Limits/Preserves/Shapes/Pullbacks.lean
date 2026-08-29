/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullbackComparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (G : C ⥤ D)

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: : PullbackCone (G.map f) (G.map g)
  body: PullbackCone.mk (G.map c.fst) (G.map c.snd)
    (by simpa using G.congr_map c.condition)

中文:
缩写 map
  签名: : PullbackCone (G.map f) (G.map g)
  定义体: PullbackCone.mk (G.map c.fst) (G.map c.snd)
    (by simpa using G.congr_map c.condition)

Depends on / 依赖: G.congr_map, G.map, PullbackCone, PullbackCone.mk, c.condition, c.fst, c.snd, condition, congr_map
-/
abbrev map : PullbackCone (G.map f) (G.map g) :=
  PullbackCone.mk (G.map c.fst) (G.map c.snd)
    (by simpa using G.congr_map c.condition)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitMapConeEquiv` / `isLimitMapConeEquiv` 的定义

English:
definition isLimitMapConeEquiv
  signature: :
  body: (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans
IsLimit.equivIsoLimit by
      refine PullbackCone.ext (Iso.refl _) ?_ ?_
      · dsimp only [fst]
        simp
      · dsimp only [snd]
        simp

中文:
定义 isLimitMapConeEquiv
  签名: :
  定义体: (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans
IsLimit.equivIsoLimit by
      refine PullbackCone.ext (Iso.refl _) ?_ ?_
      · dsimp only [fst]
        simp
      · dsimp only [snd]
        simp

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, PullbackCone, PullbackCone.ext, diagramIsoCospan, equivIsoLimit, postcomposeHomEquiv, symm.trans
-/
def isLimitMapConeEquiv :
    IsLimit (mapCone G c) ≃ IsLimit (c.map G) :=
(IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans
IsLimit.equivIsoLimit by
      refine PullbackCone.ext (Iso.refl _) ?_ ?_
      · dsimp only [fst]
        simp
      · dsimp only [snd]
        simp

end PullbackCone

variable (G : C ⥤ D)
variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/--
Definition of `isLimitMapConePullbackConeEquiv` / `isLimitMapConePullbackConeEquiv` 的定义

English:
definition isLimitMapConePullbackConeEquiv
  signature: :
  body: (PullbackCone.mk _ _ comm).isLimitMapConeEquiv G

中文:
定义 isLimitMapConePullbackConeEquiv
  签名: :
  定义体: (PullbackCone.mk _ _ comm).isLimitMapConeEquiv G

Depends on / 依赖: Comon.mk, ComonObj, PullbackCone, PullbackCone.mk, isLimitMapConeEquiv, otimes
-/
def isLimitMapConePullbackConeEquiv :
    IsLimit (mapCone G (PullbackCone.mk h k comm)) ≃
      IsLimit
        (PullbackCone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PullbackCone (G.map f) (G.map g)) :=
  (PullbackCone.mk _ _ comm).isLimitMapConeEquiv G

/--
Definition of `isLimitPullbackConeMapOfIsLimit` / `isLimitPullbackConeMapOfIsLimit` 的定义

English:
definition isLimitPullbackConeMapOfIsLimit
  signature: [PreservesLimit (cospan f g) G]
  body: by rw [← G.map_comp, ← G.map_comp, comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  (PullbackCone.isLimitMapConeEquiv _ G).1 (isLimitOfPreserves G l)

中文:
定义 isLimitPullbackConeMapOfIsLimit
  签名: [保持极限 (cospan f g) G]
  定义体: by rw [← G.map_comp, ← G.map_comp, comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  (PullbackCone.isLimitMapConeEquiv _ G).1 (isLimitOfPreserves G l)

Depends on / 依赖: G.map, G.map_comp, IsLimit, PullbackCone, PullbackCone.isLimitMapConeEquiv, PullbackCone.mk, isLimitMapConeEquiv, isLimitOfPreserves, map_comp
-/
def isLimitPullbackConeMapOfIsLimit [PreservesLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk h k comm)) :
    have : G.map h ≫ G.map f = G.map k ≫ G.map g := by rw [← G.map_comp, ← G.map_comp, comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  (PullbackCone.isLimitMapConeEquiv _ G).1 (isLimitOfPreserves G l)

/--
Definition of `isLimitOfIsLimitPullbackConeMap` / `isLimitOfIsLimitPullbackConeMap` 的定义

English:
definition isLimitOfIsLimitPullbackConeMap
  signature: [ReflectsLimit (cospan f g) G]
  body: isLimitOfReflects G
    ((PullbackCone.isLimitMapConeEquiv (PullbackCone.mk _ _ comm) G).2 l)

中文:
定义 isLimitOfIsLimitPullbackConeMap
  签名: [反映极限 (cospan f g) G]
  定义体: isLimitOfReflects G
    ((PullbackCone.isLimitMapConeEquiv (PullbackCone.mk _ _ comm) G).2 l)

Depends on / 依赖: PullbackCone, PullbackCone.isLimitMapConeEquiv, PullbackCone.mk, isLimitMapConeEquiv, isLimitOfReflects
-/
def isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G.map f = G.map k ≫ G.map g
    by simp only [← G.map_comp, comm]))) : IsLimit (PullbackCone.mk h k comm) :=
  isLimitOfReflects G
    ((PullbackCone.isLimitMapConeEquiv (PullbackCone.mk _ _ comm) G).2 l)

variable (f g) [PreservesLimit (cospan f g) G]

/--
Definition of `isLimitOfHasPullbackOfPreservesLimit` / `isLimitOfHasPullbackOfPreservesLimit` 的定义

English:
definition isLimitOfHasPullbackOfPreservesLimit
  signature: [HasPullback f g]
  body: by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

中文:
定义 isLimitOfHasPullbackOfPreservesLimit
  签名: [HasPullback f g]
  定义体: by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

Depends on / 依赖: G.map, G.map_comp, IsLimit, PullbackCone, PullbackCone.mk, condition, isLimitPullbackConeMapOfIsLimit, map_comp, pullback, pullback.condition, pullback.fst, pullback.snd, pullbackIsPullback
-/
def isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] :
    have : G.map (pullback.fst f g) ≫ G.map f = G.map (pullback.snd f g) ≫ G.map g := by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

/--
lemma `preservesPullback_symmetry` / 引理 `preservesPullback_symmetry`

English:
lemma preservesPullback_symmetry
  statement: PreservesLimit (cospan g f) G where
  proof: ⟨by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @isLimitOfPreserves _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply PullbackCone.isLimitOfFlip
        apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
        exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
      · dsimp
        infer_instance
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl :)⟩

中文:
引理 preservesPullback_symmetry
  结论: 保持极限 (cospan g f) G where
  证明: ⟨by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @isLimitOfPreserves _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply PullbackCone.isLimitOfFlip
        apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
        exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
      · dsimp
        infer_instance
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl :)⟩

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, PullbackCone, PullbackCone.isLimitOfFlip, PullbackCone.isoMk, WalkingCospan, WalkingCospan.Hom.inr, diagramIsoCospan, infer_instance, invFun, isLimitMapConePullbackConeEquiv, isLimitOfFlip, isLimitOfPreserves, naturality, ofIsoLimit, postcomposeHomEquiv, symm.t
-/
lemma preservesPullback_symmetry : PreservesLimit (cospan g f) G where
  preserves {c} hc := ⟨by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @isLimitOfPreserves _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply PullbackCone.isLimitOfFlip
        apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
        exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
      · dsimp
        infer_instance
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl :)⟩

/--
theorem `hasPullback_of_preservesPullback` / 定理 `hasPullback_of_preservesPullback`

English:
theorem hasPullback_of_preservesPullback
  given: [HasPullback f g]
  statement: HasPullback (G.map f) (G.map g)
  proof: ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩

中文:
定理 hasPullback_of_preservesPullback
  条件: [HasPullback f g]
  结论: HasPullback (G.map f) (G.map g)
  证明: ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩

Depends on / 依赖: isLimitPullbackConeMapOfIsLimit, pullbackIsPullback
-/
theorem hasPullback_of_preservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g) :=
  ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/--
Definition of `PreservesPullback.iso` / `PreservesPullback.iso` 的定义

English:
definition PreservesPullback.iso
  signature: : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g)
  body: IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)

@[simp]

中文:
定义 PreservesPullback.iso
  签名: : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g)
  定义体: IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, isLimitOfHasPullbackOfPreservesLimit, limit.isLimit
-/
def PreservesPullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)

@[simp]
/--
theorem `PreservesPullback.iso_hom` / 定理 `PreservesPullback.iso_hom`

English:
theorem PreservesPullback.iso_hom
  statement: (PreservesPullback.iso G f g).hom = pullbackComparison G f g
  proof: rfl

中文:
定理 PreservesPullback.iso_hom
  结论: (PreservesPullback.iso G f g).hom = pullbackComparison G f g
  证明: rfl
-/
theorem PreservesPullback.iso_hom : (PreservesPullback.iso G f g).hom = pullbackComparison G f g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `PreservesPullback.iso_hom_fst` / 定理 `PreservesPullback.iso_hom_fst`

English:
theorem PreservesPullback.iso_hom_fst
  proof: by
  simp [PreservesPullback.iso]

中文:
定理 PreservesPullback.iso_hom_fst
  证明: by
  simp [PreservesPullback.iso]

Depends on / 依赖: PreservesPullback, PreservesPullback.iso
-/
theorem PreservesPullback.iso_hom_fst :
    (PreservesPullback.iso G f g).hom ≫ pullback.fst _ _ = G.map (pullback.fst f g) := by
  simp [PreservesPullback.iso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `PreservesPullback.iso_hom_snd` / 定理 `PreservesPullback.iso_hom_snd`

English:
theorem PreservesPullback.iso_hom_snd
  proof: by
  simp [PreservesPullback.iso]

中文:
定理 PreservesPullback.iso_hom_snd
  证明: by
  simp [PreservesPullback.iso]

Depends on / 依赖: PreservesPullback, PreservesPullback.iso
-/
theorem PreservesPullback.iso_hom_snd :
    (PreservesPullback.iso G f g).hom ≫ pullback.snd _ _ = G.map (pullback.snd f g) := by
  simp [PreservesPullback.iso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PreservesPullback.iso_inv_fst` / 定理 `PreservesPullback.iso_inv_fst`

English:
theorem PreservesPullback.iso_inv_fst
  proof: by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

中文:
定理 PreservesPullback.iso_inv_fst
  证明: by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, PreservesPullback, PreservesPullback.iso, inv_comp_eq
-/
theorem PreservesPullback.iso_inv_fst :
    (PreservesPullback.iso G f g).inv ≫ G.map (pullback.fst f g) = pullback.fst _ _ := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PreservesPullback.iso_inv_snd` / 定理 `PreservesPullback.iso_inv_snd`

English:
theorem PreservesPullback.iso_inv_snd
  proof: by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

中文:
定理 PreservesPullback.iso_inv_snd
  证明: by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, PreservesPullback, PreservesPullback.iso, inv_comp_eq
-/
theorem PreservesPullback.iso_inv_snd :
    (PreservesPullback.iso G f g).inv ≫ G.map (pullback.snd f g) = pullback.snd _ _ := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

/--
Definition of `PullbackCone.isLimitCoyonedaEquiv` / `PullbackCone.isLimitCoyonedaEquiv` 的定义

English:
definition PullbackCone.isLimitCoyonedaEquiv
  signature: (c : PullbackCone f g)
  body: (Cone.isLimitCoyonedaEquiv c).trans
    (Equiv.piCongrRight (fun X => c.isLimitMapConeEquiv (coyoneda.obj X)))

中文:
定义 PullbackCone.isLimitCoyonedaEquiv
  签名: (c : PullbackCone f g)
  定义体: (Cone.isLimitCoyonedaEquiv c).trans
    (Equiv.piCongrRight (fun X => c.isLimitMapConeEquiv (coyoneda.obj X)))

Depends on / 依赖: Cone.isLimitCoyonedaEquiv, Equiv.piCongrRight, c.isLimitMapConeEquiv, coyoneda, coyoneda.obj, isLimitCoyonedaEquiv, isLimitMapConeEquiv, piCongrRight
-/
def PullbackCone.isLimitCoyonedaEquiv (c : PullbackCone f g) :
    IsLimit c ≃ forall (X : Cᵒᵖ), IsLimit (c.map (coyoneda.obj X)) :=
  (Cone.isLimitCoyonedaEquiv c).trans
    (Equiv.piCongrRight (fun X => c.isLimitMapConeEquiv (coyoneda.obj X)))

end Pullback

section Pushout

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PushoutCocone

variable {W X Y : C} {f : W ⟶ X} {g : W ⟶ Y} (c : PushoutCocone f g) (G : C ⥤ D)

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: : PushoutCocone (G.map f) (G.map g)
  body: PushoutCocone.mk (G.map c.inl) (G.map c.inr) (by simpa using G.congr_map c.condition)

中文:
缩写 map
  签名: : PushoutCocone (G.map f) (G.map g)
  定义体: PushoutCocone.mk (G.map c.inl) (G.map c.inr) (by simpa using G.congr_map c.condition)

Depends on / 依赖: G.congr_map, G.map, PushoutCocone, PushoutCocone.mk, c.condition, c.inl, c.inr, condition, congr_map
-/
abbrev map : PushoutCocone (G.map f) (G.map g) :=
  PushoutCocone.mk (G.map c.inl) (G.map c.inr) (by simpa using G.congr_map c.condition)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitMapCoconeEquiv` / `isColimitMapCoconeEquiv` 的定义

English:
definition isColimitMapCoconeEquiv
  signature: :
  body: (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans
IsColimit.equivIsoColimit by
      refine PushoutCocone.ext (Iso.refl _) ?_ ?_
      · dsimp only [inl]
        simp
      · dsimp only [inr]
        simp

中文:
定义 isColimitMapCoconeEquiv
  签名: :
  定义体: (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans
IsColimit.equivIsoColimit by
      refine PushoutCocone.ext (Iso.refl _) ?_ ?_
      · dsimp only [inl]
        simp
      · dsimp only [inr]
        simp

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, PushoutCocone, PushoutCocone.ext, diagramIsoSpan, equivIsoColimit, precomposeHomEquiv, symm.trans
-/
def isColimitMapCoconeEquiv :
    IsColimit (mapCocone G c) ≃ IsColimit (c.map G) :=
(IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans
IsColimit.equivIsoColimit by
      refine PushoutCocone.ext (Iso.refl _) ?_ ?_
      · dsimp only [inl]
        simp
      · dsimp only [inr]
        simp

end PushoutCocone

variable (G : C ⥤ D)
variable {W X Y Z : C} {h : X ⟶ Z} {k : Y ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (comm : f ≫ h = g ≫ k)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitMapCoconePushoutCoconeEquiv` / `isColimitMapCoconePushoutCoconeEquiv` 的定义

English:
definition isColimitMapCoconePushoutCoconeEquiv
  signature: :
  body: (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans
IsColimit.equivIsoColimit
Cocone.ext (Iso.refl _) by
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [Category.comp_id, Category.id_comp, ← G.map_comp]

中文:
定义 isColimitMapCoconePushoutCoconeEquiv
  签名: :
  定义体: (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans
IsColimit.equivIsoColimit
Cocone.ext (Iso.refl _) by
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [Category.comp_id, Category.id_comp, ← G.map_comp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Cocone, Cocone.ext, G.map_comp, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, comp_id, diagramIsoSpan, equivIsoColimit, id_comp, map_comp, precomposeHomEquiv, symm.trans
-/
def isColimitMapCoconePushoutCoconeEquiv :
    IsColimit (mapCocone G (PushoutCocone.mk h k comm)) ≃
      IsColimit
        (PushoutCocone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PushoutCocone (G.map f) (G.map g)) :=
(IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans
IsColimit.equivIsoColimit
Cocone.ext (Iso.refl _) by
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [Category.comp_id, Category.id_comp, ← G.map_comp]

/--
Definition of `isColimitPushoutCoconeMapOfIsColimit` / `isColimitPushoutCoconeMapOfIsColimit` 的定义

English:
definition isColimitPushoutCoconeMapOfIsColimit
  signature: [PreservesColimit (span f g) G]
  body: isColimitMapCoconePushoutCoconeEquiv G comm (isColimitOfPreserves G l)

中文:
定义 isColimitPushoutCoconeMapOfIsColimit
  签名: [保持余极限 (span f g) G]
  定义体: isColimitMapCoconePushoutCoconeEquiv G comm (isColimitOfPreserves G l)

Depends on / 依赖: isColimitMapCoconePushoutCoconeEquiv, isColimitOfPreserves
-/
def isColimitPushoutCoconeMapOfIsColimit [PreservesColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk h k comm)) :
    IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h = G.map g ≫ G.map k
      by simp only [← G.map_comp, comm])) :=
  isColimitMapCoconePushoutCoconeEquiv G comm (isColimitOfPreserves G l)

/--
Definition of `isColimitOfIsColimitPushoutCoconeMap` / `isColimitOfIsColimitPushoutCoconeMap` 的定义

English:
definition isColimitOfIsColimitPushoutCoconeMap
  signature: [ReflectsColimit (span f g) G]
  body: isColimitOfReflects G ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)

中文:
定义 isColimitOfIsColimitPushoutCoconeMap
  签名: [反映余极限 (span f g) G]
  定义体: isColimitOfReflects G ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)

Depends on / 依赖: isColimitMapCoconePushoutCoconeEquiv, isColimitOfReflects
-/
def isColimitOfIsColimitPushoutCoconeMap [ReflectsColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h =
      G.map g ≫ G.map k by simp only [← G.map_comp, comm]))) :
    IsColimit (PushoutCocone.mk h k comm) :=
  isColimitOfReflects G ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)

variable (f g) [PreservesColimit (span f g) G]

/--
Definition of `isColimitOfHasPushoutOfPreservesColimit` / `isColimitOfHasPushoutOfPreservesColimit` 的定义

English:
definition isColimitOfHasPushoutOfPreservesColimit
  signature: [i : HasPushout f g]
  body: isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)

中文:
定义 isColimitOfHasPushoutOfPreservesColimit
  签名: [i : HasPushout f g]
  定义体: isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)

Depends on / 依赖: isColimitPushoutCoconeMapOfIsColimit, pushoutIsPushout
-/
def isColimitOfHasPushoutOfPreservesColimit [i : HasPushout f g] :
    IsColimit (PushoutCocone.mk (G.map (pushout.inl _ _)) (G.map (@pushout.inr _ _ _ _ _ f g i))
    (show G.map f ≫ G.map (pushout.inl _ _) = G.map g ≫ G.map (pushout.inr _ _) by
      simp only [← G.map_comp, pushout.condition])) :=
  isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesPushout_symmetry` / 引理 `preservesPushout_symmetry`

English:
lemma preservesPushout_symmetry
  statement: PreservesColimit (span g f) G where
  proof: ⟨by
    apply (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply IsColimit.ofIsoColimit _ (PushoutCocone.isoMk _).symm
    apply PushoutCocone.isColimitOfFlip
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
    · -- Need to unfold these to allow the `PreservesColimit` instance to be found.
      dsimp only [span_map_fst, span_map_snd]
      exact isColimitOfPreserves _ (PushoutCocone.flipIsColimit hc)⟩

中文:
引理 preservesPushout_symmetry
  结论: 保持余极限 (span g f) G where
  证明: ⟨by
    apply (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply IsColimit.ofIsoColimit _ (PushoutCocone.isoMk _).symm
    apply PushoutCocone.isColimitOfFlip
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
    · -- Need to unfold these to allow the `PreservesColimit` instance to be found.
      dsimp only [span_map_fst, span_map_snd]
      exact isColimitOfPreserves _ (PushoutCocone.flipIsColimit hc)⟩

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, PreservesColimit, PushoutCocone, PushoutCocone.flipIsColimit, PushoutCocone.isColimitOfFlip, PushoutCocone.isoMk, diagramIsoSpan, flipIsColimit, instance, isColimitMapCoconePushoutCoconeEquiv, isColimitOfFlip, isColimitOfPreserves, ofIsoColimit, precomposeHomEquiv, span_map_fst, span_map_snd
-/
lemma preservesPushout_symmetry : PreservesColimit (span g f) G where
  preserves {c} hc := ⟨by
    apply (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply IsColimit.ofIsoColimit _ (PushoutCocone.isoMk _).symm
    apply PushoutCocone.isColimitOfFlip
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
    · -- Need to unfold these to allow the `PreservesColimit` instance to be found.
      dsimp only [span_map_fst, span_map_snd]
      exact isColimitOfPreserves _ (PushoutCocone.flipIsColimit hc)⟩

/--
theorem `hasPushout_of_preservesPushout` / 定理 `hasPushout_of_preservesPushout`

English:
theorem hasPushout_of_preservesPushout
  given: [HasPushout f g]
  statement: HasPushout (G.map f) (G.map g)
  proof: ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩

中文:
定理 hasPushout_of_preservesPushout
  条件: [HasPushout f g]
  结论: HasPushout (G.map f) (G.map g)
  证明: ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩

Depends on / 依赖: isColimitPushoutCoconeMapOfIsColimit, pushoutIsPushout
-/
theorem hasPushout_of_preservesPushout [HasPushout f g] : HasPushout (G.map f) (G.map g) :=
  ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/--
Definition of `PreservesPushout.iso` / `PreservesPushout.iso` 的定义

English:
definition PreservesPushout.iso
  signature: : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g)
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)

@[simp]

中文:
定义 PreservesPushout.iso
  签名: : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g)
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfHasPushoutOfPreservesColimit
-/
def PreservesPushout.iso : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)

@[simp]
/--
theorem `PreservesPushout.iso_hom` / 定理 `PreservesPushout.iso_hom`

English:
theorem PreservesPushout.iso_hom
  statement: (PreservesPushout.iso G f g).hom = pushoutComparison G f g
  proof: rfl

@[reassoc]

中文:
定理 PreservesPushout.iso_hom
  结论: (PreservesPushout.iso G f g).hom = pushoutComparison G f g
  证明: rfl

@[reassoc]
-/
theorem PreservesPushout.iso_hom : (PreservesPushout.iso G f g).hom = pushoutComparison G f g :=
  rfl

@[reassoc]
/--
theorem `PreservesPushout.inl_iso_hom` / 定理 `PreservesPushout.inl_iso_hom`

English:
theorem PreservesPushout.inl_iso_hom
  proof: by
  simp

@[reassoc]

中文:
定理 PreservesPushout.inl_iso_hom
  证明: by
  simp

@[reassoc]
-/
theorem PreservesPushout.inl_iso_hom :
    pushout.inl _ _ ≫ (PreservesPushout.iso G f g).hom = G.map (pushout.inl _ _) := by
  simp

@[reassoc]
/--
theorem `PreservesPushout.inr_iso_hom` / 定理 `PreservesPushout.inr_iso_hom`

English:
theorem PreservesPushout.inr_iso_hom
  proof: by
  simp

中文:
定理 PreservesPushout.inr_iso_hom
  证明: by
  simp
-/
theorem PreservesPushout.inr_iso_hom :
    pushout.inr _ _ ≫ (PreservesPushout.iso G f g).hom = G.map (pushout.inr _ _) := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PreservesPushout.inl_iso_inv` / 定理 `PreservesPushout.inl_iso_inv`

English:
theorem PreservesPushout.inl_iso_inv
  proof: by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

中文:
定理 PreservesPushout.inl_iso_inv
  证明: by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, PreservesPushout, PreservesPushout.iso, comp_inv_eq
-/
theorem PreservesPushout.inl_iso_inv :
    G.map (pushout.inl _ _) ≫ (PreservesPushout.iso G f g).inv = pushout.inl _ _ := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PreservesPushout.inr_iso_inv` / 定理 `PreservesPushout.inr_iso_inv`

English:
theorem PreservesPushout.inr_iso_inv
  proof: by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

中文:
定理 PreservesPushout.inr_iso_inv
  证明: by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, PreservesPushout, PreservesPushout.iso, comp_inv_eq
-/
theorem PreservesPushout.inr_iso_inv :
    G.map (pushout.inr _ _) ≫ (PreservesPushout.iso G f g).inv = pushout.inr _ _ := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

end Pushout

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

section Pullback

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/--
lemma `PreservesPullback.of_iso_comparison` / 引理 `PreservesPullback.of_iso_comparison`

English:
lemma PreservesPullback.of_iso_comparison
  given: [i : IsIso (pullbackComparison G f g)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (cospan (G.map f) (G.map g))) i

中文:
引理 PreservesPullback.of_iso_comparison
  条件: [i : 是同构 (pullbackComparison G f g)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (cospan (G.map f) (G.map g))) i

Depends on / 依赖: G.map, IsLimit, IsLimit.ofPointIso, cospan, isLimit, isLimitMapConePullbackConeEquiv, limit.isLimit, ofPointIso, preservesLimit_of_preserves_limit_cone, pullbackIsPullback
-/
lemma PreservesPullback.of_iso_comparison [i : IsIso (pullbackComparison G f g)] :
    PreservesLimit (cospan f g) G := by
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (cospan (G.map f) (G.map g))) i

variable [PreservesLimit (cospan f g) G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (pullbackComparison G f g)
  body: by
  rw [← PreservesPullback.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (pullbackComparison G f g)
  定义体: by
  rw [← PreservesPullback.iso_hom]
  infer_instance

Depends on / 依赖: PreservesPullback, PreservesPullback.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (pullbackComparison G f g) := by
  rw [← PreservesPullback.iso_hom]
  infer_instance

end Pullback

section Pushout

variable {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/--
lemma `PreservesPushout.of_iso_comparison` / 引理 `PreservesPushout.of_iso_comparison`

English:
lemma PreservesPushout.of_iso_comparison
  given: [i : IsIso (pushoutComparison G f g)]
  proof: by
  apply preservesColimit_of_preserves_colimit_cocone (pushoutIsPushout f g)
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).symm _
  exact IsColimit.ofPointIso _ (i := i)

中文:
引理 PreservesPushout.of_iso_comparison
  条件: [i : 是同构 (pushoutComparison G f g)]
  证明: by
  apply preservesColimit_of_preserves_colimit_cocone (pushoutIsPushout f g)
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).symm _
  exact IsColimit.ofPointIso _ (i := i)

Depends on / 依赖: IsColimit, IsColimit.ofPointIso, isColimitMapCoconePushoutCoconeEquiv, ofPointIso, preservesColimit_of_preserves_colimit_cocone, pushoutIsPushout
-/
lemma PreservesPushout.of_iso_comparison [i : IsIso (pushoutComparison G f g)] :
    PreservesColimit (span f g) G := by
  apply preservesColimit_of_preserves_colimit_cocone (pushoutIsPushout f g)
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).symm _
  exact IsColimit.ofPointIso _ (i := i)

variable [PreservesColimit (span f g) G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (pushoutComparison G f g)
  body: by
  rw [← PreservesPushout.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (pushoutComparison G f g)
  定义体: by
  rw [← PreservesPushout.iso_hom]
  infer_instance

Depends on / 依赖: PreservesPushout, PreservesPushout.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (pushoutComparison G f g) := by
  rw [← PreservesPushout.iso_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `PushoutCocone.isColimitYonedaEquiv` / `PushoutCocone.isColimitYonedaEquiv` 的定义

English:
definition PushoutCocone.isColimitYonedaEquiv
  signature: (c : PushoutCocone f g)
  body: (Limits.Cocone.isColimitYonedaEquiv c).trans
    (Equiv.piCongrRight (fun X =>
      (IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (cospanOp f g).symm (yoneda.obj X)) _).symm.trans
            (Equiv.trans (IsLimit.equivIsoLimit
              (by exact Cone.ext (Iso.refl _) (by rintro (_ | _ | _) <;> cat_disch)))
                (c.op.isLimitMapConeEquiv (yoneda.obj X))))))

中文:
定义 PushoutCocone.isColimitYonedaEquiv
  签名: (c : PushoutCocone f g)
  定义体: (Limits.Cocone.isColimitYonedaEquiv c).trans
    (Equiv.piCongrRight (fun X =>
      (IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (cospanOp f g).symm (yoneda.obj X)) _).symm.trans
            (Equiv.trans (IsLimit.equivIsoLimit
              (by exact Cone.ext (Iso.refl _) (by rintro (_ | _ | _) <;> cat_disch)))
                (c.op.isLimitMapConeEquiv (yoneda.obj X))))))

Depends on / 依赖: Cocone, Cone.ext, Equiv.piCongrRight, Equiv.trans, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, IsLimit.whiskerEquivalenceEquiv, Iso.refl, Limits, Limits.Cocone.isColimitYonedaEquiv, c.op.isLimitMapConeEquiv, cat_disch, cospanOp, equivIsoLimit, isColimitYonedaEquiv, isLimitMapConeEquiv, isoWhiskerRight, piCongrRight, postcomposeHomEquiv
-/
def PushoutCocone.isColimitYonedaEquiv (c : PushoutCocone f g) :
    IsColimit c ≃ forall (X : C), IsLimit (c.op.map (yoneda.obj X)) :=
  (Limits.Cocone.isColimitYonedaEquiv c).trans
    (Equiv.piCongrRight (fun X =>
      (IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (cospanOp f g).symm (yoneda.obj X)) _).symm.trans
            (Equiv.trans (IsLimit.equivIsoLimit
              (by exact Cone.ext (Iso.refl _) (by rintro (_ | _ | _) <;> cat_disch)))
                (c.op.isLimitMapConeEquiv (yoneda.obj X))))))

end Pushout

end

end CategoryTheory.Limits
