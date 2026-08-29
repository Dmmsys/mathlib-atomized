/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Adjunctions and limits

A left adjoint preserves colimits (`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`),
and a right adjoint preserves limits (`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`).

Equivalences create and reflect (co)limits.
(`CategoryTheory.Functor.createsLimitsOfIsEquivalence`,
`CategoryTheory.Functor.createsColimitsOfIsEquivalence`,
`CategoryTheory.Functor.reflectsLimits_of_isEquivalence`,
`CategoryTheory.Functor.reflectsColimits_of_isEquivalence`.)

In `CategoryTheory.Adjunction.coconesIso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/

@[expose] public section


open Opposite

namespace CategoryTheory

open CategoryTheory.Functor Limits

universe v u v₁ v₂ v₀ u₁ u₂

namespace Adjunction

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section PreservationColimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ C)

/--
Definition of `functorialityRightAdjoint` / `functorialityRightAdjoint` 的定义

English:
definition functorialityRightAdjoint
  signature: : Cocone (K ⋙ F) ⥤ Cocone K
  body: Cocone.functoriality _ G ⋙
    Cocone.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.unit ≫ (associator _ _ _).inv)

中文:
定义 functorialityRightAdjoint
  签名: : 余锥 (K ⋙ F) ⥤ 余锥 K
  定义体: Cocone.functoriality _ G ⋙
    Cocone.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.unit ≫ (associator _ _ _).inv)

Depends on / 依赖: Cocone, Cocone.functoriality, Cocone.precompose, K.rightUnitor.inv, adj.unit, associator, functoriality, precompose, rightUnitor, whiskerLeft
-/
def functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K :=
  Cocone.functoriality _ G ⋙
    Cocone.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.unit ≫ (associator _ _ _).inv)

attribute [local simp] functorialityRightAdjoint

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
@[simps]
/--
Definition of `functorialityUnit` / `functorialityUnit` 的定义

English:
definition functorialityUnit
  signature: :
  body: { hom := adj.unit.app c.pt }

中文:
定义 functorialityUnit
  签名: :
  定义体: { hom := adj.unit.app c.pt }

Depends on / 依赖: adj.unit.app, c.pt
-/
def functorialityUnit :
    𝟭 (Cocone K) ⟶ Cocone.functoriality _ F ⋙ functorialityRightAdjoint adj K where
  app c := { hom := adj.unit.app c.pt }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
@[simps]
/--
Definition of `functorialityCounit` / `functorialityCounit` 的定义

English:
definition functorialityCounit
  signature: :
  body: { hom := adj.counit.app c.pt }

中文:
定义 functorialityCounit
  签名: :
  定义体: { hom := adj.counit.app c.pt }

Depends on / 依赖: adj.counit.app, c.pt, counit
-/
def functorialityCounit :
    functorialityRightAdjoint adj K ⋙ Cocone.functoriality _ F ⟶ 𝟭 (Cocone (K ⋙ F)) where
  app c := { hom := adj.counit.app c.pt }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `functorialityAdjunction` / `functorialityAdjunction` 的定义

English:
definition functorialityAdjunction
  signature: : Cocone.functoriality K F ⊣ functorialityRightAdjoint adj K where
  body: functorialityUnit adj K
  counit := functorialityCounit adj K

include adj in

中文:
定义 functorialityAdjunction
  签名: : 余锥.functoriality K F ⊣ functorialityRightAdjoint adj K where
  定义体: functorialityUnit adj K
  counit := functorialityCounit adj K

include adj in

Depends on / 依赖: functorialityUnit
-/
def functorialityAdjunction : Cocone.functoriality K F ⊣ functorialityRightAdjoint adj K where
  unit := functorialityUnit adj K
  counit := functorialityCounit adj K

include adj in
/-- A left adjoint preserves colimits. -/
@[stacks 0038]
/--
lemma `leftAdjoint_preservesColimits` / 引理 `leftAdjoint_preservesColimits`

English:
lemma leftAdjoint_preservesColimits
  statement: PreservesColimitsOfSize.{v, u} F where
  proof: { preservesColimit :=
        { preserves := fun hc =>
            ⟨IsColimit.isoUniqueCoconeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsColimit.isoUniqueCoconeMorphism.hom hc _)
                ((adj.functorialityAdjunction _).homEquiv _ _)⟩ } }

noncomputable

中文:
引理 leftAdjoint_preservesColimits
  结论: 保持余limitsOfSize.{v, u} F where
  证明: { preservesColimit :=
        { preserves := fun hc =>
            ⟨IsColimit.isoUniqueCoconeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsColimit.isoUniqueCoconeMorphism.hom hc _)
                ((adj.functorialityAdjunction _).homEquiv _ _)⟩ } }

noncomputable

Depends on / 依赖: Equiv.unique, IsColimit, IsColimit.isoUniqueCoconeMorphism.hom, IsColimit.isoUniqueCoconeMorphism.inv, adj.functorialityAdjunction, functorialityAdjunction, homEquiv, isoUniqueCoconeMorphism, preserves, preservesColimit, unique
-/
lemma leftAdjoint_preservesColimits : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape :=
    { preservesColimit :=
        { preserves := fun hc =>
            ⟨IsColimit.isoUniqueCoconeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsColimit.isoUniqueCoconeMorphism.hom hc _)
                ((adj.functorialityAdjunction _).homEquiv _ _)⟩ } }

noncomputable
/--
Instance `colim_preservesColimits` / 实例 `colim_preservesColimits`

English:
instance colim_preservesColimits
  signature: [HasColimitsOfShape J C]
  body: colimConstAdj.leftAdjoint_preservesColimits

中文:
实例 colim_preservesColimits
  签名: [有形状余极限 J C]
  定义体: colimConstAdj.leftAdjoint_preservesColimits
-/
instance colim_preservesColimits [HasColimitsOfShape J C] :
    PreservesColimits (colim (J := J) (C := C)) :=
  colimConstAdj.leftAdjoint_preservesColimits

-- see Note [lower instance priority]
noncomputable instance (priority := 100) isEquivalence_preservesColimits
    (E : C ⥤ D) [E.IsEquivalence] :
    PreservesColimitsOfSize.{v, u} E :=
  leftAdjoint_preservesColimits E.adjunction

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.reflectsColimits_of_isEquivalence
    (E : D ⥤ C) [E.IsEquivalence] :
    ReflectsColimitsOfSize.{v, u} E where
  reflectsColimitsOfShape :=
    { reflectsColimit :=
        { reflects := fun t =>
          ⟨(isColimitOfPreserves E.inv t).mapCoconeEquiv E.asEquivalence.unitIso.symm⟩ } }

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.createsColimitsOfIsEquivalence (H : D ⥤ C)
    [H.IsEquivalence] :
    CreatesColimitsOfSize.{v, u} H where
  CreatesColimitsOfShape :=
    { CreatesColimit :=
        { lifts := fun c _ =>
            { liftedCocone := mapCoconeInv H c
              validLift := mapCoconeMapCoconeInv H c } } }


-- verify the preserve_colimits instance works as expected:
noncomputable example (E : C ⥤ D) [E.IsEquivalence] (c : Cocone K) (h : IsColimit c) :
    IsColimit (E.mapCocone c) :=
  isColimitOfPreserves E h

/--
theorem `hasColimit_comp_equivalence` / 定理 `hasColimit_comp_equivalence`

English:
theorem hasColimit_comp_equivalence
  given: (E : C ⥤ D) [E.IsEquivalence] [HasColimit K]
  proof: HasColimit.mk
    { cocone := E.mapCocone (colimit.cocone K)
      isColimit := isColimitOfPreserves _ (colimit.isColimit K) }

中文:
定理 hasColimit_comp_equivalence
  条件: (E : C ⥤ D) [E.是等价] [有余极限 K]
  证明: HasColimit.mk
    { cocone := E.mapCocone (colimit.cocone K)
      isColimit := isColimitOfPreserves _ (colimit.isColimit K) }

Depends on / 依赖: E.mapCocone, HasColimit, HasColimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, isColimit, isColimitOfPreserves, mapCocone
-/
theorem hasColimit_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit K] :
    HasColimit (K ⋙ E) :=
  HasColimit.mk
    { cocone := E.mapCocone (colimit.cocone K)
      isColimit := isColimitOfPreserves _ (colimit.isColimit K) }

/--
theorem `hasColimit_of_comp_equivalence` / 定理 `hasColimit_of_comp_equivalence`

English:
theorem hasColimit_of_comp_equivalence
  given: (E : C ⥤ D) [E.IsEquivalence] [HasColimit (K ⋙ E)]
  proof: by
  rw [hasColimit_iff_of_iso
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)]
  exact hasColimit_comp_equivalence (K ⋙ E) E.inv

中文:
定理 hasColimit_of_comp_equivalence
  条件: (E : C ⥤ D) [E.是等价] [有余极限 (K ⋙ E)]
  证明: by
  rw [hasColimit_iff_of_iso
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)]
  exact hasColimit_comp_equivalence (K ⋙ E) E.inv

Depends on / 依赖: E.asEquivalence.unitIso, E.inv, Functor, Functor.rightUnitor, asEquivalence, hasColimit_comp_equivalence, hasColimit_iff_of_iso, isoWhiskerLeft, rightUnitor, unitIso
-/
theorem hasColimit_of_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit (K ⋙ E)] :
    HasColimit K := by
  rw [hasColimit_iff_of_iso
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)]
  exact hasColimit_comp_equivalence (K ⋙ E) E.inv

/--
theorem `hasColimitsOfShape_of_equivalence` / 定理 `hasColimitsOfShape_of_equivalence`

English:
theorem hasColimitsOfShape_of_equivalence
  given: (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D]
  proof: ⟨fun F => hasColimit_of_comp_equivalence F E⟩

中文:
定理 hasColimitsOfShape_of_equivalence
  条件: (E : C ⥤ D) [E.是等价] [有形状余极限 J D]
  证明: ⟨fun F => hasColimit_of_comp_equivalence F E⟩

Depends on / 依赖: hasColimit_of_comp_equivalence
-/
theorem hasColimitsOfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] :
    HasColimitsOfShape J C :=
  ⟨fun F => hasColimit_of_comp_equivalence F E⟩

/--
theorem `has_colimits_of_equivalence` / 定理 `has_colimits_of_equivalence`

English:
theorem has_colimits_of_equivalence
  given: (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D]
  proof: ⟨fun _ _ => hasColimitsOfShape_of_equivalence E⟩

中文:
定理 has_colimits_of_equivalence
  条件: (E : C ⥤ D) [E.是等价] [有余limitsOfSize.{v, u} D]
  证明: ⟨fun _ _ => hasColimitsOfShape_of_equivalence E⟩

Depends on / 依赖: hasColimitsOfShape_of_equivalence
-/
theorem has_colimits_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D] :
    HasColimitsOfSize.{v, u} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_equivalence E⟩

end PreservationColimits

section PreservationLimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ D)

/--
Definition of `functorialityLeftAdjoint` / `functorialityLeftAdjoint` 的定义

English:
definition functorialityLeftAdjoint
  signature: : Cone (K ⋙ G) ⥤ Cone K
  body: Cone.functoriality _ F ⋙
    Cone.postcompose ((associator _ _ _).hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.hom)

中文:
定义 functorialityLeftAdjoint
  签名: : 锥 (K ⋙ G) ⥤ 锥 K
  定义体: Cone.functoriality _ F ⋙
    Cone.postcompose ((associator _ _ _).hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.hom)

Depends on / 依赖: Cone.functoriality, Cone.postcompose, K.rightUnitor.hom, adj.counit, associator, counit, functoriality, postcompose, rightUnitor, whiskerLeft
-/
def functorialityLeftAdjoint : Cone (K ⋙ G) ⥤ Cone K :=
  Cone.functoriality _ F ⋙
    Cone.postcompose ((associator _ _ _).hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.hom)

attribute [local simp] functorialityLeftAdjoint

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
@[simps]
/--
Definition of `functorialityUnit'` / `functorialityUnit'` 的定义

English:
definition functorialityUnit'
  signature: :
  body: { hom := adj.unit.app c.pt }

中文:
定义 functorialityUnit'
  签名: :
  定义体: { hom := adj.unit.app c.pt }

Depends on / 依赖: adj.unit.app, c.pt
-/
def functorialityUnit' :
    𝟭 (Cone (K ⋙ G)) ⟶ functorialityLeftAdjoint adj K ⋙ Cone.functoriality _ G where
  app c := { hom := adj.unit.app c.pt }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
@[simps]
/--
Definition of `functorialityCounit'` / `functorialityCounit'` 的定义

English:
definition functorialityCounit'
  signature: :
  body: { hom := adj.counit.app c.pt }

中文:
定义 functorialityCounit'
  签名: :
  定义体: { hom := adj.counit.app c.pt }

Depends on / 依赖: adj.counit.app, c.pt, counit
-/
def functorialityCounit' :
    Cone.functoriality _ G ⋙ functorialityLeftAdjoint adj K ⟶ 𝟭 (Cone K) where
  app c := { hom := adj.counit.app c.pt }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `functorialityAdjunction'` / `functorialityAdjunction'` 的定义

English:
definition functorialityAdjunction'
  signature: : functorialityLeftAdjoint adj K ⊣ Cone.functoriality K G where
  body: functorialityUnit' adj K
  counit := functorialityCounit' adj K

include adj in

中文:
定义 functorialityAdjunction'
  签名: : functorialityLeftAdjoint adj K ⊣ 锥.functoriality K G where
  定义体: functorialityUnit' adj K
  counit := functorialityCounit' adj K

include adj in

Depends on / 依赖: functorialityUnit
-/
def functorialityAdjunction' : functorialityLeftAdjoint adj K ⊣ Cone.functoriality K G where
  unit := functorialityUnit' adj K
  counit := functorialityCounit' adj K

include adj in
/-- A right adjoint preserves limits. -/
@[stacks 0038]
/--
lemma `rightAdjoint_preservesLimits` / 引理 `rightAdjoint_preservesLimits`

English:
lemma rightAdjoint_preservesLimits
  statement: PreservesLimitsOfSize.{v, u} G where
  proof: { preservesLimit :=
        { preserves := fun hc =>
            ⟨IsLimit.isoUniqueConeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsLimit.isoUniqueConeMorphism.hom hc _)
                ((adj.functorialityAdjunction' _).homEquiv _ _).symm⟩ } }

中文:
引理 rightAdjoint_preservesLimits
  结论: 保持LimitsOfSize.{v, u} G where
  证明: { preservesLimit :=
        { preserves := fun hc =>
            ⟨IsLimit.isoUniqueConeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsLimit.isoUniqueConeMorphism.hom hc _)
                ((adj.functorialityAdjunction' _).homEquiv _ _).symm⟩ } }

Depends on / 依赖: Equiv.unique, IsLimit, IsLimit.isoUniqueConeMorphism.hom, IsLimit.isoUniqueConeMorphism.inv, adj.functorialityAdjunction, functorialityAdjunction, homEquiv, isoUniqueConeMorphism, preserves, preservesLimit, unique
-/
lemma rightAdjoint_preservesLimits : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape :=
    { preservesLimit :=
        { preserves := fun hc =>
            ⟨IsLimit.isoUniqueConeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsLimit.isoUniqueConeMorphism.hom hc _)
                ((adj.functorialityAdjunction' _).homEquiv _ _).symm⟩ } }

/--
Instance `lim_preservesLimits` / 实例 `lim_preservesLimits`

English:
instance lim_preservesLimits
  signature: [HasLimitsOfShape J C]
  body: constLimAdj.rightAdjoint_preservesLimits

中文:
实例 lim_preservesLimits
  签名: [有形状极限 J C]
  定义体: constLimAdj.rightAdjoint_preservesLimits
-/
instance lim_preservesLimits [HasLimitsOfShape J C] :
    PreservesLimits (lim (J := J) (C := C)) :=
  constLimAdj.rightAdjoint_preservesLimits

-- see Note [lower instance priority]
instance (priority := 100) isEquivalencePreservesLimits
    (E : D ⥤ C) [E.IsEquivalence] :
    PreservesLimitsOfSize.{v, u} E :=
  rightAdjoint_preservesLimits E.asEquivalence.symm.toAdjunction

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.reflectsLimits_of_isEquivalence
    (E : D ⥤ C) [E.IsEquivalence] :
    ReflectsLimitsOfSize.{v, u} E where
  reflectsLimitsOfShape :=
    { reflectsLimit :=
        { reflects := fun t =>
            ⟨(isLimitOfPreserves E.inv t).mapConeEquiv E.asEquivalence.unitIso.symm⟩ } }

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.createsLimitsOfIsEquivalence (H : D ⥤ C) [H.IsEquivalence] :
    CreatesLimitsOfSize.{v, u} H where
  CreatesLimitsOfShape :=
    { CreatesLimit :=
        { lifts := fun c _ =>
            { liftedCone := mapConeInv H c
              validLift := mapConeMapConeInv H c } } }


-- verify the preserve_limits instance works as expected:
noncomputable example (E : D ⥤ C) [E.IsEquivalence] (c : Cone K) (h : IsLimit c) :
    IsLimit (E.mapCone c) :=
  isLimitOfPreserves E h

/--
theorem `hasLimit_comp_equivalence` / 定理 `hasLimit_comp_equivalence`

English:
theorem hasLimit_comp_equivalence
  given: (E : D ⥤ C) [E.IsEquivalence] [HasLimit K]
  statement: HasLimit (K ⋙ E)
  proof: HasLimit.mk
    { cone := E.mapCone (limit.cone K)
      isLimit := isLimitOfPreserves _ (limit.isLimit K) }

中文:
定理 hasLimit_comp_equivalence
  条件: (E : D ⥤ C) [E.是等价] [有极限 K]
  结论: 有极限 (K ⋙ E)
  证明: HasLimit.mk
    { cone := E.mapCone (limit.cone K)
      isLimit := isLimitOfPreserves _ (limit.isLimit K) }

Depends on / 依赖: E.mapCone, HasLimit, HasLimit.mk, isLimit, isLimitOfPreserves, limit.cone, limit.isLimit, mapCone
-/
theorem hasLimit_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit K] : HasLimit (K ⋙ E) :=
  HasLimit.mk
    { cone := E.mapCone (limit.cone K)
      isLimit := isLimitOfPreserves _ (limit.isLimit K) }

/--
theorem `hasLimit_of_comp_equivalence` / 定理 `hasLimit_of_comp_equivalence`

English:
theorem hasLimit_of_comp_equivalence
  given: (E : D ⥤ C) [E.IsEquivalence] [HasLimit (K ⋙ E)]
  proof: by
  rw [← hasLimit_iff_of_iso
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)]
  exact hasLimit_comp_equivalence (K ⋙ E) E.inv

中文:
定理 hasLimit_of_comp_equivalence
  条件: (E : D ⥤ C) [E.是等价] [有极限 (K ⋙ E)]
  证明: by
  rw [← hasLimit_iff_of_iso
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)]
  exact hasLimit_comp_equivalence (K ⋙ E) E.inv

Depends on / 依赖: E.asEquivalence.unitIso.symm, E.inv, Functor, Functor.rightUnitor, asEquivalence, hasLimit_comp_equivalence, hasLimit_iff_of_iso, isoWhiskerLeft, rightUnitor, unitIso
-/
theorem hasLimit_of_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit (K ⋙ E)] :
    HasLimit K := by
  rw [← hasLimit_iff_of_iso
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)]
  exact hasLimit_comp_equivalence (K ⋙ E) E.inv

/--
theorem `hasLimitsOfShape_of_equivalence` / 定理 `hasLimitsOfShape_of_equivalence`

English:
theorem hasLimitsOfShape_of_equivalence
  given: (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C]
  proof: ⟨fun F => hasLimit_of_comp_equivalence F E⟩

中文:
定理 hasLimitsOfShape_of_equivalence
  条件: (E : D ⥤ C) [E.是等价] [有形状极限 J C]
  证明: ⟨fun F => hasLimit_of_comp_equivalence F E⟩

Depends on / 依赖: hasLimit_of_comp_equivalence
-/
theorem hasLimitsOfShape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_comp_equivalence F E⟩

/--
theorem `has_limits_of_equivalence` / 定理 `has_limits_of_equivalence`

English:
theorem has_limits_of_equivalence
  given: (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C]
  proof: ⟨fun _ _ => hasLimitsOfShape_of_equivalence E⟩

中文:
定理 has_limits_of_equivalence
  条件: (E : D ⥤ C) [E.是等价] [有LimitsOfSize.{v, u} C]
  证明: ⟨fun _ _ => hasLimitsOfShape_of_equivalence E⟩

Depends on / 依赖: hasLimitsOfShape_of_equivalence
-/
theorem has_limits_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ _ => hasLimitsOfShape_of_equivalence E⟩

end PreservationLimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- auxiliary construction for `coconesIso` -/
@[simp]
/--
Definition of `coconesIsoComponentHom` / `coconesIsoComponentHom` 的定义

English:
definition coconesIsoComponentHom
  signature: {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
  body: (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality j j' f := by
    rw [← adj.homEquiv_naturality_left]; rw [← Functor.comp_map]; rw [t.naturality]
    simp

中文:
定义 coconesIsoComponentHom
  签名: {J : 类型u} [范畴.{v} J] {K : J ⥤ C} (Y : D)
  定义体: (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality j j' f := by
    rw [← adj.homEquiv_naturality_left]; rw [← Functor.comp_map]; rw [t.naturality]
    simp

Depends on / 依赖: K.obj, adj.homEquiv, homEquiv, t.app
-/
def coconesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj Y where
  app j := (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality j j' f := by
    rw [← adj.homEquiv_naturality_left]; rw [← Functor.comp_map]; rw [t.naturality]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- auxiliary construction for `coconesIso` -/
@[simp]
/--
Definition of `coconesIsoComponentInv` / `coconesIsoComponentInv` 的定义

English:
definition coconesIsoComponentInv
  signature: {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
  body: (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm, t.naturality]
    simp

中文:
定义 coconesIsoComponentInv
  签名: {J : 类型u} [范畴.{v} J] {K : J ⥤ C} (Y : D)
  定义体: (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm, t.naturality]
    simp

Depends on / 依赖: K.obj, adj.homEquiv, homEquiv, t.app
-/
def coconesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj Y where
  app j := (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm, t.naturality]
    simp

/-- auxiliary construction for `conesIso` -/
@[simp]
/--
Definition of `conesIsoComponentHom` / `conesIsoComponentHom` 的定义

English:
definition conesIsoComponentHom
  signature: {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
  body: (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right, ← t.naturality, Category.id_comp, Category.id_comp]
    rfl

中文:
定义 conesIsoComponentHom
  签名: {J : 类型u} [范畴.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
  定义体: (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right, ← t.naturality, Category.id_comp, Category.id_comp]
    rfl

Depends on / 依赖: K.obj, adj.homEquiv, homEquiv, t.app
-/
def conesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : (Functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X where
  app j := (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right, ← t.naturality, Category.id_comp, Category.id_comp]
    rfl

/-- auxiliary construction for `conesIso` -/
@[simp]
/--
Definition of `conesIsoComponentInv` / `conesIsoComponentInv` 的定义

English:
definition conesIsoComponentInv
  signature: {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
  body: (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right_symm, ← t.naturality, Category.id_comp, Category.id_comp]

中文:
定义 conesIsoComponentInv
  签名: {J : 类型u} [范畴.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
  定义体: (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right_symm, ← t.naturality, Category.id_comp, Category.id_comp]

Depends on / 依赖: K.obj, adj.homEquiv, homEquiv, t.app
-/
def conesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : ((cones J C).obj (K ⋙ G)).obj X) : (Functor.op F ⋙ (cones J D).obj K).obj X where
  app j := (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right_symm, ← t.naturality, Category.id_comp, Category.id_comp]

end ArbitraryUniverse

variable {C : Type u₁} [Category.{v₀} C] {D : Type u₂} [Category.{v₀} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G)

attribute [local simp] homEquiv_unit homEquiv_counit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/--
Definition of `coconesIso` / `coconesIso` 的定义

English:
definition coconesIso
  signature: {J : Type u} [Category.{v} J] {K : J ⥤ C}
  body: NatIso.ofComponents fun Y =>
    { hom := ↾(coconesIsoComponentHom adj Y)
      inv := ↾(coconesIsoComponentInv adj Y) }

中文:
定义 coconesIso
  签名: {J : 类型u} [范畴.{v} J] {K : J ⥤ C}
  定义体: NatIso.ofComponents fun Y =>
    { hom := ↾(coconesIsoComponentHom adj Y)
      inv := ↾(coconesIsoComponentInv adj Y) }

Depends on / 依赖: NatIso, NatIso.ofComponents, coconesIsoComponentHom, coconesIsoComponentInv, ofComponents
-/
def coconesIso {J : Type u} [Category.{v} J] {K : J ⥤ C} :
    (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K) :=
  NatIso.ofComponents fun Y =>
    { hom := ↾(coconesIsoComponentHom adj Y)
      inv := ↾(coconesIsoComponentInv adj Y) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/--
Definition of `conesIso` / `conesIso` 的定义

English:
definition conesIso
  signature: {J : Type u} [Category.{v} J] {K : J ⥤ D}
  body: NatIso.ofComponents fun X =>
    { hom := ↾(conesIsoComponentHom adj X)
      inv := ↾(conesIsoComponentInv adj X) }

中文:
定义 conesIso
  签名: {J : 类型u} [范畴.{v} J] {K : J ⥤ D}
  定义体: NatIso.ofComponents fun X =>
    { hom := ↾(conesIsoComponentHom adj X)
      inv := ↾(conesIsoComponentInv adj X) }

Depends on / 依赖: NatIso, NatIso.ofComponents, conesIsoComponentHom, conesIsoComponentInv, ofComponents
-/
def conesIso {J : Type u} [Category.{v} J] {K : J ⥤ D} :
    F.op ⋙ (cones J D).obj K ≅ (cones J C).obj (K ⋙ G) :=
  NatIso.ofComponents fun X =>
    { hom := ↾(conesIsoComponentHom adj X)
      inv := ↾(conesIsoComponentInv adj X) }

end Adjunction

namespace Functor

variable {J C D : Type*} [Category* J] [Category* C] [Category* D]
  (F : C ⥤ D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLeftAdjoint
  signature: F] : PreservesColimitsOfShape J F
  body: (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape

中文:
实例 [是左伴随
  签名: F] : 保持形状余极限 J F
  定义体: (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, leftAdjoint_preservesColimits, leftAdjoint_preservesColimits.preservesColimitsOfShape, ofIsLeftAdjoint, preservesColimitsOfShape
-/
noncomputable instance [IsLeftAdjoint F] : PreservesColimitsOfShape J F :=
  (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLeftAdjoint
  signature: F] : PreservesColimitsOfSize.{v, u} F where

中文:
实例 [是左伴随
  签名: F] : 保持余limitsOfSize.{v, u} F where
-/
noncomputable instance [IsLeftAdjoint F] : PreservesColimitsOfSize.{v, u} F where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsRightAdjoint
  signature: F] : PreservesLimitsOfShape J F
  body: (Adjunction.ofIsRightAdjoint F).rightAdjoint_preservesLimits.preservesLimitsOfShape

中文:
实例 [是右伴随
  签名: F] : 保持形状极限 J F
  定义体: (Adjunction.ofIsRightAdjoint F).rightAdjoint_preservesLimits.preservesLimitsOfShape

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint, preservesLimitsOfShape, rightAdjoint_preservesLimits, rightAdjoint_preservesLimits.preservesLimitsOfShape
-/
noncomputable instance [IsRightAdjoint F] : PreservesLimitsOfShape J F :=
  (Adjunction.ofIsRightAdjoint F).rightAdjoint_preservesLimits.preservesLimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsRightAdjoint
  signature: F] : PreservesLimitsOfSize.{v, u} F where

中文:
实例 [是右伴随
  签名: F] : 保持LimitsOfSize.{v, u} F where
-/
noncomputable instance [IsRightAdjoint F] : PreservesLimitsOfSize.{v, u} F where

end Functor

end CategoryTheory
