/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
/-!

# Functors preserving effective epimorphisms

This file concerns functors which preserve and/or reflect effective epimorphisms and effective
epimorphic families.

## TODO
- Find nice sufficient conditions in terms of preserving/reflecting (co)limits, to preserve/reflect
  effective epis, similar to `CategoryTheory.preserves_epi_of_preservesColimit`.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

noncomputable section Equivalence

variable {D : Type*} [Category* D] (e : C ≌ D) {B : C}

variable {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))

/--
theorem `effectiveEpiFamilyStructOfEquivalence_aux` / 定理 `effectiveEpiFamilyStructOfEquivalence_aux`

English:
theorem effectiveEpiFamilyStructOfEquivalence_aux
  statement: {W : D} (ε : (a : α) -> e.functor.obj (X a) ⟶ W)
  proof: by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

中文:
定理 effectiveEpiFamilyStructOfEquivalence_aux
  结论: {W : D} (ε : (a : α) -> e.functor.obj (X a) ⟶ W)
  证明: by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

Depends on / 依赖: Functor, Functor.map_comp, e.functor.map, e.inverse.map, functor, inverse, map_comp
-/
theorem effectiveEpiFamilyStructOfEquivalence_aux {W : D} (ε : (a : α) -> e.functor.obj (X a) ⟶ W)
    (h : forall {Z : D} (a₁ a₂ : α) (g₁ : Z ⟶ e.functor.obj (X a₁)) (g₂ : Z ⟶ e.functor.obj (X a₂)),
      g₁ ≫ e.functor.map (π a₁) = g₂ ≫ e.functor.map (π a₂) -> g₁ ≫ ε a₁ = g₂ ≫ ε a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a => e.unit.app (X a) ≫ e.inverse.map (ε a)) a₁ =
    g₂ ≫ (fun a => e.unit.app (X a) ≫ e.inverse.map (ε a)) a₂ := by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

variable [EffectiveEpiFamily X π]

/--
Definition of `effectiveEpiFamilyStructOfEquivalence` / `effectiveEpiFamilyStructOfEquivalence` 的定义

English:
definition effectiveEpiFamilyStructOfEquivalence
  signature: : EffectiveEpiFamilyStruct (fun a => e.functor.obj (X a))
  body: (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f => f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map,
        Equivalence.counitIso_inv_hom_id_app, Category.comp_id,
        Equivalence.functor_unit_comp_assoc] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a => ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

中文:
定义 effectiveEpiFamilyStructOfEquivalence
  签名: : EffectiveEpiFamilyStruct (fun a => e.functor.obj (X a))
  定义体: (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f => f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map,
        Equivalence.counitIso_inv_hom_id_app, Category.comp_id,
        Equivalence.functor_unit_comp_assoc] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a => ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

Depends on / 依赖: e.toAdjunction.homEquiv, homEquiv, toAdjunction
-/
def effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a => e.functor.obj (X a))
    (fun a => e.functor.map (π a)) where
  desc ε h := (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f => f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map,
        Equivalence.counitIso_inv_hom_id_app, Category.comp_id,
        Equivalence.functor_unit_comp_assoc] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a => e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a => ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

instance (F : C ⥤ D) [F.IsEquivalence] :
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) :=
  ⟨⟨effectiveEpiFamilyStructOfEquivalence F.asEquivalence _ _⟩⟩

example {X B : C} (π : X ⟶ B) (F : C ⥤ D) [F.IsEquivalence] [EffectiveEpi π] :
EffectiveEpi F.map π := inferInstance

end Equivalence

namespace Functor

variable {D : Type*} [Category* D]

section Preserves

/--
Definition of `PreservesEffectiveEpis` / `PreservesEffectiveEpis` 的定义

English:
class PreservesEffectiveEpis
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)

中文:
类 保持EffectiveEpis
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 {X Y : C} (f : X ⟶ Y) [有效满态射 f], 有效满态射 (F.map f)
-/
class PreservesEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphisms if it maps effective
  epimorphisms to effective epimorphisms.
  -/
  preserves : forall {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)

/--
Instance `map_effectiveEpi` / 实例 `map_effectiveEpi`

English:
instance map_effectiveEpi
  signature: (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶ Y)
  body: PreservesEffectiveEpis.preserves f

中文:
实例 map_effectiveEpi
  签名: (F : C ⥤ D) [F.保持EffectiveEpis] {X Y : C} (f : X ⟶ Y)
  定义体: PreservesEffectiveEpis.preserves f

Depends on / 依赖: PreservesEffectiveEpis, PreservesEffectiveEpis.preserves, preserves
-/
instance map_effectiveEpi (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] : EffectiveEpi (F.map f) :=
  PreservesEffectiveEpis.preserves f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsRegularEpiCategory
  signature: D] (F
  body: by
    rw [← isRegularEpi_iff_effectiveEpi]
    apply IsRegularEpiCategory.regularEpiOfEpi

中文:
实例 [是正则满态射范畴
  签名: D] (F
  定义体: by
    rw [← isRegularEpi_iff_effectiveEpi]
    apply IsRegularEpiCategory.regularEpiOfEpi

Depends on / 依赖: IsRegularEpiCategory, IsRegularEpiCategory.regularEpiOfEpi, isRegularEpi_iff_effectiveEpi, regularEpiOfEpi
-/
instance [IsRegularEpiCategory D] (F : C ⥤ D) [F.PreservesEpimorphisms] [Limits.HasPullbacks D] :
    F.PreservesEffectiveEpis where
  preserves _ _ := by
    rw [← isRegularEpi_iff_effectiveEpi]
    apply IsRegularEpiCategory.regularEpiOfEpi

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Applying a functor which preserves pullbacks and effective epimorphisms to a regular epi diagram
of the form `X ×_Y X ⇉ X → Y` gives a regular epi diagram.
-/
@[simps]
/--
Definition of `regularEpiOfPreserves` / `regularEpiOfPreserves` 的定义

English:
definition regularEpiOfPreserves
  signature: {C D : Type*} [Category* C] [Category* D] {X Y : C}
  body: F.obj c.pt
  left := F.map c.fst
  right := F.map c.snd
  w := by rw [← F.map_comp, c.condition]; simp
  isColimit := by
    refine isColimitCoforkOfEffectiveEpi (F.map f) (.mk (F.map c.fst) (F.map c.snd) ?_) ?_
    · simp [← Functor.map_comp, c.condition]
    · refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (isLimitOfPreserves F hc)
      · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
· exact Cone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch

中文:
定义 regularEpiOfPreserves
  签名: {C D : 类型} [范畴* C] [范畴* D] {X Y : C}
  定义体: F.obj c.pt
  left := F.map c.fst
  right := F.map c.snd
  w := by rw [← F.map_comp, c.condition]; simp
  isColimit := by
    refine isColimitCoforkOfEffectiveEpi (F.map f) (.mk (F.map c.fst) (F.map c.snd) ?_) ?_
    · simp [← Functor.map_comp, c.condition]
    · refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (isLimitOfPreserves F hc)
      · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
· exact Cone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch

Depends on / 依赖: F.obj, c.pt
-/
noncomputable def regularEpiOfPreserves {C D : Type*} [Category* C] [Category* D] {X Y : C}
    (f : X ⟶ Y) [EffectiveEpi f] (F : C ⥤ D) [PreservesEffectiveEpis F]
    [PreservesLimitsOfShape WalkingCospan F] (c : PullbackCone f f) (hc : IsLimit c) :
    RegularEpi (F.map f) where
  W := F.obj c.pt
  left := F.map c.fst
  right := F.map c.snd
  w := by rw [← F.map_comp, c.condition]; simp
  isColimit := by
    refine isColimitCoforkOfEffectiveEpi (F.map f) (.mk (F.map c.fst) (F.map c.snd) ?_) ?_
    · simp [← Functor.map_comp, c.condition]
    · refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (isLimitOfPreserves F hc)
      · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
· exact Cone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch

/--
Definition of `PreservesEffectiveEpiFamilies` / `PreservesEffectiveEpiFamilies` 的定义

English:
class PreservesEffectiveEpiFamilies
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π], EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))

中文:
类 保持EffectiveEpiFamilies
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 {α : 类型u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π], EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))
-/
class PreservesEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphic families if it maps effective epimorphic families to
  effective epimorphic families.
  -/
  preserves : forall {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))

/--
Instance `map_effectiveEpiFamily` / 实例 `map_effectiveEpiFamily`

English:
instance map_effectiveEpiFamily
  signature: (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{u} F]
  body: PreservesEffectiveEpiFamilies.preserves X π

中文:
实例 map_effectiveEpiFamily
  签名: (F : C ⥤ D) [保持EffectiveEpiFamilies.{u} F]
  定义体: PreservesEffectiveEpiFamilies.preserves X π

Depends on / 依赖: PreservesEffectiveEpiFamilies, PreservesEffectiveEpiFamilies.preserves, preserves
-/
instance map_effectiveEpiFamily (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{u} F]
    {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) :=
  PreservesEffectiveEpiFamilies.preserves X π

/--
Definition of `PreservesFiniteEffectiveEpiFamilies` / `PreservesFiniteEffectiveEpiFamilies` 的定义

English:
class PreservesFiniteEffectiveEpiFamilies
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π], EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))

中文:
类 保持FiniteEffectiveEpiFamilies
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 {α : 类型} [有限 α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π], EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))
-/
class PreservesFiniteEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves finite effective epimorphic families if it maps finite effective epimorphic
  families to effective epimorphic families.
  -/
  preserves : forall {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))

/--
Instance `map_finite_effectiveEpiFamily` / 实例 `map_finite_effectiveEpiFamily`

English:
instance map_finite_effectiveEpiFamily
  signature: (F : C ⥤ D) [F.PreservesFiniteEffectiveEpiFamilies]
  body: PreservesFiniteEffectiveEpiFamilies.preserves X π

中文:
实例 map_finite_effectiveEpiFamily
  签名: (F : C ⥤ D) [F.保持FiniteEffectiveEpiFamilies]
  定义体: PreservesFiniteEffectiveEpiFamilies.preserves X π

Depends on / 依赖: PreservesFiniteEffectiveEpiFamilies, PreservesFiniteEffectiveEpiFamilies.preserves, preserves
-/
instance map_finite_effectiveEpiFamily (F : C ⥤ D) [F.PreservesFiniteEffectiveEpiFamilies]
    {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) :=
  PreservesFiniteEffectiveEpiFamilies.preserves X π

instance (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{0} F] :
    PreservesFiniteEffectiveEpiFamilies F where
  preserves _ _ := inferInstance

instance (F : C ⥤ D) [PreservesFiniteEffectiveEpiFamilies F] : PreservesEffectiveEpis F where
  preserves _ := inferInstance

instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpiFamilies where
  preserves _ _ := inferInstance

section Composition

variable {E : Type*} [Category* E]

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) (G : D ⥤ E) [PreservesEffectiveEpis F] [PreservesEffectiveEpis G] :
    PreservesEffectiveEpis (F ⋙ G) where
  preserves _ _ := by dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteEffectiveEpiFamilies F]
    [PreservesFiniteEffectiveEpiFamilies G] :
    PreservesFiniteEffectiveEpiFamilies (F ⋙ G) where
  preserves _ _ _ := by dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) (G : D ⥤ E) [PreservesEffectiveEpiFamilies.{u} F]
    [PreservesEffectiveEpiFamilies.{u} G] :
    PreservesEffectiveEpiFamilies.{u} (F ⋙ G) where
  preserves _ _ _ := by dsimp; infer_instance

end Composition

end Preserves

section Reflects

/--
Definition of `ReflectsEffectiveEpis` / `ReflectsEffectiveEpis` 的定义

English:
class ReflectsEffectiveEpis
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall {X Y : C} (f : X ⟶ Y), EffectiveEpi (F.map f) -> EffectiveEpi f

中文:
类 ReflectsEffectiveEpis
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 {X Y : C} (f : X ⟶ Y), 有效满态射 (F.map f) -> 有效满态射 f
-/
class ReflectsEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphisms if morphisms that are mapped to epimorphisms are
  themselves effective epimorphisms.
  -/
  reflects : forall {X Y : C} (f : X ⟶ Y), EffectiveEpi (F.map f) -> EffectiveEpi f

/--
lemma `effectiveEpi_of_map` / 引理 `effectiveEpi_of_map`

English:
lemma effectiveEpi_of_map
  statement: (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y)
  proof: ReflectsEffectiveEpis.reflects f h

中文:
引理 effectiveEpi_of_map
  结论: (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y)
  证明: ReflectsEffectiveEpis.reflects f h

Depends on / 依赖: ReflectsEffectiveEpis, ReflectsEffectiveEpis.reflects, reflects
-/
lemma effectiveEpi_of_map (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    (h : EffectiveEpi (F.map f)) : EffectiveEpi f :=
  ReflectsEffectiveEpis.reflects f h

/--
Definition of `ReflectsEffectiveEpiFamilies` / `ReflectsEffectiveEpiFamilies` 的定义

English:
class ReflectsEffectiveEpiFamilies
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)), EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) -> EffectiveEpiFamily X π

中文:
类 ReflectsEffectiveEpiFamilies
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 {α : 类型u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)), EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) -> EffectiveEpiFamily X π
-/
class ReflectsEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphic families if families that are mapped to effective
  epimorphic families are themselves effective epimorphic families.
  -/
  reflects : forall {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)),
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) ->
    EffectiveEpiFamily X π

/--
lemma `effectiveEpiFamily_of_map` / 引理 `effectiveEpiFamily_of_map`

English:
lemma effectiveEpiFamily_of_map
  statement: (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{u} F]
  proof: ReflectsEffectiveEpiFamilies.reflects X π h

中文:
引理 effectiveEpiFamily_of_map
  结论: (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{u} F]
  证明: ReflectsEffectiveEpiFamilies.reflects X π h

Depends on / 依赖: ReflectsEffectiveEpiFamilies, ReflectsEffectiveEpiFamilies.reflects, reflects
-/
lemma effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{u} F]
    {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    (h : EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))) :
    EffectiveEpiFamily X π :=
  ReflectsEffectiveEpiFamilies.reflects X π h

/--
Definition of `ReflectsFiniteEffectiveEpiFamilies` / `ReflectsFiniteEffectiveEpiFamilies` 的定义

English:
class ReflectsFiniteEffectiveEpiFamilies
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)), EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) -> EffectiveEpiFamily X π

中文:
类 ReflectsFiniteEffectiveEpiFamilies
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 {α : 类型} [有限 α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)), EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) -> EffectiveEpiFamily X π
-/
class ReflectsFiniteEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects finite effective epimorphic families if finite families that are
  mapped to effective epimorphic families are themselves effective epimorphic families.
  -/
  reflects : forall {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)),
    EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a)) ->
    EffectiveEpiFamily X π

/--
lemma `finite_effectiveEpiFamily_of_map` / 引理 `finite_effectiveEpiFamily_of_map`

English:
lemma finite_effectiveEpiFamily_of_map
  statement: (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F]
  proof: ReflectsFiniteEffectiveEpiFamilies.reflects X π h

中文:
引理 finite_effectiveEpiFamily_of_map
  结论: (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F]
  证明: ReflectsFiniteEffectiveEpiFamilies.reflects X π h

Depends on / 依赖: ReflectsFiniteEffectiveEpiFamilies, ReflectsFiniteEffectiveEpiFamilies.reflects, reflects
-/
lemma finite_effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F]
    {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    (h : EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))) :
    EffectiveEpiFamily X π :=
  ReflectsFiniteEffectiveEpiFamilies.reflects X π h

instance (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{0} F] :
    ReflectsFiniteEffectiveEpiFamilies F where
  reflects _ _ h := by
    have := F.effectiveEpiFamily_of_map _ _ h
    infer_instance

instance (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F] : ReflectsEffectiveEpis F where
  reflects _ h := by
    rw [effectiveEpi_iff_effectiveEpiFamily] at h
    have := F.finite_effectiveEpiFamily_of_map _ _ h
    infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) [IsEquivalence F] : F.ReflectsEffectiveEpiFamilies where
  reflects {α B} X π _ := by
    let i : (a : α) -> X a ⟶ (inv F).obj (F.obj (X a)) := fun a => (asEquivalence F).unit.app _
    have : EffectiveEpiFamily X (fun a => (i a) ≫ (inv F).map (F.map (π a))) := inferInstance
    simp only [inv_fun_map, Iso.hom_inv_id_app_assoc, i] at this
    have : EffectiveEpiFamily X (fun a => (π a ≫ (asEquivalence F).unit.app B) ≫
        (asEquivalence F).unitInv.app _) := inferInstance
    simpa

section Composition

variable {E : Type*} [Category* E]

instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsEffectiveEpis F] [ReflectsEffectiveEpis G] :
    ReflectsEffectiveEpis (F ⋙ G) where
  reflects _ h := F.effectiveEpi_of_map _ (G.effectiveEpi_of_map _ h)

instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsFiniteEffectiveEpiFamilies F]
    [ReflectsFiniteEffectiveEpiFamilies G] :
    ReflectsFiniteEffectiveEpiFamilies (F ⋙ G) where
  reflects _ _ h :=
    F.finite_effectiveEpiFamily_of_map _ _ (G.finite_effectiveEpiFamily_of_map _ _ h)

instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsEffectiveEpiFamilies.{u} F]
    [ReflectsEffectiveEpiFamilies.{u} G] :
    ReflectsEffectiveEpiFamilies.{u} (F ⋙ G) where
  reflects _ _ h := F.effectiveEpiFamily_of_map _ _ (G.effectiveEpiFamily_of_map _ _ h)

end Composition

end Reflects

end Functor

end CategoryTheory
