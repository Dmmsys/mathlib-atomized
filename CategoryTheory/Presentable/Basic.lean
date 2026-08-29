/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-! # Presentable objects

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsCardinalAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category
(that is essentially small relative to the universe `w` such that `κ : Cardinal.{w}`.).
We also introduce another typeclass `Functor.IsAccessible` saying that there exists
a regular cardinal `κ` such that `Functor.IsCardinalAccessible`.

An object `X` of a category is `κ`-presentable (`IsCardinalPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.
Similarly as for accessible functors, we define a type class `IsAccessible`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe t w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

section

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/--
Definition of `IsCardinalAccessible` / `IsCardinalAccessible` 的定义

English:
class IsCardinalAccessible
  parameters: : Prop where
  axioms and operations (1):
    - preservesColimitOfShape((J : Type w) [SmallCategory J] [IsCardinalFiltered J κ]) : PreservesColimitsOfShape J F  [default: by intros; infer_instance]

中文:
类 IsCardinalAccessible
  参数: : 命题 where
  公理与运算 (1 个):
    - preservesColimitOfShape((J : Type w) [SmallCategory J] [IsCardinalFiltered J κ]) : PreservesColimitsOfShape J F  [默认: by intros; infer_instance]

Depends on / 依赖: infer_instance, intros
-/
class IsCardinalAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by intros; infer_instance

/--
lemma `preservesColimitsOfShape_of_isCardinalAccessible` / 引理 `preservesColimitsOfShape_of_isCardinalAccessible`

English:
lemma preservesColimitsOfShape_of_isCardinalAccessible
  statement: [F.IsCardinalAccessible κ]
  proof: IsCardinalAccessible.preservesColimitOfShape κ _

中文:
引理 preservesColimitsOfShape_of_isCardinalAccessible
  结论: [F.IsCardinalAccessible κ]
  证明: IsCardinalAccessible.preservesColimitOfShape κ _

Depends on / 依赖: IsCardinalAccessible, IsCardinalAccessible.preservesColimitOfShape, preservesColimitOfShape
-/
lemma preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsCardinalAccessible.preservesColimitOfShape κ _

/--
lemma `preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall` / 引理 `preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall`

English:
lemma preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
  proof: by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

中文:
引理 preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
  证明: by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

Depends on / 依赖: F.preservesColimitsOfShape_of_isCardinalAccessible, IsCardinalFiltered, IsCardinalFiltered.of_equivalence, SmallModel, equivSmallModel, of_equivalence, preservesColimitsOfShape_of_equiv, preservesColimitsOfShape_of_isCardinalAccessible
-/
lemma preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    [F.IsCardinalAccessible κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

variable {κ} in
/--
lemma `isCardinalAccessible_of_le` / 引理 `isCardinalAccessible_of_le`

English:
lemma isCardinalAccessible_of_le
  proof: by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in

中文:
引理 isCardinalAccessible_of_le
  证明: by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in

Depends on / 依赖: F.preservesColimitsOfShape_of_isCardinalAccessible, IsCardinalFiltered, IsCardinalFiltered.of_le, of_le, preservesColimitsOfShape_of_isCardinalAccessible
-/
lemma isCardinalAccessible_of_le
    [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ') :
    F.IsCardinalAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in
variable {F G} in
/--
lemma `isCardinalAccessible_of_natIso` / 引理 `isCardinalAccessible_of_natIso`

English:
lemma isCardinalAccessible_of_natIso
  given: [F.IsCardinalAccessible κ]
  statement: G.IsCardinalAccessible κ where
  proof: by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

中文:
引理 isCardinalAccessible_of_natIso
  条件: [F.IsCardinalAccessible κ]
  结论: G.IsCardinalAccessible κ where
  证明: by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

Depends on / 依赖: F.preservesColimitsOfShape_of_isCardinalAccessible, preservesColimitsOfShape_of_isCardinalAccessible, preservesColimitsOfShape_of_natIso
-/
lemma isCardinalAccessible_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where
  preservesColimitOfShape J _ hκ := by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCardinalAccessible (𝟭 C) κ

中文:
实例 :
  签名: IsCardinalAccessible (𝟭 C) κ
-/
instance : IsCardinalAccessible (𝟭 C) κ where

instance {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] :
    (F ⋙ G).IsCardinalAccessible κ := by
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ
  have := G.preservesColimitsOfShape_of_isCardinalAccessible κ
  exact { }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesColimitsOfSize.{w,
  signature: w} F] : F.IsCardinalAccessible κ where

中文:
实例 [PreservesColimitsOfSize.{w,
  签名: w} F] : F.IsCardinalAccessible κ where
-/
instance [PreservesColimitsOfSize.{w, w} F] : F.IsCardinalAccessible κ where

set_option backward.defeqAttrib.useBackward true in
instance (A : C) : IsCardinalAccessible ((Functor.const C).obj A) κ where
  preservesColimitOfShape J _ _ :=
    { preservesColimit {F} :=
        { preserves {c} hc := ⟨by
            have h := isFiltered_of_isCardinalFiltered J κ
            have (j : J) : IsIso ((((const C).obj A).mapCocone c).ι.app j) := by
              dsimp
              infer_instance
            exact Functor.IsEventuallyConstantFrom.isColimitOfIsIso
              (i₀ := h.nonempty.some) (fun _ _ => by dsimp; infer_instance) _⟩ } }

end

section

variable (F : C ⥤ D)

/-- A functor is accessible relative to a universe `w` if
it is `κ`-accessible for some regular `κ : Cardinal.{w}`. -/
@[pp_with_univ]
/--
Definition of `IsAccessible` / `IsAccessible` 的定义

English:
class IsAccessible
  parameters: : Prop where
  axioms and operations (1):
    - exists_cardinal : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessible F κ

中文:
类 IsAccessible
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_cardinal : 存在 (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessible F κ
-/
class IsAccessible : Prop where
  exists_cardinal : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessible F κ

/--
lemma `isAccessible_of_isCardinalAccessible` / 引理 `isAccessible_of_isCardinalAccessible`

English:
lemma isAccessible_of_isCardinalAccessible
  statement: (κ : Cardinal.{w}) [Fact κ.IsRegular]
  proof: ⟨κ, inferInstance, inferInstance⟩

中文:
引理 isAccessible_of_isCardinalAccessible
  结论: (κ : Cardinal.{w}) [Fact κ.IsRegular]
  证明: ⟨κ, inferInstance, inferInstance⟩
-/
lemma isAccessible_of_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessible F κ] : IsAccessible.{w} F where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

instance {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) [IsAccessible.{w} F]
    [IsAccessible.{w} G] : IsAccessible.{w} (F ⋙ G) := by
  obtain ⟨κF, _, _⟩ := IsAccessible.exists_cardinal (F := F)
  obtain ⟨κG, _, _⟩ := IsAccessible.exists_cardinal (F := G)
  have : Fact (κF ⊔ κG).IsRegular := ⟨iteInduction (fun _ => Fact.out) (fun _ => Fact.out)⟩
  have := isCardinalAccessible_of_le F (by simp : κF <= κF ⊔ κG)
  have := isCardinalAccessible_of_le G (by simp : κG <= κF ⊔ κG)
  exact isAccessible_of_isCardinalAccessible (F ⋙ G) (κF ⊔ κG)

instance (A : C) : IsAccessible.{w} ((Functor.const C).obj A) := by
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

end

end Functor

section

variable (X : C) (Y : C) (e : X ≅ Y) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/--
Definition of `IsCardinalPresentable` / `IsCardinalPresentable` 的定义

English:
abbreviation IsCardinalPresentable
  signature: : Prop
  body: (coyoneda.obj (op X)).IsCardinalAccessible κ

中文:
缩写 IsCardinalPresentable
  签名: : 命题
  定义体: (coyoneda.obj (op X)).IsCardinalAccessible κ

Depends on / 依赖: IsCardinalAccessible, coyoneda, coyoneda.obj
-/
abbrev IsCardinalPresentable : Prop := (coyoneda.obj (op X)).IsCardinalAccessible κ

variable (C) in
/--
Definition of `isCardinalPresentable` / `isCardinalPresentable` 的定义

English:
definition isCardinalPresentable
  signature: : ObjectProperty C
  body: fun X => IsCardinalPresentable X κ

中文:
定义 isCardinalPresentable
  签名: : Object命题erty C
  定义体: fun X => IsCardinalPresentable X κ

Depends on / 依赖: IsCardinalPresentable
-/
def isCardinalPresentable : ObjectProperty C := fun X => IsCardinalPresentable X κ

instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable X.obj κ :=
  X.property

instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable ((isCardinalPresentable C κ).ι.obj X) κ := by
  dsimp
  infer_instance

/--
lemma `isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj` / 引理 `isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj`

English:
lemma isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj
  proof: Iff.rfl

中文:
引理 isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj :
    IsCardinalPresentable X κ ↔ (coyoneda.obj (op X)).IsCardinalAccessible κ := Iff.rfl

/--
lemma `isCardinalPresentable_iff` / 引理 `isCardinalPresentable_iff`

English:
lemma isCardinalPresentable_iff
  given: (X : C)
  proof: Iff.rfl

中文:
引理 isCardinalPresentable_iff
  条件: (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCardinalPresentable_iff (X : C) :
    isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ := Iff.rfl

/--
lemma `preservesColimitsOfShape_of_isCardinalPresentable` / 引理 `preservesColimitsOfShape_of_isCardinalPresentable`

English:
lemma preservesColimitsOfShape_of_isCardinalPresentable
  statement: [IsCardinalPresentable X κ]
  proof: (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J

中文:
引理 preservesColimitsOfShape_of_isCardinalPresentable
  结论: [IsCardinalPresentable X κ]
  证明: (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J

Depends on / 依赖: coyoneda, coyoneda.obj, preservesColimitsOfShape_of_isCardinalAccessible
-/
lemma preservesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X κ]
    (J : Type w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J

/--
lemma `preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall` / 引理 `preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall`

English:
lemma preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
  proof: (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J

中文:
引理 preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
  证明: (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J

Depends on / 依赖: coyoneda, coyoneda.obj, preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
-/
lemma preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
    [IsCardinalPresentable X κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J

variable {κ} in
/--
lemma `isCardinalPresentable_of_le` / 引理 `isCardinalPresentable_of_le`

English:
lemma isCardinalPresentable_of_le
  statement: [IsCardinalPresentable X κ]
  proof: (coyoneda.obj (op X)).isCardinalAccessible_of_le h

中文:
引理 isCardinalPresentable_of_le
  结论: [IsCardinalPresentable X κ]
  证明: (coyoneda.obj (op X)).isCardinalAccessible_of_le h

Depends on / 依赖: coyoneda, coyoneda.obj, isCardinalAccessible_of_le
-/
lemma isCardinalPresentable_of_le [IsCardinalPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ') :
    IsCardinalPresentable X κ' :=
  (coyoneda.obj (op X)).isCardinalAccessible_of_le h

variable (C) {κ} in
/--
lemma `isCardinalPresentable_monotone` / 引理 `isCardinalPresentable_monotone`

English:
lemma isCardinalPresentable_monotone
  given: {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ')
  proof: by
  intro X hX
  rw [isCardinalPresentable_iff] at hX ⊢
  exact isCardinalPresentable_of_le _ h

include e in

中文:
引理 isCardinalPresentable_monotone
  条件: {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ')
  证明: by
  intro X hX
  rw [isCardinalPresentable_iff] at hX ⊢
  exact isCardinalPresentable_of_le _ h

include e in

Depends on / 依赖: isCardinalPresentable_iff, isCardinalPresentable_of_le
-/
lemma isCardinalPresentable_monotone {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ') :
    isCardinalPresentable C κ <= isCardinalPresentable C κ' := by
  intro X hX
  rw [isCardinalPresentable_iff] at hX ⊢
  exact isCardinalPresentable_of_le _ h

include e in
variable {X Y} in
/--
lemma `isCardinalPresentable_of_iso` / 引理 `isCardinalPresentable_of_iso`

English:
lemma isCardinalPresentable_of_iso
  given: [IsCardinalPresentable X κ]
  statement: IsCardinalPresentable Y κ
  proof: Functor.isCardinalAccessible_of_natIso (coyoneda.mapIso e.symm.op) κ

中文:
引理 isCardinalPresentable_of_iso
  条件: [IsCardinalPresentable X κ]
  结论: IsCardinalPresentable Y κ
  证明: Functor.isCardinalAccessible_of_natIso (coyoneda.mapIso e.symm.op) κ

Depends on / 依赖: Functor, Functor.isCardinalAccessible_of_natIso, coyoneda, coyoneda.mapIso, e.symm.op, isCardinalAccessible_of_natIso, mapIso
-/
lemma isCardinalPresentable_of_iso [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ :=
  Functor.isCardinalAccessible_of_natIso (coyoneda.mapIso e.symm.op) κ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isCardinalPresentable C κ).IsClosedUnderIsomorphisms
  body: by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact isCardinalPresentable_of_iso e _

中文:
实例 :
  签名: (isCardinalPresentable C κ).IsClosedUnderIsomorphisms
  定义体: by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact isCardinalPresentable_of_iso e _

Depends on / 依赖: isCardinalPresentable_iff, isCardinalPresentable_of_iso
-/
instance : (isCardinalPresentable C κ).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact isCardinalPresentable_of_iso e _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isCardinalPresentable_of_equivalence` / 引理 `isCardinalPresentable_of_equivalence`

English:
lemma isCardinalPresentable_of_equivalence
  proof: by
  refine ⟨fun J _ _ => ⟨fun {Y} => ?_⟩⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
  suffices PreservesColimit Y (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) from
    ⟨fun {c} hc => ⟨isColimitOfReflects uliftFunctor.{v₁}
        (isColimitOfPreserves (coyoneda.

中文:
引理 isCardinalPresentable_of_equivalence
  证明: by
  refine ⟨fun J _ _ => ⟨fun {Y} => ?_⟩⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
  suffices PreservesColimit Y (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) from
    ⟨fun {c} hc => ⟨isColimitOfReflects uliftFunctor.{v₁}
        (isColimitOfPreserves (coyoneda.

Depends on / 依赖: Equiv.uli, NatIso, NatIso.ofComponents, PreservesColimit, coyoneda, coyoneda.obj, e.functor.obj, e.inverse, functor, inverse, isColimitOfPreserves, isColimitOfReflects, ofComponents, preservesColimitsOfShape_of_isCardinalPresentable, uliftFunctor
-/
lemma isCardinalPresentable_of_equivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (e : C ≌ C') :
    IsCardinalPresentable (e.functor.obj X) κ := by
  refine ⟨fun J _ _ => ⟨fun {Y} => ?_⟩⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
  suffices PreservesColimit Y (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) from
    ⟨fun {c} hc => ⟨isColimitOfReflects uliftFunctor.{v₁}
        (isColimitOfPreserves (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) hc)⟩⟩
  have iso : coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁} ≅
    e.inverse ⋙ coyoneda.obj (op X) ⋙ uliftFunctor.{v₃} :=
    NatIso.ofComponents (fun Z =>
      (Equiv.ulift.trans ((e.toAdjunction.homEquiv X Z).trans Equiv.ulift.symm)).toIso) (by
        intro _ _ f
        ext ⟨g⟩
        simp [Adjunction.homEquiv_unit])
  exact preservesColimit_of_natIso Y iso.symm

/--
Instance `isCardinalPresentable_of_isEquivalence` / 实例 `isCardinalPresentable_of_isEquivalence`

English:
instance isCardinalPresentable_of_isEquivalence
  body: isCardinalPresentable_of_equivalence X κ F.asEquivalence

@[simp]

中文:
实例 isCardinalPresentable_of_isEquivalence
  定义体: isCardinalPresentable_of_equivalence X κ F.asEquivalence

@[simp]

Depends on / 依赖: F.asEquivalence, asEquivalence, isCardinalPresentable_of_equivalence
-/
instance isCardinalPresentable_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ :=
  isCardinalPresentable_of_equivalence X κ F.asEquivalence

@[simp]
/--
lemma `isCardinalPresentable_iff_of_isEquivalence` / 引理 `isCardinalPresentable_iff_of_isEquivalence`

English:
lemma isCardinalPresentable_iff_of_isEquivalence
  proof: by
  constructor
  · intro
    exact isCardinalPresentable_of_iso
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X :) κ
  · intro
    infer_instance

中文:
引理 isCardinalPresentable_iff_of_isEquivalence
  证明: by
  constructor
  · intro
    exact isCardinalPresentable_of_iso
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X :) κ
  · intro
    infer_instance

Depends on / 依赖: F.asEquivalence.unitIso.symm.app, F.inv.obj, F.obj, asEquivalence, infer_instance, isCardinalPresentable_of_iso, unitIso
-/
lemma isCardinalPresentable_iff_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ ↔ IsCardinalPresentable X κ := by
  constructor
  · intro
    exact isCardinalPresentable_of_iso
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X :) κ
  · intro
    infer_instance

section

variable {J : Type*} [Category* J] {D : J ⥤ C}

/--
lemma `Limits.exists_hom_of_preservesColimit_coyoneda` / 引理 `Limits.exists_hom_of_preservesColimit_coyoneda`

English:
lemma Limits.exists_hom_of_preservesColimit_coyoneda
  statement: {c : Cocone D} (hc : IsColimit c) {X : C}
  proof: Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

中文:
引理 Limits.exists_hom_of_preservesColimit_coyoneda
  结论: {c : Cocone D} (hc : IsColimit c) {X : C}
  证明: Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

Depends on / 依赖: Types.jointly_surjective_of_isColimit, coyoneda, coyoneda.obj, isColimitOfPreserves, jointly_surjective_of_isColimit
-/
lemma Limits.exists_hom_of_preservesColimit_coyoneda {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))] (f : X ⟶ c.pt) :
    exists (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

/--
lemma `Limits.exists_eq_of_preservesColimit_coyoneda` / 引理 `Limits.exists_eq_of_preservesColimit_coyoneda`

English:
lemma Limits.exists_eq_of_preservesColimit_coyoneda
  statement: [IsFiltered J] {c : Cocone D}
  proof: (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

中文:
引理 Limits.exists_eq_of_preservesColimit_coyoneda
  结论: [IsFiltered J] {c : Cocone D}
  证明: (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimit_eq_iff, coyoneda, coyoneda.obj, isColimitOfPreserves, isColimit_eq_iff
-/
lemma Limits.exists_eq_of_preservesColimit_coyoneda [IsFiltered J] {c : Cocone D}
    (hc : IsColimit c) {X : C} [PreservesColimit D (coyoneda.obj (.op X))]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    exists (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

/--
lemma `Limits.exists_eq_of_preservesColimit_coyoneda_self` / 引理 `Limits.exists_eq_of_preservesColimit_coyoneda_self`

English:
lemma Limits.exists_eq_of_preservesColimit_coyoneda_self
  statement: [IsFiltered J] {c : Cocone D}
  proof: (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f g).mp h

中文:
引理 Limits.exists_eq_of_preservesColimit_coyoneda_self
  结论: [IsFiltered J] {c : Cocone D}
  证明: (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f g).mp h

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimit_eq_iff, coyoneda, coyoneda.obj, isColimitOfPreserves, isColimit_eq_iff
-/
lemma Limits.exists_eq_of_preservesColimit_coyoneda_self [IsFiltered J] {c : Cocone D}
    (hc : IsColimit c) {X : C} [PreservesColimit D (coyoneda.obj (.op X))]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    exists (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f g).mp h

/--
lemma `Limits.exists_hom_of_preservesColimit_yoneda` / 引理 `Limits.exists_hom_of_preservesColimit_yoneda`

English:
lemma Limits.exists_hom_of_preservesColimit_yoneda
  statement: {c : Cone D} (hc : IsLimit c) {X : C}
  proof: by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (yoneda.obj X) hc.op) f
  exact ⟨j.unop, p, hp⟩

中文:
引理 Limits.exists_hom_of_preservesColimit_yoneda
  结论: {c : Cone D} (hc : IsLimit c) {X : C}
  证明: by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (yoneda.obj X) hc.op) f
  exact ⟨j.unop, p, hp⟩

Depends on / 依赖: Types.jointly_surjective_of_isColimit, hc.op, isColimitOfPreserves, j.unop, jointly_surjective_of_isColimit, yoneda, yoneda.obj
-/
lemma Limits.exists_hom_of_preservesColimit_yoneda {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)] (f : c.pt ⟶ X) :
    exists (j : J) (p : D.obj j ⟶ X), c.π.app j ≫ p = f := by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (yoneda.obj X) hc.op) f
  exact ⟨j.unop, p, hp⟩

/--
lemma `Limits.exists_eq_of_preservesColimit_yoneda` / 引理 `Limits.exists_eq_of_preservesColimit_yoneda`

English:
lemma Limits.exists_eq_of_preservesColimit_yoneda
  statement: [IsCofiltered J] {c : Cone D} (hc : IsLimit c)
  proof: by
  obtain ⟨k, u, v, huv⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (yoneda.obj X) hc.op)).mp h
  exact ⟨k.unop, u.unop, v.unop, huv⟩

中文:
引理 Limits.exists_eq_of_preservesColimit_yoneda
  结论: [IsCofiltered J] {c : Cone D} (hc : IsLimit c)
  证明: by
  obtain ⟨k, u, v, huv⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (yoneda.obj X) hc.op)).mp h
  exact ⟨k.unop, u.unop, v.unop, huv⟩

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimit_eq_iff, hc.op, isColimitOfPreserves, isColimit_eq_iff, k.unop, u.unop, v.unop, yoneda, yoneda.obj
-/
lemma Limits.exists_eq_of_preservesColimit_yoneda [IsCofiltered J] {c : Cone D} (hc : IsLimit c)
    {X : C} [PreservesColimit D.op (yoneda.obj X)]
    {i j : J} (f : D.obj i ⟶ X) (g : D.obj j ⟶ X) (h : c.π.app i ≫ f = c.π.app j ≫ g) :
    exists (k : J) (u : k ⟶ i) (v : k ⟶ j), D.map u ≫ f = D.map v ≫ g := by
  obtain ⟨k, u, v, huv⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (yoneda.obj X) hc.op)).mp h
  exact ⟨k.unop, u.unop, v.unop, huv⟩

/--
lemma `Limits.exists_eq_of_preservesColimit_yoneda_self` / 引理 `Limits.exists_eq_of_preservesColimit_yoneda_self`

English:
lemma Limits.exists_eq_of_preservesColimit_yoneda_self
  statement: [IsCofiltered J] {c : Cone D}
  proof: by
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (yoneda.obj X) hc.op) f g).mp h
  exact ⟨j.unop, a.unop, ha⟩

中文:
引理 Limits.exists_eq_of_preservesColimit_yoneda_self
  结论: [IsCofiltered J] {c : Cone D}
  证明: by
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (yoneda.obj X) hc.op) f g).mp h
  exact ⟨j.unop, a.unop, ha⟩

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimit_eq_iff, a.unop, hc.op, isColimitOfPreserves, isColimit_eq_iff, j.unop, yoneda, yoneda.obj
-/
lemma Limits.exists_eq_of_preservesColimit_yoneda_self [IsCofiltered J] {c : Cone D}
    (hc : IsLimit c) {X : C} [PreservesColimit D.op (yoneda.obj X)]
    {i : J} (f g : D.obj i ⟶ X) (h : c.π.app i ≫ f = c.π.app i ≫ g) :
    exists (j : J) (a : j ⟶ i), D.map a ≫ f = D.map a ≫ g := by
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (yoneda.obj X) hc.op) f g).mp h
  exact ⟨j.unop, a.unop, ha⟩

variable {X} in
/--
lemma `IsCardinalPresentable.exists_hom_of_isColimit` / 引理 `IsCardinalPresentable.exists_hom_of_isColimit`

English:
lemma IsCardinalPresentable.exists_hom_of_isColimit
  statement: [IsCardinalPresentable X κ]
  proof: by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  exact exists_hom_of_preservesColimit_coyoneda hc f

中文:
引理 IsCardinalPresentable.exists_hom_of_isColimit
  结论: [IsCardinalPresentable X κ]
  证明: by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  exact exists_hom_of_preservesColimit_coyoneda hc f

Depends on / 依赖: exists_hom_of_preservesColimit_coyoneda, preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
-/
lemma IsCardinalPresentable.exists_hom_of_isColimit [IsCardinalPresentable X κ]
    [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (f : X ⟶ c.pt) :
    exists (j : J) (f' : X ⟶ F.obj j), f' ≫ c.ι.app j = f := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  exact exists_hom_of_preservesColimit_coyoneda hc f

variable {X} in
/--
lemma `IsCardinalPresentable.exists_eq_of_isColimit` / 引理 `IsCardinalPresentable.exists_eq_of_isColimit`

English:
lemma IsCardinalPresentable.exists_eq_of_isColimit
  statement: [IsCardinalPresentable X κ]
  proof: by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda hc f₁ f₂ hf

中文:
引理 IsCardinalPresentable.exists_eq_of_isColimit
  结论: [IsCardinalPresentable X κ]
  证明: by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda hc f₁ f₂ hf

Depends on / 依赖: exists_eq_of_preservesColimit_coyoneda, isFiltered_of_isCardinalFiltered, preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
-/
lemma IsCardinalPresentable.exists_eq_of_isColimit [IsCardinalPresentable X κ]
    [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {i₁ i₂ : J} (f₁ : X ⟶ F.obj i₁)
    (f₂ : X ⟶ F.obj i₂) (hf : f₁ ≫ c.ι.app i₁ = f₂ ≫ c.ι.app i₂) :
    exists (j : J) (u : i₁ ⟶ j) (v : i₂ ⟶ j), f₁ ≫ F.map u = f₂ ≫ F.map v := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda hc f₁ f₂ hf

variable {X} in
/--
lemma `IsCardinalPresentable.exists_eq_of_isColimit'` / 引理 `IsCardinalPresentable.exists_eq_of_isColimit'`

English:
lemma IsCardinalPresentable.exists_eq_of_isColimit'
  statement: [IsCardinalPresentable X κ]
  proof: by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda_self hc f₁ f₂ hf

中文:
引理 IsCardinalPresentable.exists_eq_of_isColimit'
  结论: [IsCardinalPresentable X κ]
  证明: by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda_self hc f₁ f₂ hf

Depends on / 依赖: exists_eq_of_preservesColimit_coyoneda_self, isFiltered_of_isCardinalFiltered, preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
-/
lemma IsCardinalPresentable.exists_eq_of_isColimit' [IsCardinalPresentable X κ]
    [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {i : J} (f₁ f₂ : X ⟶ F.obj i)
    (hf : f₁ ≫ c.ι.app i = f₂ ≫ c.ι.app i) :
    exists (j : J) (u : i ⟶ j), f₁ ≫ F.map u = f₂ ≫ F.map u := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact exists_eq_of_preservesColimit_coyoneda_self hc f₁ f₂ hf

end

/--
lemma `isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj` / 引理 `isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj`

English:
lemma isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj
  proof: by
  change _ ↔ (coyoneda.obj (op X) ⋙ uliftFunctor.{t}).IsCardinalAccessible κ
  refine ⟨fun _ => inferInstance, fun _ => ⟨fun J _ _ => ?_⟩⟩
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (coyoneda.obj (op X) ⋙ uliftFunctor.{t}) κ J
  exact preservesColimitsOfShape_of_reflec

中文:
引理 isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj
  证明: by
  change _ ↔ (coyoneda.obj (op X) ⋙ uliftFunctor.{t}).IsCardinalAccessible κ
  refine ⟨fun _ => inferInstance, fun _ => ⟨fun J _ _ => ?_⟩⟩
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (coyoneda.obj (op X) ⋙ uliftFunctor.{t}) κ J
  exact preservesColimitsOfShape_of_reflec

Depends on / 依赖: Functor, Functor.preservesColimitsOfShape_of_isCardinalAccessible, IsCardinalAccessible, coyoneda, coyoneda.obj, preservesColimitsOfShape_of_isCardinalAccessible, preservesColimitsOfShape_of_reflects_of_preserves, uliftFunctor
-/
lemma isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj :
    IsCardinalPresentable X κ ↔ (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ := by
  change _ ↔ (coyoneda.obj (op X) ⋙ uliftFunctor.{t}).IsCardinalAccessible κ
  refine ⟨fun _ => inferInstance, fun _ => ⟨fun J _ _ => ?_⟩⟩
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (coyoneda.obj (op X) ⋙ uliftFunctor.{t}) κ J
  exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{t, v₁}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCardinalPresentable
  signature: X κ] :
  body: (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{t} X κ).1 inferInstance

中文:
实例 [IsCardinalPresentable
  签名: X κ] :
  定义体: (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{t} X κ).1 inferInstance

Depends on / 依赖: isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj
-/
instance [IsCardinalPresentable X κ] :
    (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ :=
  (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{t} X κ).1 inferInstance

end

section

variable (X : C)

/-- An object of a category is presentable relative to a universe `w`
if it is `κ`-presentable for some regular `κ : Cardinal.{w}`. -/
@[pp_with_univ]
/--
Definition of `IsPresentable` / `IsPresentable` 的定义

English:
abbreviation IsPresentable
  signature: (X : C)
  body: Functor.IsAccessible.{w} (coyoneda.obj (op X))

中文:
缩写 IsPresentable
  签名: (X : C)
  定义体: Functor.IsAccessible.{w} (coyoneda.obj (op X))

Depends on / 依赖: Functor, Functor.IsAccessible, IsAccessible, coyoneda, coyoneda.obj
-/
abbrev IsPresentable (X : C) : Prop :=
  Functor.IsAccessible.{w} (coyoneda.obj (op X))

/--
lemma `isPresentable_of_isCardinalPresentable` / 引理 `isPresentable_of_isCardinalPresentable`

English:
lemma isPresentable_of_isCardinalPresentable
  statement: (κ : Cardinal.{w}) [Fact κ.IsRegular]
  proof: ⟨κ, inferInstance, inferInstance⟩

中文:
引理 isPresentable_of_isCardinalPresentable
  结论: (κ : Cardinal.{w}) [Fact κ.IsRegular]
  证明: ⟨κ, inferInstance, inferInstance⟩
-/
lemma isPresentable_of_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] : IsPresentable.{w} X where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

end

section

/--
Definition of `HasCardinalFilteredColimits` / `HasCardinalFilteredColimits` 的定义

English:
class HasCardinalFilteredColimits
  parameters: (C : Type u₁) [Category.{v₁} C]
  axioms and operations (1):
    - hasColimitsOfShape((C) (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ]) : HasColimitsOfShape J C  [default: by intros; infer_instance]

中文:
类 HasCardinalFilteredColimits
  参数: (C : 类型u₁) [Category.{v₁} C]
  公理与运算 (1 个):
    - hasColimitsOfShape((C) (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ]) : HasColimitsOfShape J C  [默认: by intros; infer_instance]

Depends on / 依赖: infer_instance, intros
-/
class HasCardinalFilteredColimits (C : Type u₁) [Category.{v₁} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  hasColimitsOfShape (C) (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    HasColimitsOfShape J C := by intros; infer_instance

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasColimitsOfSize.{w, w} C] :
    HasCardinalFilteredColimits.{w} C κ where

end

end CategoryTheory
