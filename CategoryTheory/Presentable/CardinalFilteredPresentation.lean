/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Presentable.Retracts
public import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Presentable generators

Let `C` be a category, a regular cardinal `κ` and `P : ObjectProperty C`.
We define a predicate `P.IsCardinalFilteredGenerator κ` saying that
`P` consists of `κ`-presentable objects and that any object in `C`
is a `κ`-filtered colimit of objects satisfying `P`.
We show that if this condition is satisfied, then `P` is a strong generator
(see `IsCardinalFilteredGenerator.isStrongGenerator`). Moreover,
if `C` is locally small, we show that any object in `C` is presentable
(see `IsCardinalFilteredGenerator.presentable`).

Finally, we define a typeclass `HasCardinalFilteredGenerator C κ` saying
that `C` is locally `w`-small and that there exists an (essentially) small `P`
such that `P.IsCardinalFilteredGenerator κ` holds.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits.ColimitPresentation

/--
lemma `isCardinalPresentable` / 引理 `isCardinalPresentable`

English:
lemma isCardinalPresentable
  statement: {X : C} {J : Type w} [SmallCategory J]
  proof: have (k : J) : IsCardinalPresentable (p.diag.obj k) κ' := isCardinalPresentable_of_le _ h
  isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

中文:
引理 isCardinalPresentable
  结论: {X : C} {J : 类型 w} [小范畴 J]
  证明: have (k : J) : IsCardinalPresentable (p.diag.obj k) κ' := isCardinalPresentable_of_le _ h
  isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

Depends on / 依赖: IsCardinalPresentable, isCardinalPresentable_of_isColimit, isCardinalPresentable_of_le, isColimit, p.diag.obj, p.isColimit
-/
lemma isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : ColimitPresentation J X) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : forall (j : J), IsCardinalPresentable (p.diag.obj j) κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ <= κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  have (k : J) : IsCardinalPresentable (p.diag.obj k) κ' := isCardinalPresentable_of_le _ h
  isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end Limits.ColimitPresentation

open Limits

namespace ObjectProperty

variable {P : ObjectProperty C}

/--
lemma `ColimitOfShape.isCardinalPresentable` / 引理 `ColimitOfShape.isCardinalPresentable`

English:
lemma ColimitOfShape.isCardinalPresentable
  statement: {X : C} {J : Type w} [SmallCategory J]
  proof: p.toColimitPresentation.isCardinalPresentable κ
    (fun j => hP _ (p.prop_diag_obj j)) _ h hJ

中文:
引理 余limitOfShape.isCardinalPresentable
  结论: {X : C} {J : 类型 w} [小范畴 J]
  证明: p.toColimitPresentation.isCardinalPresentable κ
    (fun j => hP _ (p.prop_diag_obj j)) _ h hJ

Depends on / 依赖: isCardinalPresentable, p.prop_diag_obj, p.toColimitPresentation.isCardinalPresentable, prop_diag_obj, toColimitPresentation
-/
lemma ColimitOfShape.isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : P.ColimitOfShape J X) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : P <= isCardinalPresentable C κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ <= κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  p.toColimitPresentation.isCardinalPresentable κ
    (fun j => hP _ (p.prop_diag_obj j)) _ h hJ

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (P κ) in
/--
Definition of `IsCardinalFilteredGenerator` / `IsCardinalFilteredGenerator` 的定义

English:
structure IsCardinalFilteredGenerator
  parameters: : Prop where
  axioms and operations (2):
    - le_isCardinalPresentable : P <= isCardinalPresentable C κ
    - exists_colimitsOfShape((X : C)) : exists (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ), P.colimitsOfShape J X

中文:
结构 是CardinalFilteredGenerator
  参数: : 命题 where
  公理与运算 (2 个):
    - le_isCardinalPresentable : P <= isCardinalPresentable C κ
    - exists_colimitsOfShape((X : C)) : 存在 (J : 类型 w) (_ : 小范畴 J) (_ : 是CardinalFiltered J κ), P.colimitsOfShape J X
-/
structure IsCardinalFilteredGenerator : Prop where
  le_isCardinalPresentable : P <= isCardinalPresentable C κ
  exists_colimitsOfShape (X : C) :
    exists (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      P.colimitsOfShape J X

namespace IsCardinalFilteredGenerator

variable (h : P.IsCardinalFilteredGenerator κ) (X : C)

include h in
/--
lemma `of_le_isoClosure` / 引理 `of_le_isoClosure`

English:
lemma of_le_isoClosure
  statement: {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure)
  proof: h₂
  exists_colimitsOfShape X := by
    obtain ⟨J, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨J, inferInstance, inferInstance, by
      simpa only [colimitsOfShape_isoClosure] using colimitsOfShape_monotone J h₁ _ hX⟩

include h in

中文:
引理 of_le_isoClosure
  结论: {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure)
  证明: h₂
  exists_colimitsOfShape X := by
    obtain ⟨J, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨J, inferInstance, inferInstance, by
      simpa only [colimitsOfShape_isoClosure] using colimitsOfShape_monotone J h₁ _ hX⟩

include h in
-/
lemma of_le_isoClosure {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure)
    (h₂ : P' <= isCardinalPresentable C κ) :
    P'.IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := h₂
  exists_colimitsOfShape X := by
    obtain ⟨J, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨J, inferInstance, inferInstance, by
      simpa only [colimitsOfShape_isoClosure] using colimitsOfShape_monotone J h₁ _ hX⟩

include h in
/--
lemma `isoClosure` / 引理 `isoClosure`

English:
lemma isoClosure
  statement: P.isoClosure.IsCardinalFilteredGenerator κ
  proof: h.of_le_isoClosure (P.le_isoClosure.trans P.isoClosure.le_isoClosure)
    (by simpa only [ObjectProperty.isoClosure_le_iff] using h.le_isCardinalPresentable)

中文:
引理 isoClosure
  结论: P.isoClosure.是CardinalFilteredGenerator κ
  证明: h.of_le_isoClosure (P.le_isoClosure.trans P.isoClosure.le_isoClosure)
    (by simpa only [ObjectProperty.isoClosure_le_iff] using h.le_isCardinalPresentable)

Depends on / 依赖: ObjectProperty, ObjectProperty.isoClosure_le_iff, P.isoClosure.le_isoClosure, P.le_isoClosure.trans, h.le_isCardinalPresentable, h.of_le_isoClosure, isoClosure, isoClosure_le_iff, le_isCardinalPresentable, le_isoClosure, of_le_isoClosure
-/
lemma isoClosure : P.isoClosure.IsCardinalFilteredGenerator κ :=
  h.of_le_isoClosure (P.le_isoClosure.trans P.isoClosure.le_isoClosure)
    (by simpa only [ObjectProperty.isoClosure_le_iff] using h.le_isCardinalPresentable)

/--
lemma `isoClosure_iff` / 引理 `isoClosure_iff`

English:
lemma isoClosure_iff
  proof: ⟨fun h => h.of_le_isoClosure (by rfl) (P.le_isoClosure.trans h.le_isCardinalPresentable),
    isoClosure⟩

include h in

中文:
引理 isoClosure_iff
  证明: ⟨fun h => h.of_le_isoClosure (by rfl) (P.le_isoClosure.trans h.le_isCardinalPresentable),
    isoClosure⟩

include h in

Depends on / 依赖: P.le_isoClosure.trans, h.le_isCardinalPresentable, h.of_le_isoClosure, isoClosure, le_isCardinalPresentable, le_isoClosure, of_le_isoClosure
-/
lemma isoClosure_iff :
    P.isoClosure.IsCardinalFilteredGenerator κ ↔ P.IsCardinalFilteredGenerator κ :=
  ⟨fun h => h.of_le_isoClosure (by rfl) (P.le_isoClosure.trans h.le_isCardinalPresentable),
    isoClosure⟩

include h in
/--
lemma `presentable` / 引理 `presentable`

English:
lemma presentable
  given: [LocallySmall.{w} C] (X : C)
  proof: by
  obtain ⟨J, _, _, ⟨hX⟩⟩ := h.exists_colimitsOfShape X
  obtain ⟨κ', _, le, hκ'⟩ : exists (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ <= κ'),
      HasCardinalLT (Arrow J) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) =

中文:
引理 presentable
  条件: [LocallySmall.{w} C] (X : C)
  证明: by
  obtain ⟨J, _, _, ⟨hX⟩⟩ := h.exists_colimitsOfShape X
  obtain ⟨κ', _, le, hκ'⟩ : exists (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ <= κ'),
      HasCardinalLT (Arrow J) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) =

Depends on / 依赖: Cardinal, HasCardinalLT, HasCardinalLT.exists_regular_cardinal_forall, IsRegular, Sum.elim, Sum.inl, Sum.inr, ToType, exists_colimitsOfShape, exists_regular_cardinal_forall, h.exists_colimitsOfShape, h.le_isCardinalPresentable, hX.isCardinalPresentable, hasCardinalLT_iff_cardinal_mk_lt, isCardinalPresentable, le_isCardinalPresentable, le_of_lt, ord.ToType
-/
lemma presentable [LocallySmall.{w} C] (X : C) :
    IsPresentable.{w} X := by
  obtain ⟨J, _, _, ⟨hX⟩⟩ := h.exists_colimitsOfShape X
  obtain ⟨κ', _, le, hκ'⟩ : exists (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ <= κ'),
      HasCardinalLT (Arrow J) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) => Arrow J) (fun (_ : Unit) => κ.ord.ToType))
    exact ⟨κ', ⟨h₁⟩,
      le_of_lt (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h₂ (Sum.inr ⟨⟩)),
      h₂ (Sum.inl ⟨⟩)⟩
  have := hX.isCardinalPresentable h.le_isCardinalPresentable _ le hκ'
  exact isPresentable_of_isCardinalPresentable _ κ'

include h in
/--
lemma `isStrongGenerator` / 引理 `isStrongGenerator`

English:
lemma isStrongGenerator
  statement: P.IsStrongGenerator
  proof: IsStrongGenerator.mk_of_exists_colimitsOfShape.{w} (fun X => by
    obtain ⟨_, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨_, _, hX⟩)

include h in

中文:
引理 isStrongGenerator
  结论: P.IsStrongGenerator
  证明: IsStrongGenerator.mk_of_exists_colimitsOfShape.{w} (fun X => by
    obtain ⟨_, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨_, _, hX⟩)

include h in

Depends on / 依赖: IsStrongGenerator, IsStrongGenerator.mk_of_exists_colimitsOfShape, exists_colimitsOfShape, h.exists_colimitsOfShape, mk_of_exists_colimitsOfShape
-/
lemma isStrongGenerator : P.IsStrongGenerator :=
  IsStrongGenerator.mk_of_exists_colimitsOfShape.{w} (fun X => by
    obtain ⟨_, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨_, _, hX⟩)

include h in
/--
lemma `isPresentable_eq_retractClosure` / 引理 `isPresentable_eq_retractClosure`

English:
lemma isPresentable_eq_retractClosure
  proof: by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [isCardinalPresentable_iff] at hX
    obtain ⟨J, _, _, ⟨p⟩⟩ := h.exists_colimitsOfShape X
    have := essentiallySmall_of_small_of_locallySmall.{w} J
    obtain ⟨j, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit (𝟙 X)
    exac

中文:
引理 isPresentable_eq_retractClosure
  证明: by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [isCardinalPresentable_iff] at hX
    obtain ⟨J, _, _, ⟨p⟩⟩ := h.exists_colimitsOfShape X
    have := essentiallySmall_of_small_of_locallySmall.{w} J
    obtain ⟨j, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit (𝟙 X)
    exac

Depends on / 依赖: IsCardinalPresentable, IsCardinalPresentable.exists_hom_of_isColimit, ObjectProperty, ObjectProperty.retractClosure_le_iff, essentiallySmall_of_small_of_locallySmall, exists_colimitsOfShape, exists_hom_of_isColimit, h.exists_colimitsOfShape, h.le_isCardinalPresentable, isCardinalPresentable_iff, isColimit, le_antisymm, le_isCardinalPresentable, p.isColimit, p.prop_diag_obj, prop_diag_obj, retract, retractClosure_le_iff
-/
lemma isPresentable_eq_retractClosure :
    isCardinalPresentable C κ = P.retractClosure := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [isCardinalPresentable_iff] at hX
    obtain ⟨J, _, _, ⟨p⟩⟩ := h.exists_colimitsOfShape X
    have := essentiallySmall_of_small_of_locallySmall.{w} J
    obtain ⟨j, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit (𝟙 X)
    exact ⟨_, p.prop_diag_obj j, ⟨{ i := _, r := _, retract := hf}⟩⟩
  · simpa only [ObjectProperty.retractClosure_le_iff] using h.le_isCardinalPresentable

include h in
/--
lemma `essentiallySmall_isPresentable` / 引理 `essentiallySmall_isPresentable`

English:
lemma essentiallySmall_isPresentable
  proof: by
  rw [h.isPresentable_eq_retractClosure]
  infer_instance

中文:
引理 essentiallySmall_isPresentable
  证明: by
  rw [h.isPresentable_eq_retractClosure]
  infer_instance

Depends on / 依赖: h.isPresentable_eq_retractClosure, infer_instance, isPresentable_eq_retractClosure
-/
lemma essentiallySmall_isPresentable
    [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  rw [h.isPresentable_eq_retractClosure]
  infer_instance

end IsCardinalFilteredGenerator

end ObjectProperty

/--
Definition of `HasCardinalFilteredGenerator` / `HasCardinalFilteredGenerator` 的定义

English:
class HasCardinalFilteredGenerator
  parameters: (C : Type u) [hC : Category.{v} C]
  extends: LocallySmall.{w} C
  axioms and operations (1):
    - exists_generator((C κ) [hC] [hκ]) : exists (P : ObjectProperty C) (_ : ObjectProperty.EssentiallySmall.{w} P), P.IsCardinalFilteredGenerator κ

中文:
类 有CardinalFilteredGenerator
  参数: (C : 类型u) [hC : 范畴.{v} C]
  继承: LocallySmall.{w} C
  公理与运算 (1 个):
    - exists_generator((C κ) [hC] [hκ]) : 存在 (P : ObjectProperty C) (_ : ObjectProperty.EssentiallySmall.{w} P), P.是CardinalFilteredGenerator κ
-/
class HasCardinalFilteredGenerator (C : Type u) [hC : Category.{v} C]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] : Prop extends LocallySmall.{w} C where
  exists_generator (C κ) [hC] [hκ] :
    exists (P : ObjectProperty C) (_ : ObjectProperty.EssentiallySmall.{w} P),
      P.IsCardinalFilteredGenerator κ

/--
lemma `ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator` / 引理 `ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator`

English:
lemma ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator
  proof: ⟨P, inferInstance, hP⟩

中文:
引理 ObjectProperty.是CardinalFilteredGenerator.hasCardinalFilteredGenerator
  证明: ⟨P, inferInstance, hP⟩
-/
lemma ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator
    {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    [LocallySmall.{w} C] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    (hP : P.IsCardinalFilteredGenerator κ) :
    HasCardinalFilteredGenerator C κ where
  exists_generator := ⟨P, inferInstance, hP⟩

/--
lemma `HasCardinalFilteredGenerator.exists_small_generator` / 引理 `HasCardinalFilteredGenerator.exists_small_generator`

English:
lemma HasCardinalFilteredGenerator.exists_small_generator
  statement: (C : Type u) [Category.{v} C]
  proof: by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  exact ⟨Q, inferInstance, hP.of_le_isoClosure h₂ (h₁.trans hP.le_isCardinalPresentable)⟩

中文:
引理 有CardinalFilteredGenerator.存在_small_generator
  结论: (C : 类型u) [范畴.{v} C]
  证明: by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  exact ⟨Q, inferInstance, hP.of_le_isoClosure h₂ (h₁.trans hP.le_isCardinalPresentable)⟩

Depends on / 依赖: EssentiallySmall, HasCardinalFilteredGenerator, HasCardinalFilteredGenerator.exists_generator, ObjectProperty, ObjectProperty.EssentiallySmall.exists_small_le, exists_generator, exists_small_le, hP.le_isCardinalPresentable, hP.of_le_isoClosure, le_isCardinalPresentable, of_le_isoClosure
-/
lemma HasCardinalFilteredGenerator.exists_small_generator (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasCardinalFilteredGenerator C κ] :
    exists (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P),
      P.IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  exact ⟨Q, inferInstance, hP.of_le_isoClosure h₂ (h₁.trans hP.le_isCardinalPresentable)⟩

instance (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasCardinalFilteredGenerator C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  exact hP.essentiallySmall_isPresentable

end CategoryTheory
