/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## Main definitions

- `CategoryTheory.MorphismProperty.ind`: `f` satisfies `ind P` if `f` is a filtered colimit of
  morphisms in `P`.

## Main results:

- `CategoryTheory.MorphismProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `pro P`.
- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

@[expose] public section

universe w v u

namespace CategoryTheory.MorphismProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

/--
Definition of `ind` / `ind` 的定义

English:
definition ind
  signature: (P : MorphismProperty C)
  body: fun X Y f => exists (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ C) (t : (Functor.const J).obj X ⟶ D) (s : D ⟶ (Functor.const J).obj Y)
    (_ : IsColimit (Cocone.mk _ s)), forall j, P (t.app j) ∧ t.app j ≫ s.app j = f

中文:
定义 ind
  签名: (P : MorphismProperty C)
  定义体: fun X Y f => exists (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ C) (t : (Functor.const J).obj X ⟶ D) (s : D ⟶ (Functor.const J).obj Y)
    (_ : IsColimit (Cocone.mk _ s)), forall j, P (t.app j) ∧ t.app j ≫ s.app j = f

Depends on / 依赖: Cocone, Cocone.mk, Functor, Functor.const, IsColimit, IsFiltered, IsVerdierRightLocalizing, IsVerdierRightLocalizing.fac, Quiver, Quiver.Hom.unop_inj, SmallCategory, a.op, b.op, f.unop, s.app, t.app, unop_inj
-/
def ind (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f => exists (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ C) (t : (Functor.const J).obj X ⟶ D) (s : D ⟶ (Functor.const J).obj Y)
    (_ : IsColimit (Cocone.mk _ s)), forall j, P (t.app j) ∧ t.app j ≫ s.app j = f

/--
lemma `exists_hom_of_isFinitelyPresentable` / 引理 `exists_hom_of_isFinitelyPresentable`

English:
lemma exists_hom_of_isFinitelyPresentable
  statement: {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
  proof: hp.exists_hom_of_isColimit_under hc _ s _ h

中文:
引理 存在_hom_of_isFinitelyPresentable
  结论: {J : 类型 w} [小范畴 J] [是Filtered J] {D : J ⥤ C}
  证明: hp.exists_hom_of_isColimit_under hc _ s _ h

Depends on / 依赖: IsVerdierRightLocalizing, IsVerdierRightLocalizing.fac, Quiver, Quiver.Hom.op_inj, a.unop, b.unop, exists_hom_of_isColimit_under, f.op, hp.exists_hom_of_isColimit_under, op_inj
-/
lemma exists_hom_of_isFinitelyPresentable {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    {c : Cocone D} (hc : IsColimit c) {X A : C} {p : X ⟶ A} (hp : isFinitelyPresentable.{w} C p)
    (s : (Functor.const J).obj X ⟶ D) (f : A ⟶ c.pt) (h : forall (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    exists (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f :=
  hp.exists_hom_of_isColimit_under hc _ s _ h

set_option backward.defeqAttrib.useBackward true in
/--
lemma `le_ind` / 引理 `le_ind`

English:
lemma le_ind
  statement: P <= ind.{w} P
  proof: by
  intro X Y f hf
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const PUnit).obj Y, ?_, 𝟙 _, ?_, ?_⟩
  · exact { app _ := f }
  · exact isColimitConstCocone _ _
  · simpa

中文:
引理 le_ind
  结论: P <= ind.{w} P
  证明: by
  intro X Y f hf
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const PUnit).obj Y, ?_, 𝟙 _, ?_, ?_⟩
  · exact { app _ := f }
  · exact isColimitConstCocone _ _
  · simpa

Depends on / 依赖: Functor, Functor.const, isColimitConstCocone
-/
lemma le_ind : P <= ind.{w} P := by
  intro X Y f hf
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const PUnit).obj Y, ?_, 𝟙 _, ?_, ?_⟩
  · exact { app _ := f }
  · exact isColimitConstCocone _ _
  · simpa

variable {P}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ind_iff_ind_underMk` / 引理 `ind_iff_ind_underMk`

English:
lemma ind_iff_ind_underMk
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ => ?_, fun ⟨J, _, _, pres, hpres⟩ => ?_⟩
  · refine ⟨J, ‹_›, ‹_›, ⟨Under.lift D t, ?_, ?_⟩, ?_⟩
    · exact { app j := CategoryTheory.Under.homMk (s.app j) (by simp [hst]) }
    · have : Nonempty J := IsFiltered.nonempty
      exact Under.isColimitLiftCoc

中文:
引理 ind_iff_ind_underMk
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ => ?_, fun ⟨J, _, _, pres, hpres⟩ => ?_⟩
  · refine ⟨J, ‹_›, ‹_›, ⟨Under.lift D t, ?_, ?_⟩, ?_⟩
    · exact { app j := CategoryTheory.Under.homMk (s.app j) (by simp [hst]) }
    · have : Nonempty J := IsFiltered.nonempty
      exact Under.isColimitLiftCoc

Depends on / 依赖: CategoryTheory, CategoryTheory.Under.forget, CategoryTheory.Under.homMk, Functor, Functor.whiskerR, IsFiltered, IsFiltered.nonempty, Nonempty, Under.isColimitLiftCocone, Under.lift, forget, isColimitLiftCocone, nonempty, pres.diag, pres.diag.obj, s.app, underObj, whiskerR
-/
lemma ind_iff_ind_underMk {X Y : C} (f : X ⟶ Y) :
    ind.{w} P f ↔ ObjectProperty.ind.{w} P.underObj (CategoryTheory.Under.mk f) := by
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ => ?_, fun ⟨J, _, _, pres, hpres⟩ => ?_⟩
  · refine ⟨J, ‹_›, ‹_›, ⟨Under.lift D t, ?_, ?_⟩, ?_⟩
    · exact { app j := CategoryTheory.Under.homMk (s.app j) (by simp [hst]) }
    · have : Nonempty J := IsFiltered.nonempty
      exact Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs
    · simp [underObj, hst]
  · refine ⟨J, ‹_›, ‹_›, pres.diag ⋙ CategoryTheory.Under.forget _, ?_, ?_, ?_, fun j => ⟨?_, ?_⟩⟩
    · exact { app j := (pres.diag.obj j).hom }
    · exact Functor.whiskerRight pres.ι (CategoryTheory.Under.forget X)
    · exact isColimitOfPreserves (CategoryTheory.Under.forget _) pres.isColimit
    · exact hpres j
    · simp

/--
lemma `underObj_ind_eq_ind_underObj` / 引理 `underObj_ind_eq_ind_underObj`

English:
lemma underObj_ind_eq_ind_underObj
  given: (X : C)
  proof: by
  ext f
  simp [underObj, show f = CategoryTheory.Under.mk f.hom from rfl, ind_iff_ind_underMk]

中文:
引理 underObj_ind_eq_ind_underObj
  条件: (X : C)
  证明: by
  ext f
  simp [underObj, show f = CategoryTheory.Under.mk f.hom from rfl, ind_iff_ind_underMk]

Depends on / 依赖: CategoryTheory, CategoryTheory.Under.mk, ObjectProperty, ObjectProperty.ind, P.underObj, f.hom, ind_iff_ind_underMk, underObj
-/
lemma underObj_ind_eq_ind_underObj (X : C) :
    underObj (ind.{w} P) (X := X) = ObjectProperty.ind.{w} P.underObj := by
  ext f
  simp [underObj, show f = CategoryTheory.Under.mk f.hom from rfl, ind_iff_ind_underMk]

variable (Q : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.RespectsLeft
  signature: Q] : P.ind.RespectsLeft Q where
  body: fun ⟨J, _, _, D, t, s, hs, hst⟩ => by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j => ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

中文:
实例 [P.RespectsLeft
  签名: Q] : P.ind.RespectsLeft Q where
  定义体: fun ⟨J, _, _, D, t, s, hs, hst⟩ => by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j => ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

Depends on / 依赖: Functor, Functor.const, RespectsLeft, RespectsLeft.precomp, precomp
-/
instance [P.RespectsLeft Q] : P.ind.RespectsLeft Q where
  precomp {X Y Z} i hi f := fun ⟨J, _, _, D, t, s, hs, hst⟩ => by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j => ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.RespectsIso]
  signature: : P.ind.RespectsIso where
  body: fun ⟨J, _, _, D, t, s, hs, hst⟩ => by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j => ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocone.ext (asIso i))) hs
    · simp [reassoc_of% (hst j).2]

中文:
实例 [P.RespectsIso]
  签名: : P.ind.RespectsIso where
  定义体: fun ⟨J, _, _, D, t, s, hs, hst⟩ => by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j => ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocone.ext (asIso i))) hs
    · simp [reassoc_of% (hst j).2]

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.const, IsColimit, IsColimit.equivIsoColimit, equivIsoColimit, reassoc_of
-/
instance [P.RespectsIso] : P.ind.RespectsIso where
  postcomp {X Y Z} i (hi : IsIso i) f := fun ⟨J, _, _, D, t, s, hs, hst⟩ => by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j => ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocone.ext (asIso i))) hs
    · simp [reassoc_of% (hst j).2]

/--
lemma `ind_underObj_pushout` / 引理 `ind_underObj_pushout`

English:
lemma ind_underObj_pushout
  statement: {X Y : C} (g : X ⟶ Y) [HasPushouts C] [P.IsStableUnderCobaseChange]
  proof: by
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  use J, inferInstance, inferInstance, pres.map (Under.pushout g)
  intro i
  exact P.pushout_inr _ _ (hpres i)

中文:
引理 ind_underObj_pushout
  结论: {X Y : C} (g : X ⟶ Y) [有Pushouts C] [P.是StableUnderCobaseChange]
  证明: by
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  use J, inferInstance, inferInstance, pres.map (Under.pushout g)
  intro i
  exact P.pushout_inr _ _ (hpres i)

Depends on / 依赖: P.pushout_inr, Under.pushout, pres.map, pushout, pushout_inr
-/
lemma ind_underObj_pushout {X Y : C} (g : X ⟶ Y) [HasPushouts C] [P.IsStableUnderCobaseChange]
    {f : Under X} (hf : ObjectProperty.ind.{w} P.underObj f) :
    ObjectProperty.ind.{w} P.underObj ((Under.pushout g).obj f) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  use J, inferInstance, inferInstance, pres.map (Under.pushout g)
  intro i
  exact P.pushout_inr _ _ (hpres i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderCobaseChange]
  signature: [HasPushouts C]
  body: by
  refine .mk' fun A B A' f g _ hf => ?_
  rw [ind_iff_ind_underMk] at hf ⊢
  exact ind_underObj_pushout g hf

中文:
实例 [P.是StableUnderCobaseChange]
  签名: [有Pushouts C]
  定义体: by
  refine .mk' fun A B A' f g _ hf => ?_
  rw [ind_iff_ind_underMk] at hf ⊢
  exact ind_underObj_pushout g hf

Depends on / 依赖: ind_iff_ind_underMk, ind_underObj_pushout
-/
instance [P.IsStableUnderCobaseChange] [HasPushouts C] : P.ind.IsStableUnderCobaseChange := by
  refine .mk' fun A B A' f g _ hf => ?_
  rw [ind_iff_ind_underMk] at hf ⊢
  exact ind_underObj_pushout g hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: : (ind.{w} P).ContainsIdentities where
  body: le_ind _ _ (P.id_mem X)

中文:
实例 [P.余ntainsIdentities]
  签名: : (ind.{w} P).余ntainsIdentities where
  定义体: le_ind _ _ (P.id_mem X)

Depends on / 依赖: P.id_mem, id_mem, le_ind
-/
instance [P.ContainsIdentities] : (ind.{w} P).ContainsIdentities where
  id_mem X := le_ind _ _ (P.id_mem X)

/--
lemma `ind_ind` / 引理 `ind_ind`

English:
lemma ind_ind
  given: (hp : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C]
  proof: by
  refine le_antisymm (fun X Y f hf => ?_) P.ind.le_ind
  have : P.underObj <= ObjectProperty.isFinitelyPresentable.{w} (Under X) := fun f hf => hp _ hf
  simpa [ind_iff_ind_underMk, underObj_ind_eq_ind_underObj,
    ObjectProperty.ind_ind.{w} this] using hf

中文:
引理 ind_ind
  条件: (hp : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C]
  证明: by
  refine le_antisymm (fun X Y f hf => ?_) P.ind.le_ind
  have : P.underObj <= ObjectProperty.isFinitelyPresentable.{w} (Under X) := fun f hf => hp _ hf
  simpa [ind_iff_ind_underMk, underObj_ind_eq_ind_underObj,
    ObjectProperty.ind_ind.{w} this] using hf

Depends on / 依赖: ObjectProperty, ObjectProperty.ind_ind, ObjectProperty.isFinitelyPresentable, P.ind.le_ind, P.underObj, ind_iff_ind_underMk, ind_ind, isFinitelyPresentable, le_antisymm, le_ind, underObj, underObj_ind_eq_ind_underObj
-/
lemma ind_ind (hp : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X Y f hf => ?_) P.ind.le_ind
  have : P.underObj <= ObjectProperty.isFinitelyPresentable.{w} (Under X) := fun f hf => hp _ hf
  simpa [ind_iff_ind_underMk, underObj_ind_eq_ind_underObj,
    ObjectProperty.ind_ind.{w} this] using hf

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ind_iff_exists` / 引理 `ind_iff_exists`

English:
lemma ind_iff_exists
  statement: (H : P <= isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [ind_iff_ind_underMk]; rw [ObjectProperty.ind_iff_exists]
  · refine ⟨fun H Z p g hp hpg => ?_, fun H Z g hZ => ?_⟩
    · have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
      obtain ⟨W, u, v, huv, hW⟩ := H (CategoryTheory.Under.homMk (U := CategoryTheory.Under.mk p)
        (

中文:
引理 ind_iff_存在
  结论: (H : P <= isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [ind_iff_ind_underMk]; rw [ObjectProperty.ind_iff_exists]
  · refine ⟨fun H Z p g hp hpg => ?_, fun H Z g hZ => ?_⟩
    · have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
      obtain ⟨W, u, v, huv, hW⟩ := H (CategoryTheory.Under.homMk (U := CategoryTheory.Under.mk p)
        (

Depends on / 依赖: CategoryTheory, CategoryTheory.Under, CategoryTheory.Under.homMk, CategoryTheory.Under.mk, CategoryTheory.Under.w, IsFinitelyPresentable, ObjectProperty, ObjectProperty.ind_iff_exists, W.hom, W.right, Z.hom, g.right, ind_iff_exists, ind_iff_ind_underMk, u.right, v.right
-/
lemma ind_iff_exists (H : P <= isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y)
    [IsFinitelyAccessibleCategory.{w} (Under X)] :
    ind.{w} P f ↔ forall {Z : C} (p : X ⟶ Z) (g : Z ⟶ Y),
      isFinitelyPresentable.{w} _ p -> p ≫ g = f ->
      exists (W : C) (u : Z ⟶ W) (v : W ⟶ Y), u ≫ v = g ∧ P (p ≫ u) := by
  rw [ind_iff_ind_underMk]; rw [ObjectProperty.ind_iff_exists]
  · refine ⟨fun H Z p g hp hpg => ?_, fun H Z g hZ => ?_⟩
    · have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
      obtain ⟨W, u, v, huv, hW⟩ := H (CategoryTheory.Under.homMk (U := CategoryTheory.Under.mk p)
        (V := CategoryTheory.Under.mk f) g hpg)
      use W.right, u.right, v.right, congr($(huv).right)
      rwa [show p ≫ u.right = W.hom from CategoryTheory.Under.w u]
    · obtain ⟨W, u, v, huv, hW⟩ := H Z.hom g.right hZ (CategoryTheory.Under.w g)
      exact ⟨CategoryTheory.Under.mk (Z.hom ≫ u), CategoryTheory.Under.homMk u,
          CategoryTheory.Under.homMk v, by ext; simpa, hW⟩
  · intro Y hY
    exact H _ hY

/--
Definition of `PreIndSpreads` / `PreIndSpreads` 的定义

English:
class PreIndSpreads
  parameters: (P : MorphismProperty C)
  axioms and operations (1):
    - exists_isPushout({J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (_ : IsColimit c) {T : C} (f : c.pt ⟶ T)) : P f -> exists (j : J) (T' : C) (f' : D.obj j ⟶ T') (g : T' ⟶ T), IsPushout (c.ι.app j) f' f g ∧ P f'

中文:
类 PreIndSpreads
  参数: (P : MorphismProperty C)
  公理与运算 (1 个):
    - exists_isPushout({J : 类型 w} [小范畴 J] [是Filtered J] {D : J ⥤ C} {c : 余锥 D} (_ : 是余极限 c) {T : C} (f : c.pt ⟶ T)) : P f -> 存在 (j : J) (T' : C) (f' : D.obj j ⟶ T') (g : T' ⟶ T), 是推出 (c.ι.app j) f' f g ∧ P f'

Depends on / 依赖: PreIndSpreads, PreIndSpreads.exists_isPushout, exists_isPushout
-/
class PreIndSpreads (P : MorphismProperty C) : Prop where
  exists_isPushout {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    {c : Cocone D} (_ : IsColimit c) {T : C} (f : c.pt ⟶ T) :
    P f ->
    exists (j : J) (T' : C) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ P f'

alias exists_isPushout_of_isFiltered := PreIndSpreads.exists_isPushout

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is stable under composition if `P` is. -/
@[stacks 0BSI "The stacks project lemma is for the special case of ind-étale ring homomorphisms."]
/--
lemma `IsStableUnderComposition.ind_of_preIndSpreads` / 引理 `IsStableUnderComposition.ind_of_preIndSpreads`

English:
lemma IsStableUnderComposition.ind_of_preIndSpreads
  proof: by
    rw [ind_iff_exists H]
    intro T p u hp hpu
    obtain ⟨J₁, _, _, D₁, s₁, t₁, ht₁, h₁⟩ := hf
    obtain ⟨J₂, _, _, D₂, s₂, t₂, ht₂, h₂⟩ := hg
    have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
    obtain ⟨j₂, q, hcomp, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_unde

中文:
引理 是StableUnderComposition.ind_of_preIndSpreads
  证明: by
    rw [ind_iff_exists H]
    intro T p u hp hpu
    obtain ⟨J₁, _, _, D₁, s₁, t₁, ht₁, h₁⟩ := hf
    obtain ⟨J₂, _, _, D₂, s₂, t₂, ht₂, h₂⟩ := hg
    have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
    obtain ⟨j₂, q, hcomp, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_unde

Depends on / 依赖: Categor, CategoryTheory, CategoryTheory.Under.mk, Functor, Functor.const, IsFinitelyPresentable, IsFinitelyPresentable.exists_hom_of_isColimit_under, P.exists_isPushout_of_isFiltered, Under.post, Under.pushout, exists_hom_of_isColimit_under, exists_isPushout_of_isFiltered, ind_iff_exists, pushout
-/
lemma IsStableUnderComposition.ind_of_preIndSpreads
    [forall X : C, (IsFinitelyAccessibleCategory.{w} (Under X))] [HasPushouts C]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] (H : P <= isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    rw [ind_iff_exists H]
    intro T p u hp hpu
    obtain ⟨J₁, _, _, D₁, s₁, t₁, ht₁, h₁⟩ := hf
    obtain ⟨J₂, _, _, D₂, s₂, t₂, ht₂, h₂⟩ := hg
    have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
    obtain ⟨j₂, q, hcomp, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
ht₂ p ((Functor.const _).map f ≫ s₂) u by simp [h₂, hpu]
    obtain ⟨j₁, W, f', g', h, hf'⟩ :=
      P.exists_isPushout_of_isFiltered ht₁ (s₂.app j₂) (h₂ j₂).left
    let D' : Under j₁ ⥤ C :=
      (Under.post D₁ ⋙ Under.pushout f') ⋙ CategoryTheory.Under.forget _
    let c' : Cocone D' :=
      (Under.pushout f' ⋙ CategoryTheory.Under.forget _).mapCocone
.extend h.isoPushout.inv ((Cocone.mk _ t₁).underPost j₁)
    let hc' : IsColimit c' :=
IsColimit.extendIso _ isColimitOfPreserves _ (ht₁.underPost j₁)
    let s' : (Functor.const (Under j₁)).obj X ⟶ D' :=
      { app k := s₁.app k.right ≫ pushout.inl _ _
        naturality k l a := by
          have h2 := s₁.naturality a.right
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
          simp [h2, D'] }
    obtain ⟨j₃, v, hcomp', hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
hc' p s' q fun k => by
      simp [c', s', hcomp, reassoc_of% (h₁ k.right).right]
    refine ⟨D'.obj j₃, v, c'.ι.app j₃ ≫ t₂.app j₂, ?_, ?_⟩
    · rwa [reassoc_of% hq]
    · rw [hcomp']
      exact P.comp_mem _ _ (h₁ _).left (P.pushout_inl _ _ hf')

/--
lemma `IsMultiplicative.ind_of_preIndSpreads` / 引理 `IsMultiplicative.ind_of_preIndSpreads`

English:
lemma IsMultiplicative.ind_of_preIndSpreads
  proof: IsStableUnderComposition.ind_of_preIndSpreads H

中文:
引理 是Multiplicative.ind_of_preIndSpreads
  证明: IsStableUnderComposition.ind_of_preIndSpreads H

Depends on / 依赖: IsStableUnderComposition, IsStableUnderComposition.ind_of_preIndSpreads, ind_of_preIndSpreads
-/
lemma IsMultiplicative.ind_of_preIndSpreads
    [forall X : C, (IsFinitelyAccessibleCategory.{w} (Under X))] [HasPushouts C]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] (H : P <= isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsMultiplicative where
  __ := IsStableUnderComposition.ind_of_preIndSpreads H

end CategoryTheory.MorphismProperty
