/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Relation of morphism properties with limits

The following predicates are introduces for morphism properties `P`:
* `IsStableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `IsStableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

We define `P.universally` for the class of morphisms which satisfy `P` after any base change.

We also introduce properties `IsStableUnderProductsOfShape`, `IsStableUnderLimitsOfShape`,
`IsStableUnderFiniteProducts`, and similar properties for colimits and coproducts.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : MorphismProperty C)

/--
Definition of `pullbacks` / `pullbacks` 的定义

English:
definition pullbacks
  signature: : MorphismProperty C
  body: fun A B q =>
  exists (X Y : C) (p : X ⟶ Y) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPullback f q p g

中文:
定义 pullbacks
  签名: : MorphismProperty C
  定义体: fun A B q =>
  exists (X Y : C) (p : X ⟶ Y) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPullback f q p g
-/
def pullbacks : MorphismProperty C := fun A B q =>
  exists (X Y : C) (p : X ⟶ Y) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPullback f q p g

/--
lemma `pullbacks_mk` / 引理 `pullbacks_mk`

English:
lemma pullbacks_mk
  statement: {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  proof: ⟨_, _, _, _, _, hp, sq⟩

中文:
引理 pullbacks_mk
  结论: {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  证明: ⟨_, _, _, _, _, hp, sq⟩
-/
lemma pullbacks_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPullback f q p g) (hp : P p) :
    P.pullbacks q :=
  ⟨_, _, _, _, _, hp, sq⟩

/--
lemma `le_pullbacks` / 引理 `le_pullbacks`

English:
lemma le_pullbacks
  statement: P <= P.pullbacks
  proof: by
  intro A B q hq
  exact P.pullbacks_mk IsPullback.of_id_fst hq

中文:
引理 le_pullbacks
  结论: P <= P.pullbacks
  证明: by
  intro A B q hq
  exact P.pullbacks_mk IsPullback.of_id_fst hq

Depends on / 依赖: IsPullback, IsPullback.of_id_fst, P.pullbacks_mk, of_id_fst, pullbacks_mk
-/
lemma le_pullbacks : P <= P.pullbacks := by
  intro A B q hq
  exact P.pullbacks_mk IsPullback.of_id_fst hq

/--
lemma `pullbacks_monotone` / 引理 `pullbacks_monotone`

English:
lemma pullbacks_monotone
  statement: Monotone (pullbacks (C := C))
  proof: by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

中文:
引理 pullbacks_monotone
  结论: 递增 (pullbacks (C := C))
  证明: by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩
-/
lemma pullbacks_monotone : Monotone (pullbacks (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

/--
Definition of `pushouts` / `pushouts` 的定义

English:
definition pushouts
  signature: : MorphismProperty C
  body: fun X Y q =>
  exists (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g

中文:
定义 pushouts
  签名: : MorphismProperty C
  定义体: fun X Y q =>
  exists (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g
-/
def pushouts : MorphismProperty C := fun X Y q =>
  exists (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g

/--
lemma `pushouts_mk` / 引理 `pushouts_mk`

English:
lemma pushouts_mk
  statement: {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  proof: ⟨_, _, _, _, _, hq, sq⟩

中文:
引理 pushouts_mk
  结论: {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  证明: ⟨_, _, _, _, _, hq, sq⟩
-/
lemma pushouts_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout f q p g) (hq : P q) :
    P.pushouts p :=
  ⟨_, _, _, _, _, hq, sq⟩

/--
lemma `le_pushouts` / 引理 `le_pushouts`

English:
lemma le_pushouts
  statement: P <= P.pushouts
  proof: by
  intro X Y p hp
  exact P.pushouts_mk IsPushout.of_id_fst hp

中文:
引理 le_pushouts
  结论: P <= P.pushouts
  证明: by
  intro X Y p hp
  exact P.pushouts_mk IsPushout.of_id_fst hp

Depends on / 依赖: IsPushout, IsPushout.of_id_fst, P.pushouts_mk, of_id_fst, pushouts_mk
-/
lemma le_pushouts : P <= P.pushouts := by
  intro X Y p hp
  exact P.pushouts_mk IsPushout.of_id_fst hp

/--
lemma `pushouts_monotone` / 引理 `pushouts_monotone`

English:
lemma pushouts_monotone
  statement: Monotone (pushouts (C := C))
  proof: by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

中文:
引理 pushouts_monotone
  结论: 递增 (pushouts (C := C))
  证明: by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩
-/
lemma pushouts_monotone : Monotone (pushouts (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.pushouts.RespectsIso
  body: RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)

中文:
实例 :
  签名: P.pushouts.RespectsIso
  定义体: RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)

Depends on / 依赖: IsPushout, IsPushout.of_horiz_isIso, IsPushout.paste_horiz, RespectsIso, RespectsIso.of_respects_arrow_iso, e.hom.left, e.hom.right, e.hom.w, of_horiz_isIso, of_respects_arrow_iso, paste_horiz
-/
instance : P.pushouts.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨A, B, p, f, g, hp, h⟩
    exact ⟨A, B, p, f ≫ e.hom.left, g ≫ e.hom.right, hp,
      IsPushout.paste_horiz h (IsPushout.of_horiz_isIso ⟨e.hom.w⟩)⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.pullbacks.RespectsIso
  body: RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨X, Y, p, f, g, hp, h⟩
    exact ⟨X, Y, p, e.inv.left ≫ f, e.inv.right ≫ g, hp,
      IsPullback.paste_horiz (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) h⟩)

中文:
实例 :
  签名: P.pullbacks.RespectsIso
  定义体: RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨X, Y, p, f, g, hp, h⟩
    exact ⟨X, Y, p, e.inv.left ≫ f, e.inv.right ≫ g, hp,
      IsPullback.paste_horiz (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) h⟩)

Depends on / 依赖: IsPullback, IsPullback.of_horiz_isIso, IsPullback.paste_horiz, RespectsIso, RespectsIso.of_respects_arrow_iso, e.inv.left, e.inv.right, e.inv.w, of_horiz_isIso, of_respects_arrow_iso, paste_horiz
-/
instance : P.pullbacks.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro q q' e ⟨X, Y, p, f, g, hp, h⟩
    exact ⟨X, Y, p, e.inv.left ≫ f, e.inv.right ≫ g, hp,
      IsPullback.paste_horiz (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) h⟩)

/--
lemma `isomorphisms_le_pushouts` / 引理 `isomorphisms_le_pushouts`

English:
lemma isomorphisms_le_pushouts
  proof: by
  intro X Y f (_ : IsIso f)
  obtain ⟨A, B, p, hp, g, _⟩ := h X
  exact ⟨A, B, p, p ≫ g, g ≫ f, hp, (IsPushout.of_id_snd (f := p ≫ g)).of_iso
    (Iso.refl _) (Iso.refl _) (asIso p) (asIso f) (by simp) (by simp) (by simp) (by simp)⟩

中文:
引理 isomorphisms_le_pushouts
  证明: by
  intro X Y f (_ : IsIso f)
  obtain ⟨A, B, p, hp, g, _⟩ := h X
  exact ⟨A, B, p, p ≫ g, g ≫ f, hp, (IsPushout.of_id_snd (f := p ≫ g)).of_iso
    (Iso.refl _) (Iso.refl _) (asIso p) (asIso f) (by simp) (by simp) (by simp) (by simp)⟩

Depends on / 依赖: IsPushout, IsPushout.of_id_snd, Iso.refl, of_id_snd, of_iso
-/
lemma isomorphisms_le_pushouts
    (h : forall (X : C), exists (A B : C) (p : A ⟶ B) (_ : P p) (_ : B ⟶ X), IsIso p) :
    isomorphisms C <= P.pushouts := by
  intro X Y f (_ : IsIso f)
  obtain ⟨A, B, p, hp, g, _⟩ := h X
  exact ⟨A, B, p, p ≫ g, g ≫ f, hp, (IsPushout.of_id_snd (f := p ≫ g)).of_iso
    (Iso.refl _) (Iso.refl _) (asIso p) (asIso f) (by simp) (by simp) (by simp) (by simp)⟩

/--
Definition of `IsStableUnderBaseChange` / `IsStableUnderBaseChange` 的定义

English:
class IsStableUnderBaseChange
  parameters: : Prop where
  axioms and operations (1):
    - of_isPullback({X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : P g)) : P g'

中文:
类 是StableUnderBaseChange
  参数: : 命题 where
  公理与运算 (1 个):
    - of_isPullback({X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : 是拉回 f' g' g f) (hg : P g)) : P g'
-/
class IsStableUnderBaseChange : Prop where
  of_isPullback {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.pullbacks.IsStableUnderBaseChange
  body: by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pullbacks_mk (h.paste_horiz hq) hp

中文:
实例 :
  签名: P.pullbacks.是StableUnderBaseChange
  定义体: by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pullbacks_mk (h.paste_horiz hq) hp

Depends on / 依赖: P.pullbacks_mk, h.paste_horiz, paste_horiz, pullbacks_mk
-/
instance : P.pullbacks.IsStableUnderBaseChange where
  of_isPullback := by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pullbacks_mk (h.paste_horiz hq) hp

/--
Definition of `IsStableUnderCobaseChange` / `IsStableUnderCobaseChange` 的定义

English:
class IsStableUnderCobaseChange
  parameters: : Prop where
  axioms and operations (1):
    - of_isPushout({A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') (hf : P f)) : P f'

中文:
类 是StableUnderCobaseChange
  参数: : 命题 where
  公理与运算 (1 个):
    - of_isPushout({A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : 是推出 g f f' g') (hf : P f)) : P f'
-/
class IsStableUnderCobaseChange : Prop where
  of_isPushout {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.pushouts.IsStableUnderCobaseChange
  body: by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pushouts_mk (hq.paste_horiz h) hp

中文:
实例 :
  签名: P.pushouts.是StableUnderCobaseChange
  定义体: by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pushouts_mk (hq.paste_horiz h) hp

Depends on / 依赖: P.pushouts_mk, hq.paste_horiz, paste_horiz, pushouts_mk
-/
instance : P.pushouts.IsStableUnderCobaseChange where
  of_isPushout := by
    rintro _ _ _ _ _ _ _ _ h ⟨_, _, _, _, _, hp, hq⟩
    exact P.pushouts_mk (hq.paste_horiz h) hp

/--
Definition of `HasPullbacksAlong` / `HasPullbacksAlong` 的定义

English:
class HasPullbacksAlong
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - hasPullback({W} (g : W ⟶ Y)) : P g -> HasPullback g f

中文:
类 有PullbacksAlong
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - hasPullback({W} (g : W ⟶ Y)) : P g -> HasPullback g f
-/
protected class HasPullbacksAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPullback {W} (g : W ⟶ Y) : P g -> HasPullback g f

instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : P.HasPullbacksAlong f where
  hasPullback _ _ := inferInstance

/--
Definition of `HasPushoutsAlong` / `HasPushoutsAlong` 的定义

English:
class HasPushoutsAlong
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - hasPushout({W} (g : X ⟶ W)) : P g -> HasPushout g f

中文:
类 有PushoutsAlong
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - hasPushout({W} (g : X ⟶ W)) : P g -> HasPushout g f
-/
protected class HasPushoutsAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPushout {W} (g : X ⟶ W) : P g -> HasPushout g f

instance {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] : P.HasPushoutsAlong f where
  hasPushout _ _ := inferInstance

/--
Definition of `IsStableUnderBaseChangeAlong` / `IsStableUnderBaseChangeAlong` 的定义

English:
class IsStableUnderBaseChangeAlong
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - of_isPullback({Z W : C} {f' : W ⟶ Z} {g' : W ⟶ X} {g : Z ⟶ Y} (pb : IsPullback f' g' g f)) : P g -> P g'

中文:
类 是StableUnderBaseChangeAlong
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - of_isPullback({Z W : C} {f' : W ⟶ Z} {g' : W ⟶ X} {g : Z ⟶ Y} (pb : 是拉回 f' g' g f)) : P g -> P g'
-/
class IsStableUnderBaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPullback {Z W : C} {f' : W ⟶ Z} {g' : W ⟶ X} {g : Z ⟶ Y}
    (pb : IsPullback f' g' g f) : P g -> P g'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderBaseChange]
  signature: {X Y : C} (f : X ⟶ Y)
  body: IsStableUnderBaseChange.of_isPullback

中文:
实例 [P.是StableUnderBaseChange]
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: IsStableUnderBaseChange.of_isPullback

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.of_isPullback, of_isPullback
-/
instance [P.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) : P.IsStableUnderBaseChangeAlong f where
  of_isPullback := IsStableUnderBaseChange.of_isPullback

/--
Definition of `IsStableUnderCobaseChangeAlong` / `IsStableUnderCobaseChangeAlong` 的定义

English:
class IsStableUnderCobaseChangeAlong
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - of_isPushout({Z W : C} {f' : Z ⟶ W} {g' : Y ⟶ W} {g : X ⟶ Z} (pb : IsPushout f g g' f')) : P g -> P g'

中文:
类 是StableUnderCobaseChangeAlong
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - of_isPushout({Z W : C} {f' : Z ⟶ W} {g' : Y ⟶ W} {g : X ⟶ Z} (pb : 是推出 f g g' f')) : P g -> P g'
-/
class IsStableUnderCobaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPushout {Z W : C} {f' : Z ⟶ W} {g' : Y ⟶ W} {g : X ⟶ Z}
    (pb : IsPushout f g g' f') : P g -> P g'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderCobaseChange]
  signature: {X Y : C} (f : X ⟶ Y)
  body: IsStableUnderCobaseChange.of_isPushout

alias of_isPullback := IsStableUnderBaseChange.of_isPullback

中文:
实例 [P.是StableUnderCobaseChange]
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: IsStableUnderCobaseChange.of_isPushout

alias of_isPullback := IsStableUnderBaseChange.of_isPullback

Depends on / 依赖: IsStableUnderCobaseChange, IsStableUnderCobaseChange.of_isPushout, of_isPushout
-/
instance [P.IsStableUnderCobaseChange] {X Y : C} (f : X ⟶ Y) :
    P.IsStableUnderCobaseChangeAlong f where
  of_isPushout := IsStableUnderCobaseChange.of_isPushout

alias of_isPullback := IsStableUnderBaseChange.of_isPullback

/--
lemma `isStableUnderBaseChange_iff_pullbacks_le` / 引理 `isStableUnderBaseChange_iff_pullbacks_le`

English:
lemma isStableUnderBaseChange_iff_pullbacks_le
  proof: by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

中文:
引理 isStableUnderBaseChange_iff_pullbacks_le
  证明: by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

Depends on / 依赖: of_isPullback
-/
lemma isStableUnderBaseChange_iff_pullbacks_le :
    P.IsStableUnderBaseChange ↔ P.pullbacks <= P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

/--
lemma `pullbacks_le` / 引理 `pullbacks_le`

English:
lemma pullbacks_le
  given: [P.IsStableUnderBaseChange]
  statement: P.pullbacks <= P
  proof: by
  rwa [← isStableUnderBaseChange_iff_pullbacks_le]

中文:
引理 pullbacks_le
  条件: [P.是StableUnderBaseChange]
  结论: P.pullbacks <= P
  证明: by
  rwa [← isStableUnderBaseChange_iff_pullbacks_le]

Depends on / 依赖: isStableUnderBaseChange_iff_pullbacks_le
-/
lemma pullbacks_le [P.IsStableUnderBaseChange] : P.pullbacks <= P := by
  rwa [← isStableUnderBaseChange_iff_pullbacks_le]

variable {P} in
/--
theorem `IsStableUnderBaseChange.mk'` / 定理 `IsStableUnderBaseChange.mk'`

English:
theorem IsStableUnderBaseChange.mk'
  statement: [RespectsIso P]
  proof: by
    have : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv]; rw [sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg

中文:
定理 是StableUnderBaseChange.mk'
  结论: [RespectsIso P]
  证明: by
    have : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv]; rw [sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg

Depends on / 依赖: HasPullback, P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, e.inv, hasPullback, isoPullback, isoPullback_inv_fst, sq.flip.hasPullback, sq.flip.isoPullback, sq.flip.isoPullback_inv_fst
-/
theorem IsStableUnderBaseChange.mk' [RespectsIso P]
    (hP₂ : forall (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (_ : P g),
      P (pullback.fst f g)) :
    IsStableUnderBaseChange P where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    have : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv]; rw [sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg

/--
lemma `IsStableUnderBaseChange.of_forall_exists_isPullback` / 引理 `IsStableUnderBaseChange.of_forall_exists_isPullback`

English:
lemma IsStableUnderBaseChange.of_forall_exists_isPullback
  statement: {P : MorphismProperty C} [P.RespectsIso]
  proof: by
  refine .mk' fun X Y S f g _ hg => ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

中文:
引理 是StableUnderBaseChange.of_对任意_存在_isPullback
  结论: {P : MorphismProperty C} [P.RespectsIso]
  证明: by
  refine .mk' fun X Y S f g _ hg => ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

Depends on / 依赖: P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, h.isoPullback_inv_fst, isoPullback_inv_fst
-/
lemma IsStableUnderBaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : forall {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (_ : P g),
      exists (T : C) (fst : T ⟶ X) (snd : T ⟶ Y), IsPullback fst snd f g ∧ P fst) :
    P.IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ hg => ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

variable (C)

/--
Instance `IsStableUnderBaseChange.isomorphisms` / 实例 `IsStableUnderBaseChange.isomorphisms`

English:
instance IsStableUnderBaseChange.isomorphisms
  signature: :
  body: h.isIso_snd_of_isIso

中文:
实例 是StableUnderBaseChange.isomorphisms
  签名: :
  定义体: h.isIso_snd_of_isIso

Depends on / 依赖: h.isIso_snd_of_isIso, isIso_snd_of_isIso
-/
instance IsStableUnderBaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderBaseChange where
  of_isPullback h _ := h.isIso_snd_of_isIso

/--
Instance `IsStableUnderBaseChange.monomorphisms` / 实例 `IsStableUnderBaseChange.monomorphisms`

English:
instance IsStableUnderBaseChange.monomorphisms
  signature: :
  body: h.mono_snd_of_mono

中文:
实例 是StableUnderBaseChange.monomorphisms
  签名: :
  定义体: h.mono_snd_of_mono

Depends on / 依赖: h.mono_snd_of_mono, mono_snd_of_mono
-/
instance IsStableUnderBaseChange.monomorphisms :
    (monomorphisms C).IsStableUnderBaseChange where
  of_isPullback h _ := h.mono_snd_of_mono

variable {C P}

instance (priority := 900) IsStableUnderBaseChange.respectsIso
    [IsStableUnderBaseChange P] : RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e
  exact of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))

/--
theorem `pullback_fst` / 定理 `pullback_fst`

English:
theorem pullback_fst
  statement: {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
  proof: IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g).flip H

中文:
定理 pullback_fst
  结论: {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
  证明: IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g).flip H

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsStableUnderBaseChangeAlong, IsStableUnderBaseChangeAlong.of_isPullback, of_hasPullback, of_isPullback
-/
theorem pullback_fst {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong f] (H : P g) : P (pullback.fst f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g).flip H

/--
theorem `pullback_snd` / 定理 `pullback_snd`

English:
theorem pullback_snd
  statement: {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
  proof: IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g) H

中文:
定理 pullback_snd
  结论: {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
  证明: IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g) H

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsStableUnderBaseChangeAlong, IsStableUnderBaseChangeAlong.of_isPullback, of_hasPullback, of_isPullback
-/
theorem pullback_snd {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong g] (H : P f) : P (pullback.snd f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g) H

/--
theorem `baseChange_obj` / 定理 `baseChange_obj`

English:
theorem baseChange_obj
  statement: {S S' : C} (f : S' ⟶ S)
  proof: pullback_snd X.hom f H

中文:
定理 baseChange_obj
  结论: {S S' : C} (f : S' ⟶ S)
  证明: pullback_snd X.hom f H

Depends on / 依赖: X.hom, pullback_snd
-/
theorem baseChange_obj {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (X : Over S) (H : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  pullback_snd X.hom f H

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullbackLift_fst_snd` / 定理 `pullbackLift_fst_snd`

English:
theorem pullbackLift_fst_snd
  statement: [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
  proof: by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

@[deprecated (since := "2026-03-20")]
alias baseChange_map' := pul

中文:
定理 pullbackLift_fst_snd
  结论: [是StableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
  证明: by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

@[deprecated (since := "2026-03-20")]
alias baseChange_map' := pul

Depends on / 依赖: pullback, pullback.fst
-/
theorem pullbackLift_fst_snd [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) [HasPullback v₁₂ f]
    [HasPullback v₂₂ f] (H : P g) : P (pullback.lift (f := v₂₂) (g := f) (pullback.fst v₁₂ f ≫ g)
    (pullback.snd v₁₂ f) (by simp [pullback.condition, ← hv₁₂])) := by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

@[deprecated (since := "2026-03-20")]
alias baseChange_map' := pullbackLift_fst_snd

/--
theorem `overPullbackMap` / 定理 `overPullbackMap`

English:
theorem overPullbackMap
  statement: [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S)
  proof: pullbackLift_fst_snd f (g.w.symm) H

@[deprecated (since := "2026-03-20")]
alias baseChange_map := overPullbackMap

中文:
定理 overPullbackMap
  结论: [是StableUnderBaseChange P] {S S' : C} (f : S' ⟶ S)
  证明: pullbackLift_fst_snd f (g.w.symm) H

@[deprecated (since := "2026-03-20")]
alias baseChange_map := overPullbackMap

Depends on / 依赖: g.w.symm, pullbackLift_fst_snd
-/
theorem overPullbackMap [IsStableUnderBaseChange P] {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] {X Y : Over S} (g : X ⟶ Y) (H : P g.left) :
    P ((Over.pullback f).map g).left :=
  pullbackLift_fst_snd f (g.w.symm) H

@[deprecated (since := "2026-03-20")]
alias baseChange_map := overPullbackMap

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] hasPullback_symmetry_of_hasPullbacksAlong in
/--
theorem `pullbackMap` / 定理 `pullbackMap`

English:
theorem pullbackMap
  proof: by
  have : HasPullbacksAlong (Over.mk f).hom := by cat_disch
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).le

中文:
定理 pullbackMap
  证明: by
  have : HasPullbacksAlong (Over.mk f).hom := by cat_disch
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).le

Depends on / 依赖: Category, Category.comp_id, HasPullbacksAlong, Over.homMk, Over.mk, Over.pullback, P.cancel_left_of_respectsIso, P.comp_mem, cancel_left_of_respectsIso, cat_disch, comp_id, comp_mem, exacts, overPullbackMap, pullback, pullback.map, pullbackSymmetry
-/
theorem pullbackMap
    [IsStableUnderBaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : X ⟶ S}
    [HasPullbacksAlong f] {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'}
    [HasPullbacksAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have : HasPullbacksAlong (Over.mk f).hom := by cat_disch
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((Over.pullback g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [overPullbackMap _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂,
    overPullbackMap _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁]

@[deprecated (since := "2026-03-20")]
alias pullback_map := pullbackMap

/--
Instance `IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms` / 实例 `IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms`

English:
instance IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  body: by
    have : f = (asIso (pullback.fst (f ≫ g) g)).inv ≫ pullback.snd (f ≫ g) g := by
      simp [← cancel_mono g, pullback.condition]
    rw [this]; rw [cancel_left_of_respectsIso (P := P)]
    exact P.pullback_snd _ _ hcomp

alias of_isPushout := IsStableUnderCobaseChange.of_isPushout

中文:
实例 是StableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  定义体: by
    have : f = (asIso (pullback.fst (f ≫ g) g)).inv ≫ pullback.snd (f ≫ g) g := by
      simp [← cancel_mono g, pullback.condition]
    rw [this]; rw [cancel_left_of_respectsIso (P := P)]
    exact P.pullback_snd _ _ hcomp

alias of_isPushout := IsStableUnderCobaseChange.of_isPushout

Depends on / 依赖: P.pullback_snd, cancel_left_of_respectsIso, cancel_mono, condition, pullback, pullback.condition, pullback.fst, pullback.snd, pullback_snd
-/
instance IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
    [P.IsStableUnderBaseChange] : P.HasOfPostcompProperty (MorphismProperty.monomorphisms C) where
  of_postcomp {X Y Z} f g (hg : Mono g) hcomp := by
    have : f = (asIso (pullback.fst (f ≫ g) g)).inv ≫ pullback.snd (f ≫ g) g := by
      simp [← cancel_mono g, pullback.condition]
    rw [this]; rw [cancel_left_of_respectsIso (P := P)]
    exact P.pullback_snd _ _ hcomp

alias of_isPushout := IsStableUnderCobaseChange.of_isPushout

/--
lemma `isStableUnderCobaseChange_iff_pushouts_le` / 引理 `isStableUnderCobaseChange_iff_pushouts_le`

English:
lemma isStableUnderCobaseChange_iff_pushouts_le
  proof: by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPushout h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

中文:
引理 isStableUnderCobaseChange_iff_pushouts_le
  证明: by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPushout h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

Depends on / 依赖: of_isPushout
-/
lemma isStableUnderCobaseChange_iff_pushouts_le :
    P.IsStableUnderCobaseChange ↔ P.pushouts <= P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPushout h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

/--
lemma `pushouts_le` / 引理 `pushouts_le`

English:
lemma pushouts_le
  given: [P.IsStableUnderCobaseChange]
  statement: P.pushouts <= P
  proof: by
  rwa [← isStableUnderCobaseChange_iff_pushouts_le]

@[simp]

中文:
引理 pushouts_le
  条件: [P.是StableUnderCobaseChange]
  结论: P.pushouts <= P
  证明: by
  rwa [← isStableUnderCobaseChange_iff_pushouts_le]

@[simp]

Depends on / 依赖: isStableUnderCobaseChange_iff_pushouts_le
-/
lemma pushouts_le [P.IsStableUnderCobaseChange] : P.pushouts <= P := by
  rwa [← isStableUnderCobaseChange_iff_pushouts_le]

@[simp]
/--
lemma `pushouts_le_iff` / 引理 `pushouts_le_iff`

English:
lemma pushouts_le_iff
  given: {P Q : MorphismProperty C} [Q.IsStableUnderCobaseChange]
  proof: by
  constructor
  · exact le_trans P.le_pushouts
  · intro h
    exact le_trans (pushouts_monotone h) pushouts_le

中文:
引理 pushouts_le_iff
  条件: {P Q : MorphismProperty C} [Q.是StableUnderCobaseChange]
  证明: by
  constructor
  · exact le_trans P.le_pushouts
  · intro h
    exact le_trans (pushouts_monotone h) pushouts_le

Depends on / 依赖: P.le_pushouts, le_pushouts, le_trans, pushouts_le, pushouts_monotone
-/
lemma pushouts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderCobaseChange] :
    P.pushouts <= Q ↔ P <= Q := by
  constructor
  · exact le_trans P.le_pushouts
  · intro h
    exact le_trans (pushouts_monotone h) pushouts_le

/--
theorem `IsStableUnderCobaseChange.mk'` / 定理 `IsStableUnderCobaseChange.mk'`

English:
theorem IsStableUnderCobaseChange.mk'
  statement: [RespectsIso P]
  proof: by
    have : HasPushout f g := sq.flip.hasPushout
    let e := sq.flip.isoPushout
    rw [← P.cancel_right_of_respectsIso _ e.hom]; rw [sq.flip.inr_isoPushout_hom]
    exact hP₂ _ _ _ f g hf

中文:
定理 是StableUnderCobaseChange.mk'
  结论: [RespectsIso P]
  证明: by
    have : HasPushout f g := sq.flip.hasPushout
    let e := sq.flip.isoPushout
    rw [← P.cancel_right_of_respectsIso _ e.hom]; rw [sq.flip.inr_isoPushout_hom]
    exact hP₂ _ _ _ f g hf

Depends on / 依赖: HasPushout, P.cancel_right_of_respectsIso, cancel_right_of_respectsIso, e.hom, hasPushout, inr_isoPushout_hom, isoPushout, sq.flip.hasPushout, sq.flip.inr_isoPushout_hom, sq.flip.isoPushout
-/
theorem IsStableUnderCobaseChange.mk' [RespectsIso P]
    (hP₂ : forall (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g] (_ : P f),
      P (pushout.inr f g)) :
    IsStableUnderCobaseChange P where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    have : HasPushout f g := sq.flip.hasPushout
    let e := sq.flip.isoPushout
    rw [← P.cancel_right_of_respectsIso _ e.hom]; rw [sq.flip.inr_isoPushout_hom]
    exact hP₂ _ _ _ f g hf

/--
lemma `IsStableUnderCobaseChange.of_forall_exists_isPullback` / 引理 `IsStableUnderCobaseChange.of_forall_exists_isPullback`

English:
lemma IsStableUnderCobaseChange.of_forall_exists_isPullback
  statement: {P : MorphismProperty C} [P.RespectsIso]
  proof: by
  refine .mk' fun X Y S f g _ hg => ?_
  obtain ⟨T, inl, inr, h, hinl⟩ := H f g hg
  rwa [← h.inr_isoPushout_hom, P.cancel_right_of_respectsIso]

中文:
引理 是StableUnderCobaseChange.of_对任意_存在_isPullback
  结论: {P : MorphismProperty C} [P.RespectsIso]
  证明: by
  refine .mk' fun X Y S f g _ hg => ?_
  obtain ⟨T, inl, inr, h, hinl⟩ := H f g hg
  rwa [← h.inr_isoPushout_hom, P.cancel_right_of_respectsIso]

Depends on / 依赖: P.cancel_right_of_respectsIso, cancel_right_of_respectsIso, h.inr_isoPushout_hom, inr_isoPushout_hom
-/
lemma IsStableUnderCobaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : forall {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] (_ : P f),
      exists (T : C) (inl : X ⟶ T) (inr : Y ⟶ T), IsPushout f g inl inr ∧ P inr) :
    P.IsStableUnderCobaseChange := by
  refine .mk' fun X Y S f g _ hg => ?_
  obtain ⟨T, inl, inr, h, hinl⟩ := H f g hg
  rwa [← h.inr_isoPushout_hom, P.cancel_right_of_respectsIso]

/--
Instance `IsStableUnderCobaseChange.isomorphisms` / 实例 `IsStableUnderCobaseChange.isomorphisms`

English:
instance IsStableUnderCobaseChange.isomorphisms
  signature: :
  body: h.isIso_inl_of_isIso

中文:
实例 是StableUnderCobaseChange.isomorphisms
  签名: :
  定义体: h.isIso_inl_of_isIso

Depends on / 依赖: h.isIso_inl_of_isIso, isIso_inl_of_isIso
-/
instance IsStableUnderCobaseChange.isomorphisms :
    (isomorphisms C).IsStableUnderCobaseChange where
  of_isPushout h _ := h.isIso_inl_of_isIso

variable (C) in
/--
Instance `IsStableUnderCobaseChange.epimorphisms` / 实例 `IsStableUnderCobaseChange.epimorphisms`

English:
instance IsStableUnderCobaseChange.epimorphisms
  signature: :
  body: h.epi_inl_of_epi

中文:
实例 是StableUnderCobaseChange.epimorphisms
  签名: :
  定义体: h.epi_inl_of_epi

Depends on / 依赖: epi_inl_of_epi, h.epi_inl_of_epi
-/
instance IsStableUnderCobaseChange.epimorphisms :
    (epimorphisms C).IsStableUnderCobaseChange where
  of_isPushout h _ := h.epi_inl_of_epi

/--
Instance `IsStableUnderCobaseChange.respectsIso` / 实例 `IsStableUnderCobaseChange.respectsIso`

English:
instance IsStableUnderCobaseChange.respectsIso
  body: RespectsIso.of_respects_arrow_iso _ fun _ _ e =>
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

中文:
实例 是StableUnderCobaseChange.respectsIso
  定义体: RespectsIso.of_respects_arrow_iso _ fun _ _ e =>
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

Depends on / 依赖: CommSq, CommSq.mk, IsPushout, IsPushout.of_horiz_isIso, RespectsIso, RespectsIso.of_respects_arrow_iso, e.hom.w, of_horiz_isIso, of_isPushout, of_respects_arrow_iso
-/
instance IsStableUnderCobaseChange.respectsIso
    [IsStableUnderCobaseChange P] : RespectsIso P :=
  RespectsIso.of_respects_arrow_iso _ fun _ _ e =>
    of_isPushout (IsPushout.of_horiz_isIso (CommSq.mk e.hom.w))

/--
theorem `pushout_inl` / 定理 `pushout_inl`

English:
theorem pushout_inl
  statement: {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
  proof: IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g) H

中文:
定理 pushout_inl
  结论: {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
  证明: IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g) H

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, IsStableUnderCobaseChangeAlong, IsStableUnderCobaseChangeAlong.of_isPushout, of_hasPushout, of_isPushout
-/
theorem pushout_inl {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
    [P.IsStableUnderCobaseChangeAlong f] (H : P g) :
    P (pushout.inl f g) :=
  IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g) H

/--
theorem `pushout_inr` / 定理 `pushout_inr`

English:
theorem pushout_inr
  statement: {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
  proof: IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g).flip H

中文:
定理 pushout_inr
  结论: {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
  证明: IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g).flip H

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, IsStableUnderCobaseChangeAlong, IsStableUnderCobaseChangeAlong.of_isPushout, of_hasPushout, of_isPushout
-/
theorem pushout_inr {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [HasPushout f g]
    [P.IsStableUnderCobaseChangeAlong g] (H : P f) : P (pushout.inr f g) :=
  IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout f g).flip H

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pushoutDesc_inl_inr` / 定理 `pushoutDesc_inl_inr`

English:
theorem pushoutDesc_inl_inr
  statement: [IsStableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ S')
  proof: by
  subst hv₁₂
  refine IsStableUnderCobaseChangeAlong.of_isPushout (f' := pushout.inl (v₂₂ ≫ g) f)
    (f := pushout.inl v₂₂ f) ?_ H
  refine IsPushout.of_top ?_ (by simp) (IsPushout.of_hasPushout v₂₂ f).flip
  simpa using (IsPushout.of_hasPushout (v₂₂ ≫ g) f).flip

中文:
定理 pushoutDesc_inl_inr
  结论: [是StableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ S')
  证明: by
  subst hv₁₂
  refine IsStableUnderCobaseChangeAlong.of_isPushout (f' := pushout.inl (v₂₂ ≫ g) f)
    (f := pushout.inl v₂₂ f) ?_ H
  refine IsPushout.of_top ?_ (by simp) (IsPushout.of_hasPushout v₂₂ f).flip
  simpa using (IsPushout.of_hasPushout (v₂₂ ≫ g) f).flip

Depends on / 依赖: pushout, pushout.inl
-/
theorem pushoutDesc_inl_inr [IsStableUnderCobaseChange P] {S S' X Y : C} (f : S ⟶ S')
    {v₁₂ : S ⟶ X} {v₂₂ : S ⟶ Y} {g : Y ⟶ X} (hv₁₂ : v₁₂ = v₂₂ ≫ g) [HasPushout v₁₂ f]
    [HasPushout v₂₂ f] (H : P g) :
    P (pushout.desc (f := v₂₂) (g := f) (g ≫ pushout.inl v₁₂ f)
      (pushout.inr v₁₂ f) (by simp [pushout.condition, ← reassoc_of% hv₁₂])) := by
  subst hv₁₂
  refine IsStableUnderCobaseChangeAlong.of_isPushout (f' := pushout.inl (v₂₂ ≫ g) f)
    (f := pushout.inl v₂₂ f) ?_ H
  refine IsPushout.of_top ?_ (by simp) (IsPushout.of_hasPushout v₂₂ f).flip
  simpa using (IsPushout.of_hasPushout (v₂₂ ≫ g) f).flip

/--
theorem `underPushoutMap` / 定理 `underPushoutMap`

English:
theorem underPushoutMap
  statement: [IsStableUnderCobaseChange P] {S S' : C} (f : S' ⟶ S)
  proof: pushoutDesc_inl_inr f g.w.symm H

中文:
定理 underPushoutMap
  结论: [是StableUnderCobaseChange P] {S S' : C} (f : S' ⟶ S)
  证明: pushoutDesc_inl_inr f g.w.symm H

Depends on / 依赖: g.w.symm, pushoutDesc_inl_inr
-/
theorem underPushoutMap [IsStableUnderCobaseChange P] {S S' : C} (f : S' ⟶ S)
    [HasPushoutsAlong f] {X Y : Under S'} (g : X ⟶ Y) (H : P g.right) :
    P ((Under.pushout f).map g).right :=
  pushoutDesc_inl_inr f g.w.symm H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] hasPushouts_symmetry_of_hasPushoutsAlong in
/--
theorem `pushoutMap` / 定理 `pushoutMap`

English:
theorem pushoutMap
  proof: by
  have : HasPushoutsAlong (Under.mk g').hom := by cat_disch
  have : pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂]) =
      ((pushoutSymmetry _ _).hom ≫
        ((Under.pushout f).map (Under.homMk _ e₂.symm : Under.mk g ⟶ Under.mk g')).right) ≫
        (pushoutSymmetry _ _).hom ≫

中文:
定理 pushoutMap
  证明: by
  have : HasPushoutsAlong (Under.mk g').hom := by cat_disch
  have : pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂]) =
      ((pushoutSymmetry _ _).hom ≫
        ((Under.pushout f).map (Under.homMk _ e₂.symm : Under.mk g ⟶ Under.mk g')).right) ≫
        (pushoutSymmetry _ _).hom ≫

Depends on / 依赖: HasPushoutsAlong, P.cancel_left_of_respectsIso, P.comp_mem, Under.homMk, Under.mk, Under.pushout, cancel_left_of_respectsIso, cat_disch, comp_mem, exacts, pushout, pushout.map, pushoutSymmetry, underPushoutMap
-/
theorem pushoutMap
    [IsStableUnderCobaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C} {f : S ⟶ X}
    {g : S ⟶ Y} {f' : S ⟶ X'} {g' : S ⟶ Y'} {i₁ : X ⟶ X'} [HasPushoutsAlong f]
    [HasPushoutsAlong g'] {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f' = f ≫ i₁) (e₂ : g' = g ≫ i₂) :
    P (pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂])) := by
  have : HasPushoutsAlong (Under.mk g').hom := by cat_disch
  have : pushout.map f g f' g' i₁ i₂ (𝟙 _) (by simp [e₁]) (by simp [e₂]) =
      ((pushoutSymmetry _ _).hom ≫
        ((Under.pushout f).map (Under.homMk _ e₂.symm : Under.mk g ⟶ Under.mk g')).right) ≫
        (pushoutSymmetry _ _).hom ≫
        ((Under.pushout g').map (Under.homMk _ e₁.symm : Under.mk f ⟶ Under.mk f')).right := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  exacts [underPushoutMap _ _ h₂, underPushoutMap _ _ h₁]

/--
Instance `IsStableUnderCobaseChange.hasOfPrecompProperty_epimorphisms` / 实例 `IsStableUnderCobaseChange.hasOfPrecompProperty_epimorphisms`

English:
instance IsStableUnderCobaseChange.hasOfPrecompProperty_epimorphisms
  body: by
    have : g = pushout.inr (f ≫ g) f ≫ (asIso (pushout.inl (f ≫ g) f)).inv := by
      rw [asIso_inv]; rw [IsIso.eq_comp_inv]; rw [← cancel_epi f]; rw [← pushout.condition]; rw [assoc]
    rw [this]; rw [cancel_right_of_respectsIso (P := P)]
    exact P.pushout_inr _ _ hcomp

中文:
实例 是StableUnderCobaseChange.hasOfPrecompProperty_epimorphisms
  定义体: by
    have : g = pushout.inr (f ≫ g) f ≫ (asIso (pushout.inl (f ≫ g) f)).inv := by
      rw [asIso_inv]; rw [IsIso.eq_comp_inv]; rw [← cancel_epi f]; rw [← pushout.condition]; rw [assoc]
    rw [this]; rw [cancel_right_of_respectsIso (P := P)]
    exact P.pushout_inr _ _ hcomp

Depends on / 依赖: IsIso.eq_comp_inv, P.pushout_inr, asIso_inv, cancel_epi, cancel_right_of_respectsIso, condition, eq_comp_inv, pushout, pushout.condition, pushout.inl, pushout.inr, pushout_inr
-/
instance IsStableUnderCobaseChange.hasOfPrecompProperty_epimorphisms
    [P.IsStableUnderCobaseChange] : P.HasOfPrecompProperty (MorphismProperty.epimorphisms C) where
  of_precomp {X Y Z} f g (hf : Epi f) hcomp := by
    have : g = pushout.inr (f ≫ g) f ≫ (asIso (pushout.inl (f ≫ g) f)).inv := by
      rw [asIso_inv]; rw [IsIso.eq_comp_inv]; rw [← cancel_epi f]; rw [← pushout.condition]; rw [assoc]
    rw [this]; rw [cancel_right_of_respectsIso (P := P)]
    exact P.pushout_inr _ _ hcomp

/--
Instance `IsStableUnderCobaseChange.op` / 实例 `IsStableUnderCobaseChange.op`

English:
instance IsStableUnderCobaseChange.op
  signature: [IsStableUnderCobaseChange P]
  body: P.of_isPushout sq.unop hg

中文:
实例 是StableUnderCobaseChange.op
  签名: [是StableUnderCobaseChange P]
  定义体: P.of_isPushout sq.unop hg

Depends on / 依赖: P.of_isPushout, of_isPushout, sq.unop
-/
instance IsStableUnderCobaseChange.op [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.op where
  of_isPullback sq hg := P.of_isPushout sq.unop hg

/--
Instance `IsStableUnderCobaseChange.unop` / 实例 `IsStableUnderCobaseChange.unop`

English:
instance IsStableUnderCobaseChange.unop
  signature: {P : MorphismProperty Cᵒᵖ} [IsStableUnderCobaseChange P]
  body: P.of_isPushout sq.op hg

中文:
实例 是StableUnderCobaseChange.unop
  签名: {P : MorphismProperty Cᵒᵖ} [是StableUnderCobaseChange P]
  定义体: P.of_isPushout sq.op hg

Depends on / 依赖: P.of_isPushout, of_isPushout, sq.op
-/
instance IsStableUnderCobaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderCobaseChange P] :
    IsStableUnderBaseChange P.unop where
  of_isPullback sq hg := P.of_isPushout sq.op hg

/--
Instance `IsStableUnderBaseChange.op` / 实例 `IsStableUnderBaseChange.op`

English:
instance IsStableUnderBaseChange.op
  signature: [IsStableUnderBaseChange P]
  body: P.of_isPullback sq.unop hf

中文:
实例 是StableUnderBaseChange.op
  签名: [是StableUnderBaseChange P]
  定义体: P.of_isPullback sq.unop hf

Depends on / 依赖: P.of_isPullback, of_isPullback, sq.unop
-/
instance IsStableUnderBaseChange.op [IsStableUnderBaseChange P] :
    IsStableUnderCobaseChange P.op where
  of_isPushout sq hf := P.of_isPullback sq.unop hf

/--
Instance `IsStableUnderBaseChange.unop` / 实例 `IsStableUnderBaseChange.unop`

English:
instance IsStableUnderBaseChange.unop
  signature: {P : MorphismProperty Cᵒᵖ} [IsStableUnderBaseChange P]
  body: P.of_isPullback sq.op hf

中文:
实例 是StableUnderBaseChange.unop
  签名: {P : MorphismProperty Cᵒᵖ} [是StableUnderBaseChange P]
  定义体: P.of_isPullback sq.op hf

Depends on / 依赖: P.of_isPullback, of_isPullback, sq.op
-/
instance IsStableUnderBaseChange.unop {P : MorphismProperty Cᵒᵖ} [IsStableUnderBaseChange P] :
    IsStableUnderCobaseChange P.unop where
  of_isPushout sq hf := P.of_isPullback sq.op hf

/--
Instance `IsStableUnderBaseChange.inf` / 实例 `IsStableUnderBaseChange.inf`

English:
instance IsStableUnderBaseChange.inf
  signature: {P Q : MorphismProperty C} [IsStableUnderBaseChange P]
  body: ⟨of_isPullback hp hg.left, of_isPullback hp hg.right⟩

中文:
实例 是StableUnderBaseChange.下确界
  签名: {P Q : MorphismProperty C} [是StableUnderBaseChange P]
  定义体: ⟨of_isPullback hp hg.left, of_isPullback hp hg.right⟩

Depends on / 依赖: hg.left, hg.right, of_isPullback
-/
instance IsStableUnderBaseChange.inf {P Q : MorphismProperty C} [IsStableUnderBaseChange P]
    [IsStableUnderBaseChange Q] :
    IsStableUnderBaseChange (P ⊓ Q) where
  of_isPullback hp hg := ⟨of_isPullback hp hg.left, of_isPullback hp hg.right⟩

/--
Instance `IsStableUnderCobaseChange.inf` / 实例 `IsStableUnderCobaseChange.inf`

English:
instance IsStableUnderCobaseChange.inf
  signature: {P Q : MorphismProperty C} [IsStableUnderCobaseChange P]
  body: ⟨of_isPushout hp hg.left, of_isPushout hp hg.right⟩

中文:
实例 是StableUnderCobaseChange.下确界
  签名: {P Q : MorphismProperty C} [是StableUnderCobaseChange P]
  定义体: ⟨of_isPushout hp hg.left, of_isPushout hp hg.right⟩

Depends on / 依赖: hg.left, hg.right, of_isPushout
-/
instance IsStableUnderCobaseChange.inf {P Q : MorphismProperty C} [IsStableUnderCobaseChange P]
    [IsStableUnderCobaseChange Q] :
    IsStableUnderCobaseChange (P ⊓ Q) where
  of_isPushout hp hg := ⟨of_isPushout hp hg.left, of_isPushout hp hg.right⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : MorphismProperty C).IsStableUnderBaseChange
  body: trivial

中文:
实例 :
  签名: (⊤ : MorphismProperty C).是StableUnderBaseChange
  定义体: trivial
-/
instance : (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : MorphismProperty C).IsStableUnderCobaseChange
  body: trivial

中文:
实例 :
  签名: (⊤ : MorphismProperty C).是StableUnderCobaseChange
  定义体: trivial
-/
instance : (⊤ : MorphismProperty C).IsStableUnderCobaseChange where
  of_isPushout _ _ := trivial

end

section LimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category* J]

/--
Inductive type `limitsOfShape` / 归纳类型 `limitsOfShape`

English:
inductive limitsOfShape
  parameters: : MorphismProperty C
  constructors (1):
    - mk: (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂) (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) : limitsOfShape (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

中文:
归纳类型 limitsOfShape
  参数: : MorphismProperty C
  构造子 (1 个):
    - mk: (X₁ X₂ : J ⥤ C) (c₁ : 锥 X₁) (c₂ : 锥 X₂) (_ : 是极限 c₁) (h₂ : 是极限 c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) : limitsOfShape (h₂.lift (锥.mk _ (c₁.π ≫ f)))
-/
inductive limitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      limitsOfShape (h₂.lift (Cone.mk _ (c₁.π ≫ f)))

variable {W J} in
/--
lemma `limitsOfShape.mk'` / 引理 `limitsOfShape.mk'`

English:
lemma limitsOfShape.mk'
  statement: (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
  proof: by
  obtain rfl : φ = h₂.lift (Cone.mk _ (c₁.π ≫ f)) := h₂.hom_ext (fun j => by simp [hφ])
  exact ⟨_, _, _, _, h₁, _, _, hf⟩

中文:
引理 limitsOfShape.mk'
  结论: (X₁ X₂ : J ⥤ C) (c₁ : 锥 X₁) (c₂ : 锥 X₂)
  证明: by
  obtain rfl : φ = h₂.lift (Cone.mk _ (c₁.π ≫ f)) := h₂.hom_ext (fun j => by simp [hφ])
  exact ⟨_, _, _, _, h₁, _, _, hf⟩

Depends on / 依赖: Cone.mk, hom_ext
-/
lemma limitsOfShape.mk' (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (hf : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : forall j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) :
    W.limitsOfShape J φ := by
  obtain rfl : φ = h₂.lift (Cone.mk _ (c₁.π ≫ f)) := h₂.hom_ext (fun j => by simp [hφ])
  exact ⟨_, _, _, _, h₁, _, _, hf⟩

/--
lemma `limitsOfShape_monotone` / 引理 `limitsOfShape_monotone`

English:
lemma limitsOfShape_monotone
  statement: {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂)
  proof: by
  rintro _ _ _ ⟨_, _, _, _, h₁, _, f, hf⟩
  exact ⟨_, _, _, _, h₁, _, f, fun j => h _ (hf j)⟩

中文:
引理 limitsOfShape_monotone
  结论: {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂)
  证明: by
  rintro _ _ _ ⟨_, _, _, _, h₁, _, f, hf⟩
  exact ⟨_, _, _, _, h₁, _, f, fun j => h _ (hf j)⟩
-/
lemma limitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂)
    (J : Type*) [Category* J] :
    W₁.limitsOfShape J <= W₂.limitsOfShape J := by
  rintro _ _ _ ⟨_, _, _, _, h₁, _, f, hf⟩
  exact ⟨_, _, _, _, h₁, _, f, fun j => h _ (hf j)⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (W.limitsOfShape J).RespectsIso
  body: RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : g ≫ e₂.inv = e₁.inv ≫ h₂.lift (Cone.mk _ (c₁.π ≫ f)) :=
      e.inv.w.symm
    let c₁' : Cone X₁ := {

中文:
实例 :
  签名: (W.limitsOfShape J).RespectsIso
  定义体: RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : g ≫ e₂.inv = e₁.inv ≫ h₂.lift (Cone.mk _ (c₁.π ≫ f)) :=
      e.inv.w.symm
    let c₁' : Cone X₁ := {

Depends on / 依赖: Arrow.leftFunc.mapIso, Arrow.rightFunc.mapIso, Cone.ext, Cone.mk, Functor, Functor.const, IsLimit, IsLimit.ofIsoLimit, RespectsIso, RespectsIso.of_respects_arrow_iso, e.inv.w.symm, leftFunc, mapIso, ofIsoLimit, of_respects_arrow_iso, rightFunc
-/
instance : (W.limitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : g ≫ e₂.inv = e₁.inv ≫ h₂.lift (Cone.mk _ (c₁.π ≫ f)) :=
      e.inv.w.symm
    let c₁' : Cone X₁ := { pt := Y₁, π := (Functor.const _).map e₁.inv ≫ c₁.π }
    let c₂' : Cone X₂ := { pt := Y₂, π := (Functor.const _).map e₂.inv ≫ c₂.π }
    have h₁' : IsLimit c₁' := IsLimit.ofIsoLimit h₁ (Cone.ext e₁)
    have h₂' : IsLimit c₂' := IsLimit.ofIsoLimit h₂ (Cone.ext e₂)
    obtain hg : h₂'.lift (Cone.mk _ (c₁'.π ≫ f)) = g :=
      h₂'.hom_ext (fun j => by
        rw [h₂'.fac]
        simp [reassoc_of% fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, h₁', _, _, hf⟩)

variable {W J} in
/--
lemma `limitsOfShape_limMap` / 引理 `limitsOfShape_limMap`

English:
lemma limitsOfShape_limMap
  statement: {X Y : J ⥤ C}
  proof: ⟨_, _, _, _, limit.isLimit X, _, _, hf⟩

中文:
引理 limitsOfShape_limMap
  结论: {X Y : J ⥤ C}
  证明: ⟨_, _, _, _, limit.isLimit X, _, _, hf⟩

Depends on / 依赖: isLimit, limit.isLimit
-/
lemma limitsOfShape_limMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W.limitsOfShape J (limMap f) :=
  ⟨_, _, _, _, limit.isLimit X, _, _, hf⟩

/--
Definition of `IsStableUnderLimitsOfShape` / `IsStableUnderLimitsOfShape` 的定义

English:
class IsStableUnderLimitsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - condition((X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂) (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) (φ : c₁.pt ⟶ c₂.pt) (hφ : forall j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)) : W φ

中文:
类 是StableUnderLimitsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - condition((X₁ X₂ : J ⥤ C) (c₁ : 锥 X₁) (c₂ : 锥 X₂) (_ : 是极限 c₁) (h₂ : 是极限 c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) (φ : c₁.pt ⟶ c₂.pt) (hφ : 对任意 j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)) : W φ
-/
class IsStableUnderLimitsOfShape : Prop where
  condition (X₁ X₂ : J ⥤ C) (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (h₂ : IsLimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : forall j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) : W φ

/--
lemma `isStableUnderLimitsOfShape_iff_limitsOfShape_le` / 引理 `isStableUnderLimitsOfShape_iff_limitsOfShape_le`

English:
lemma isStableUnderLimitsOfShape_iff_limitsOfShape_le
  proof: by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (limitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

中文:
引理 isStableUnderLimitsOfShape_iff_limitsOfShape_le
  证明: by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (limitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

Depends on / 依赖: condition, h.condition, limitsOfShape, limitsOfShape.mk
-/
lemma isStableUnderLimitsOfShape_iff_limitsOfShape_le :
    W.IsStableUnderLimitsOfShape J ↔ W.limitsOfShape J <= W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (limitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

variable {W J}

/--
lemma `limitsOfShape_le` / 引理 `limitsOfShape_le`

English:
lemma limitsOfShape_le
  given: [W.IsStableUnderLimitsOfShape J]
  proof: by
  rwa [← isStableUnderLimitsOfShape_iff_limitsOfShape_le]

中文:
引理 limitsOfShape_le
  条件: [W.是StableUnderLimitsOfShape J]
  证明: by
  rwa [← isStableUnderLimitsOfShape_iff_limitsOfShape_le]

Depends on / 依赖: isStableUnderLimitsOfShape_iff_limitsOfShape_le
-/
lemma limitsOfShape_le [W.IsStableUnderLimitsOfShape J] :
    W.limitsOfShape J <= W := by
  rwa [← isStableUnderLimitsOfShape_iff_limitsOfShape_le]

/--
lemma `limMap` / 引理 `limMap`

English:
lemma limMap
  statement: [W.IsStableUnderLimitsOfShape J] {X Y : J ⥤ C}
  proof: limitsOfShape_le _ (limitsOfShape_limMap _ hf)

中文:
引理 limMap
  结论: [W.是StableUnderLimitsOfShape J] {X Y : J ⥤ C}
  证明: limitsOfShape_le _ (limitsOfShape_limMap _ hf)
-/
protected lemma limMap [W.IsStableUnderLimitsOfShape J] {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasLimit X] [HasLimit Y] (hf : W.functorCategory _ f) :
    W (limMap f) :=
  limitsOfShape_le _ (limitsOfShape_limMap _ hf)

end LimitsOfShape

section ColimitsOfShape

variable (W : MorphismProperty C) (J : Type*) [Category* J]

/--
Inductive type `colimitsOfShape` / 归纳类型 `colimitsOfShape`

English:
inductive colimitsOfShape
  parameters: : MorphismProperty C
  constructors (1):
    - mk: (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂) (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) : colimitsOfShape (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

中文:
归纳类型 colimitsOfShape
  参数: : MorphismProperty C
  构造子 (1 个):
    - mk: (X₁ X₂ : J ⥤ C) (c₁ : 余锥 X₁) (c₂ : 余锥 X₂) (h₁ : 是余极限 c₁) (h₂ : 是余极限 c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) : colimitsOfShape (h₁.desc (余锥.mk _ (f ≫ c₂.ι)))
-/
inductive colimitsOfShape : MorphismProperty C
  | mk (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) :
      colimitsOfShape (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))

set_option backward.isDefEq.respectTransparency false in
variable {W J} in
/--
lemma `colimitsOfShape.mk'` / 引理 `colimitsOfShape.mk'`

English:
lemma colimitsOfShape.mk'
  statement: (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
  proof: by
  obtain rfl : φ = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) := h₁.hom_ext (fun j => by simp [hφ])
  exact ⟨_, _, _, _, _, h₂, _, hf⟩

中文:
引理 colimitsOfShape.mk'
  结论: (X₁ X₂ : J ⥤ C) (c₁ : 余锥 X₁) (c₂ : 余锥 X₂)
  证明: by
  obtain rfl : φ = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) := h₁.hom_ext (fun j => by simp [hφ])
  exact ⟨_, _, _, _, _, h₂, _, hf⟩

Depends on / 依赖: Cocone, Cocone.mk, hom_ext
-/
lemma colimitsOfShape.mk' (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) (hf : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : forall j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    W.colimitsOfShape J φ := by
  obtain rfl : φ = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) := h₁.hom_ext (fun j => by simp [hφ])
  exact ⟨_, _, _, _, _, h₂, _, hf⟩

/--
lemma `colimitsOfShape_monotone` / 引理 `colimitsOfShape_monotone`

English:
lemma colimitsOfShape_monotone
  statement: {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂)
  proof: by
  rintro _ _ _ ⟨_, _, _, _, _, h₂, f, hf⟩
  exact ⟨_, _, _, _, _, h₂, f, fun j => h _ (hf j)⟩

中文:
引理 colimitsOfShape_monotone
  结论: {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂)
  证明: by
  rintro _ _ _ ⟨_, _, _, _, _, h₂, f, hf⟩
  exact ⟨_, _, _, _, _, h₂, f, fun j => h _ (hf j)⟩

Depends on / 依赖: P.ext_of_isTriangulatedClosed, Q.ext_of_isTriangulatedClosed, Q.prop_of_iso, prop_of_iso
-/
lemma colimitsOfShape_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂)
    (J : Type*) [Category* J] :
    W₁.colimitsOfShape J <= W₂.colimitsOfShape J := by
  rintro _ _ _ ⟨_, _, _, _, _, h₂, f, hf⟩
  exact ⟨_, _, _, _, _, h₂, f, fun j => h _ (hf j)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {J} in
/--
lemma `colimitsOfShape_le_of_final` / 引理 `colimitsOfShape_le_of_final`

English:
lemma colimitsOfShape_le_of_final
  given: {J' : Type*} [Category* J'] (F : J ⥤ J') [F.Final]
  proof: by
  intro _ _ _ ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
  have h₁' : IsColimit (c₁.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₁).symm h₁
  have h₂' : IsColimit (c₂.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₂).symm h₂
  have : h₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι)) =
      h₁'.desc (Coc

中文:
引理 colimitsOfShape_le_of_final
  条件: {J' : 类型} [范畴* J'] (F : J ⥤ J') [F.终]
  证明: by
  intro _ _ _ ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
  have h₁' : IsColimit (c₁.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₁).symm h₁
  have h₂' : IsColimit (c₂.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₂).symm h₂
  have : h₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι)) =
      h₁'.desc (Coc

Depends on / 依赖: Cocone, Cocone.mk, Functor, Functor.Final.isColimitWhiskerEquiv, Functor.whiskerLeft, IsColimit, hom_ext, isColimitWhiskerEquiv, whisker, whiskerLeft
-/
lemma colimitsOfShape_le_of_final {J' : Type*} [Category* J'] (F : J ⥤ J') [F.Final] :
    W.colimitsOfShape J' <= W.colimitsOfShape J := by
  intro _ _ _ ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
  have h₁' : IsColimit (c₁.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₁).symm h₁
  have h₂' : IsColimit (c₂.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c₂).symm h₂
  have : h₁.desc (Cocone.mk c₂.pt (f ≫ c₂.ι)) =
      h₁'.desc (Cocone.mk c₂.pt (Functor.whiskerLeft _ f ≫ (c₂.whisker F).ι)) :=
    h₁'.hom_ext (fun j => by
      have := h₁'.fac (Cocone.mk c₂.pt (Functor.whiskerLeft F f ≫ Functor.whiskerLeft F c₂.ι)) j
      dsimp at this ⊢
      simp [this])
  rw [this]
  exact ⟨_, _, _, _, h₁', h₂', _, fun _ => hf _⟩

variable {J} in
/--
lemma `colimitsOfShape_eq_of_equivalence` / 引理 `colimitsOfShape_eq_of_equivalence`

English:
lemma colimitsOfShape_eq_of_equivalence
  given: {J' : Type*} [Category* J'] (e : J ≌ J')
  proof: le_antisymm (W.colimitsOfShape_le_of_final e.inverse)
    (W.colimitsOfShape_le_of_final e.functor)

中文:
引理 colimitsOfShape_eq_of_equivalence
  条件: {J' : 类型} [范畴* J'] (e : J ≌ J')
  证明: le_antisymm (W.colimitsOfShape_le_of_final e.inverse)
    (W.colimitsOfShape_le_of_final e.functor)

Depends on / 依赖: W.colimitsOfShape_le_of_final, colimitsOfShape_le_of_final, e.functor, e.inverse, functor, inverse, le_antisymm
-/
lemma colimitsOfShape_eq_of_equivalence {J' : Type*} [Category* J'] (e : J ≌ J') :
    W.colimitsOfShape J = W.colimitsOfShape J' :=
  le_antisymm (W.colimitsOfShape_le_of_final e.inverse)
    (W.colimitsOfShape_le_of_final e.functor)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (W.colimitsOfShape J).RespectsIso
  body: RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : e₁.hom ≫ g = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) ≫ e₂.hom := e.hom.w
    let c₁' : Cocone X₁ := { pt := 

中文:
实例 :
  签名: (W.colimitsOfShape J).RespectsIso
  定义体: RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : e₁.hom ≫ g = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) ≫ e₂.hom := e.hom.w
    let c₁' : Cocone X₁ := { pt := 

Depends on / 依赖: Arrow.leftFunc.mapIso, Arrow.rightFunc.mapIso, Cocone, Cocone.ext, Cocone.mk, Functor, Functor.const, IsColimit, IsColimit.ofIsoColimit, RespectsIso, RespectsIso.of_respects_arrow_iso, e.hom.w, leftFunc, mapIso, ofIsoColimit, of_respects_arrow_iso, rightFunc
-/
instance : (W.colimitsOfShape J).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (by
    rintro ⟨_, _, f⟩ ⟨Y₁, Y₂, g⟩ e ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hf⟩
    let e₁ := Arrow.leftFunc.mapIso e
    let e₂ := Arrow.rightFunc.mapIso e
    have fac : e₁.hom ≫ g = h₁.desc (Cocone.mk _ (f ≫ c₂.ι)) ≫ e₂.hom := e.hom.w
    let c₁' : Cocone X₁ := { pt := Y₁, ι := c₁.ι ≫ (Functor.const _).map e₁.hom }
    let c₂' : Cocone X₂ := { pt := Y₂, ι := c₂.ι ≫ (Functor.const _).map e₂.hom }
    have h₁' : IsColimit c₁' := IsColimit.ofIsoColimit h₁ (Cocone.ext e₁)
    have h₂' : IsColimit c₂' := IsColimit.ofIsoColimit h₂ (Cocone.ext e₂)
    obtain hg : h₁'.desc (Cocone.mk _ (f ≫ c₂'.ι)) = g :=
      h₁'.hom_ext (fun j => by
        rw [h₁'.fac]
        simp [fac, c₁', c₂'])
    rw [← hg]
    exact ⟨_, _, _, _, _, h₂', _, hf⟩)

variable {W J} in
/--
lemma `colimitsOfShape_colimMap` / 引理 `colimitsOfShape_colimMap`

English:
lemma colimitsOfShape_colimMap
  statement: {X Y : J ⥤ C}
  proof: ⟨_, _, _, _, _, colimit.isColimit Y, _, hf⟩

中文:
引理 colimitsOfShape_colimMap
  结论: {X Y : J ⥤ C}
  证明: ⟨_, _, _, _, _, colimit.isColimit Y, _, hf⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
lemma colimitsOfShape_colimMap {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W.colimitsOfShape J (colimMap f) :=
  ⟨_, _, _, _, _, colimit.isColimit Y, _, hf⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local instance] IsCofiltered.isConnected in
variable {W} in
/--
lemma `colimitsOfShape.of_isColimit` / 引理 `colimitsOfShape.of_isColimit`

English:
lemma colimitsOfShape.of_isColimit
  proof: .mk' _ _ _ _ (isColimitConstCocone J (F.obj ⊥)) hc
    { app k := F.map (homOfLE bot_le)
      naturality _ _ _ := by
        dsimp
        rw [Category.id_comp]; rw [← Functor.map_comp]
        rfl } h _ (by simp)

中文:
引理 colimitsOfShape.of_isColimit
  证明: .mk' _ _ _ _ (isColimitConstCocone J (F.obj ⊥)) hc
    { app k := F.map (homOfLE bot_le)
      naturality _ _ _ := by
        dsimp
        rw [Category.id_comp]; rw [← Functor.map_comp]
        rfl } h _ (by simp)

Depends on / 依赖: Category, Category.id_comp, F.map, F.obj, Functor, Functor.map_comp, bot_le, homOfLE, id_comp, isColimitConstCocone, map_comp, naturality
-/
lemma colimitsOfShape.of_isColimit
    {J : Type*} [Preorder J] [OrderBot J] {F : J ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (h : forall (j : J), W (F.map (homOfLE bot_le : ⊥ ⟶ j))) :
    W.colimitsOfShape J (c.ι.app ⊥) :=
  .mk' _ _ _ _ (isColimitConstCocone J (F.obj ⊥)) hc
    { app k := F.map (homOfLE bot_le)
      naturality _ _ _ := by
        dsimp
        rw [Category.id_comp]; rw [← Functor.map_comp]
        rfl } h _ (by simp)

/--
Definition of `IsStableUnderColimitsOfShape` / `IsStableUnderColimitsOfShape` 的定义

English:
class IsStableUnderColimitsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - condition((X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂) (h₁ : IsColimit c₁) (h₁ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) (φ : c₁.pt ⟶ c₂.pt) (hφ : forall j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)) : W φ

中文:
类 是StableUnderColimitsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - condition((X₁ X₂ : J ⥤ C) (c₁ : 余锥 X₁) (c₂ : 余锥 X₂) (h₁ : 是余极限 c₁) (h₁ : 是余极限 c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f) (φ : c₁.pt ⟶ c₂.pt) (hφ : 对任意 j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)) : W φ
-/
class IsStableUnderColimitsOfShape : Prop where
  condition (X₁ X₂ : J ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₁ : IsColimit c₂) (f : X₁ ⟶ X₂) (_ : W.functorCategory J f)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : forall j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : W φ

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isStableUnderColimitsOfShape_iff_colimitsOfShape_le` / 引理 `isStableUnderColimitsOfShape_iff_colimitsOfShape_le`

English:
lemma isStableUnderColimitsOfShape_iff_colimitsOfShape_le
  proof: by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (colimitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

中文:
引理 isStableUnderColimitsOfShape_iff_colimitsOfShape_le
  证明: by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (colimitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

Depends on / 依赖: colimitsOfShape, colimitsOfShape.mk, condition, h.condition
-/
lemma isStableUnderColimitsOfShape_iff_colimitsOfShape_le :
    W.IsStableUnderColimitsOfShape J ↔ W.colimitsOfShape J <= W := by
  constructor
  · rintro h _ _ _ ⟨_, _, _, _, h₁, h₂, f, hf⟩
    exact h.condition _ _ _ _ h₁ h₂ f hf _ (by simp)
  · rintro h
    constructor
    intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
    exact h _ (colimitsOfShape.mk' X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ)

variable {W J}

/--
lemma `colimitsOfShape_le` / 引理 `colimitsOfShape_le`

English:
lemma colimitsOfShape_le
  given: [W.IsStableUnderColimitsOfShape J]
  proof: by
  rwa [← isStableUnderColimitsOfShape_iff_colimitsOfShape_le]

中文:
引理 colimitsOfShape_le
  条件: [W.是StableUnderColimitsOfShape J]
  证明: by
  rwa [← isStableUnderColimitsOfShape_iff_colimitsOfShape_le]

Depends on / 依赖: isStableUnderColimitsOfShape_iff_colimitsOfShape_le
-/
lemma colimitsOfShape_le [W.IsStableUnderColimitsOfShape J] :
    W.colimitsOfShape J <= W := by
  rwa [← isStableUnderColimitsOfShape_iff_colimitsOfShape_le]

/--
lemma `colimMap` / 引理 `colimMap`

English:
lemma colimMap
  statement: [W.IsStableUnderColimitsOfShape J] {X Y : J ⥤ C}
  proof: colimitsOfShape_le _ (colimitsOfShape_colimMap _ hf)

中文:
引理 colimMap
  结论: [W.是StableUnderColimitsOfShape J] {X Y : J ⥤ C}
  证明: colimitsOfShape_le _ (colimitsOfShape_colimMap _ hf)
-/
protected lemma colimMap [W.IsStableUnderColimitsOfShape J] {X Y : J ⥤ C}
    (f : X ⟶ Y) [HasColimit X] [HasColimit Y] (hf : W.functorCategory _ f) :
    W (colimMap f) :=
  colimitsOfShape_le _ (colimitsOfShape_colimMap _ hf)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C J) in
/--
Instance `IsStableUnderColimitsOfShape.isomorphisms` / 实例 `IsStableUnderColimitsOfShape.isomorphisms`

English:
instance IsStableUnderColimitsOfShape.isomorphisms
  signature: :
  body: by
    have := NatIso.isIso_of_isIso_app f
    exact ⟨h₂.desc (Cocone.mk _ (inv f ≫ c₁.ι)),
      h₁.hom_ext (fun j => by simp [reassoc_of% (hφ j)]),
      h₂.hom_ext (by simp [hφ])⟩

中文:
实例 是StableUnderColimitsOfShape.isomorphisms
  签名: :
  定义体: by
    have := NatIso.isIso_of_isIso_app f
    exact ⟨h₂.desc (Cocone.mk _ (inv f ≫ c₁.ι)),
      h₁.hom_ext (fun j => by simp [reassoc_of% (hφ j)]),
      h₂.hom_ext (by simp [hφ])⟩

Depends on / 依赖: Cocone, Cocone.mk, NatIso, NatIso.isIso_of_isIso_app, hom_ext, isIso_of_isIso_app, reassoc_of
-/
instance IsStableUnderColimitsOfShape.isomorphisms :
    (isomorphisms C).IsStableUnderColimitsOfShape J where
  condition F₁ F₂ c₁ c₂ h₁ h₂ f (_ : forall j, IsIso (f.app j)) φ hφ := by
    have := NatIso.isIso_of_isIso_app f
    exact ⟨h₂.desc (Cocone.mk _ (inv f ≫ c₁.ι)),
      h₁.hom_ext (fun j => by simp [reassoc_of% (hφ j)]),
      h₂.hom_ext (by simp [hφ])⟩

end ColimitsOfShape

/-- The condition that a property of morphisms is stable by filtered colimits. -/
@[pp_with_univ]
/--
Definition of `IsStableUnderFilteredColimits` / `IsStableUnderFilteredColimits` 的定义

English:
class IsStableUnderFilteredColimits
  parameters: (W : MorphismProperty C)
  axioms and operations (1):
    - isStableUnderColimitsOfShape((J : Type w') [Category.{w} J] [IsFiltered J]) : W.IsStableUnderColimitsOfShape J  [default: by infer_instance]

中文:
类 是StableUnderFilteredColimits
  参数: (W : MorphismProperty C)
  公理与运算 (1 个):
    - isStableUnderColimitsOfShape((J : 类型 w') [范畴.{w} J] [是Filtered J]) : W.是StableUnderColimitsOfShape J  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsStableUnderFilteredColimits (W : MorphismProperty C) : Prop where
  isStableUnderColimitsOfShape (J : Type w') [Category.{w} J] [IsFiltered J] :
    W.IsStableUnderColimitsOfShape J := by infer_instance

attribute [instance] IsStableUnderFilteredColimits.isStableUnderColimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderFilteredColimits.{w, w'} (isomorphisms C)

中文:
实例 :
  签名: 是StableUnderFilteredColimits.{w, w'} (isomorphisms C)
-/
instance : IsStableUnderFilteredColimits.{w, w'} (isomorphisms C) where

section Coproducts

variable (W : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is class of morphisms that are
isomorphic to a coproduct of a family (indexed by some `J : Type w`) of maps in `W`. -/
@[pp_with_univ]
/--
Definition of `coproducts` / `coproducts` 的定义

English:
definition coproducts
  signature: : MorphismProperty C
  body: ⨆ (J : Type w), W.colimitsOfShape (Discrete J)

中文:
定义 coproducts
  签名: : MorphismProperty C
  定义体: ⨆ (J : Type w), W.colimitsOfShape (Discrete J)

Depends on / 依赖: Discrete, W.colimitsOfShape, colimitsOfShape
-/
def coproducts : MorphismProperty C := ⨆ (J : Type w), W.colimitsOfShape (Discrete J)

/--
lemma `colimitsOfShape_le_coproducts` / 引理 `colimitsOfShape_le_coproducts`

English:
lemma colimitsOfShape_le_coproducts
  given: (J : Type w)
  proof: le_iSup (f := fun (J : Type w) => W.colimitsOfShape (Discrete J)) J

中文:
引理 colimitsOfShape_le_coproducts
  条件: (J : 类型 w)
  证明: le_iSup (f := fun (J : Type w) => W.colimitsOfShape (Discrete J)) J

Depends on / 依赖: Discrete, W.colimitsOfShape, colimitsOfShape, le_iSup
-/
lemma colimitsOfShape_le_coproducts (J : Type w) :
    W.colimitsOfShape (Discrete J) <= coproducts.{w} W :=
  le_iSup (f := fun (J : Type w) => W.colimitsOfShape (Discrete J)) J

/--
lemma `coproducts_iff` / 引理 `coproducts_iff`

English:
lemma coproducts_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp only [coproducts, iSup_iff]

中文:
引理 coproducts_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp only [coproducts, iSup_iff]

Depends on / 依赖: coproducts, iSup_iff
-/
lemma coproducts_iff {X Y : C} (f : X ⟶ Y) :
    coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Discrete J) f := by
  simp only [coproducts, iSup_iff]

/--
lemma `coproducts_of_small` / 引理 `coproducts_of_small`

English:
lemma coproducts_of_small
  statement: {X Y : C} (f : X ⟶ Y) {J : Type w'}
  proof: by
  rw [coproducts_iff]
  refine ⟨Shrink J, ?_⟩
  rwa [← W.colimitsOfShape_eq_of_equivalence (Discrete.equivalence (equivShrink.{w} J))]

中文:
引理 coproducts_of_small
  结论: {X Y : C} (f : X ⟶ Y) {J : 类型 w'}
  证明: by
  rw [coproducts_iff]
  refine ⟨Shrink J, ?_⟩
  rwa [← W.colimitsOfShape_eq_of_equivalence (Discrete.equivalence (equivShrink.{w} J))]

Depends on / 依赖: Discrete, Discrete.equivalence, Shrink, W.colimitsOfShape_eq_of_equivalence, colimitsOfShape_eq_of_equivalence, coproducts_iff, equivShrink, equivalence
-/
lemma coproducts_of_small {X Y : C} (f : X ⟶ Y) {J : Type w'}
    (hf : W.colimitsOfShape (Discrete J) f) [Small.{w} J] :
    coproducts.{w} W f := by
  rw [coproducts_iff]
  refine ⟨Shrink J, ?_⟩
  rwa [← W.colimitsOfShape_eq_of_equivalence (Discrete.equivalence (equivShrink.{w} J))]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `le_colimitsOfShape_punit` / 引理 `le_colimitsOfShape_punit`

English:
lemma le_colimitsOfShape_punit
  statement: W <= W.colimitsOfShape (Discrete PUnit.{w + 1})
  proof: by
  intro X₁ X₂ f hf
  have h := initialIsInitial (C := Discrete (PUnit.{w + 1}))
  let c₁ := coconeOfDiagramInitial (F := Discrete.functor (fun _ => X₁)) h
  let c₂ := coconeOfDiagramInitial (F := Discrete.functor (fun _ => X₂)) h
  have hc₁ : IsColimit c₁ := colimitOfDiagramInitial h _
  have hc₂

中文:
引理 le_colimitsOfShape_punit
  结论: W <= W.colimitsOfShape (离散 命题单元.{w + 1})
  证明: by
  intro X₁ X₂ f hf
  have h := initialIsInitial (C := Discrete (PUnit.{w + 1}))
  let c₁ := coconeOfDiagramInitial (F := Discrete.functor (fun _ => X₁)) h
  let c₂ := coconeOfDiagramInitial (F := Discrete.functor (fun _ => X₂)) h
  have hc₁ : IsColimit c₁ := colimitOfDiagramInitial h _
  have hc₂

Depends on / 依赖: Cocone, Cocone.mk, Discrete, Discrete.functor, Discrete.natTrans, IsColimit, IsColimit.fac, coconeOfDiagramInitial, colimitOfDiagramInitial, functor, hom_ext, initialIsInitial, natTrans
-/
lemma le_colimitsOfShape_punit : W <= W.colimitsOfShape (Discrete PUnit.{w + 1}) := by
  intro X₁ X₂ f hf
  have h := initialIsInitial (C := Discrete (PUnit.{w + 1}))
  let c₁ := coconeOfDiagramInitial (F := Discrete.functor (fun _ => X₁)) h
  let c₂ := coconeOfDiagramInitial (F := Discrete.functor (fun _ => X₂)) h
  have hc₁ : IsColimit c₁ := colimitOfDiagramInitial h _
  have hc₂ : IsColimit c₂ := colimitOfDiagramInitial h _
  have : hc₁.desc (Cocone.mk _ (Discrete.natTrans (fun _ => by exact f) ≫ c₂.ι)) = f :=
    hc₁.hom_ext (fun x => by
      obtain rfl : x = ⊥_ _ := by ext
      rw [IsColimit.fac]
      simp [c₁, c₂])
  rw [← this]
  exact ⟨_, _, _, _, _, hc₂, _, fun _ => hf⟩

/--
lemma `le_coproducts` / 引理 `le_coproducts`

English:
lemma le_coproducts
  statement: W <= coproducts.{w} W
  proof: (le_colimitsOfShape_punit.{w} W).trans
    (colimitsOfShape_le_coproducts W PUnit.{w + 1})

中文:
引理 le_coproducts
  结论: W <= coproducts.{w} W
  证明: (le_colimitsOfShape_punit.{w} W).trans
    (colimitsOfShape_le_coproducts W PUnit.{w + 1})

Depends on / 依赖: colimitsOfShape_le_coproducts, le_colimitsOfShape_punit
-/
lemma le_coproducts : W <= coproducts.{w} W :=
  (le_colimitsOfShape_punit.{w} W).trans
    (colimitsOfShape_le_coproducts W PUnit.{w + 1})

/--
lemma `coproducts_monotone` / 引理 `coproducts_monotone`

English:
lemma coproducts_monotone
  statement: Monotone (coproducts.{w} (C := C))
  proof: by
  rintro W₁ W₂ h X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact W₂.colimitsOfShape_le_coproducts J _
    (colimitsOfShape_monotone h _ _ hf)

中文:
引理 coproducts_monotone
  结论: 递增 (coproducts.{w} (C := C))
  证明: by
  rintro W₁ W₂ h X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact W₂.colimitsOfShape_le_coproducts J _
    (colimitsOfShape_monotone h _ _ hf)

Depends on / 依赖: colimitsOfShape_le_coproducts, colimitsOfShape_monotone, coproducts_iff
-/
lemma coproducts_monotone : Monotone (coproducts.{w} (C := C)) := by
  rintro W₁ W₂ h X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact W₂.colimitsOfShape_le_coproducts J _
    (colimitsOfShape_monotone h _ _ hf)

end Coproducts

section Products

variable (W : MorphismProperty C)

/--
Definition of `IsStableUnderProductsOfShape` / `IsStableUnderProductsOfShape` 的定义

English:
abbreviation IsStableUnderProductsOfShape
  signature: (J : Type*)
  body: W.IsStableUnderLimitsOfShape (Discrete J)

中文:
缩写 IsStableUnderProductsOfShape
  签名: (J : 类型)
  定义体: W.IsStableUnderLimitsOfShape (Discrete J)

Depends on / 依赖: Discrete, IsStableUnderLimitsOfShape, W.IsStableUnderLimitsOfShape
-/
abbrev IsStableUnderProductsOfShape (J : Type*) := W.IsStableUnderLimitsOfShape (Discrete J)

/--
Definition of `IsStableUnderCoproductsOfShape` / `IsStableUnderCoproductsOfShape` 的定义

English:
abbreviation IsStableUnderCoproductsOfShape
  signature: (J : Type*)
  body: W.IsStableUnderColimitsOfShape (Discrete J)

中文:
缩写 IsStableUnderCoproductsOfShape
  签名: (J : 类型)
  定义体: W.IsStableUnderColimitsOfShape (Discrete J)

Depends on / 依赖: Discrete, IsStableUnderColimitsOfShape, W.IsStableUnderColimitsOfShape
-/
abbrev IsStableUnderCoproductsOfShape (J : Type*) := W.IsStableUnderColimitsOfShape (Discrete J)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsStableUnderProductsOfShape.mk` / 引理 `IsStableUnderProductsOfShape.mk`

English:
lemma IsStableUnderProductsOfShape.mk
  statement: (J : Type*) [W.RespectsIso]
  proof: by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasLimit X₁ := ⟨c₁, hc₁⟩
    have : HasLimit X₂ := ⟨c₂, hc₂⟩
    have : HasProduct fun j => X₁.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₁.obj j)))
    have : HasProduct fun j => X₂.obj (Discrete.mk j)

中文:
引理 IsStableUnderProductsOfShape.mk
  结论: (J : 类型) [W.RespectsIso]
  证明: by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasLimit X₁ := ⟨c₁, hc₁⟩
    have : HasLimit X₂ := ⟨c₂, hc₂⟩
    have : HasProduct fun j => X₁.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₁.obj j)))
    have : HasProduct fun j => X₂.obj (Discrete.mk j)

Depends on / 依赖: Arrow.isoMk, Discrete, Discrete.mk, Discrete.natIso, HasLimit, HasProduct, IsLimit, IsLimit.conePointUniqueUpToIso, Iso.refl, W.arrow_mk_iso_iff, arrow_mk_iso_iff, conePointUniqueUpToIso, f.app, hasLimit_of_iso, isLimit, limit.isLimit, natIso
-/
lemma IsStableUnderProductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : forall (X₁ X₂ : J -> C) [HasProduct X₁] [HasProduct X₂]
      (f : forall j, X₁ j ⟶ X₂ j) (_ : forall (j : J), W (f j)),
      W (Limits.Pi.map f)) : W.IsStableUnderProductsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf α hα := by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasLimit X₁ := ⟨c₁, hc₁⟩
    have : HasLimit X₂ := ⟨c₂, hc₂⟩
    have : HasProduct fun j => X₁.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₁.obj j)))
    have : HasProduct fun j => X₂.obj (Discrete.mk j) :=
      hasLimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₂.obj j)))
    have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
    refine (W.arrow_mk_iso_iff ?_).2 hf'
    refine Arrow.isoMk
      (IsLimit.conePointUniqueUpToIso hc₁ (limit.isLimit X₁) ≪≫ (Pi.isoLimit X₁).symm)
      (IsLimit.conePointUniqueUpToIso hc₂ (limit.isLimit X₂) ≪≫ (Pi.isoLimit _).symm) ?_
    apply limit.hom_ext
    rintro ⟨j⟩
    simp [φ, hα]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsStableUnderCoproductsOfShape.mk` / 引理 `IsStableUnderCoproductsOfShape.mk`

English:
lemma IsStableUnderCoproductsOfShape.mk
  statement: (J : Type*) [W.RespectsIso]
  proof: by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasColimit X₁ := ⟨c₁, hc₁⟩
    have : HasColimit X₂ := ⟨c₂, hc₂⟩
    have : HasCoproduct fun j => X₁.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₁.obj j)))
    have : HasCoproduct fun j => X₂.obj (Disc

中文:
引理 IsStableUnderCoproductsOfShape.mk
  结论: (J : 类型) [W.RespectsIso]
  证明: by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasColimit X₁ := ⟨c₁, hc₁⟩
    have : HasColimit X₂ := ⟨c₂, hc₂⟩
    have : HasCoproduct fun j => X₁.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₁.obj j)))
    have : HasCoproduct fun j => X₂.obj (Disc

Depends on / 依赖: Arrow.isoMk, Discrete, Discrete.mk, Discrete.natIso, HasColimit, HasCoproduct, IsColimit, IsColimit.coc, Iso.refl, Sigma.isoColimit, W.arrow_mk_iso_iff, arrow_mk_iso_iff, f.app, hasColimit_of_iso, isoColimit, natIso
-/
lemma IsStableUnderCoproductsOfShape.mk (J : Type*) [W.RespectsIso]
    (hW : forall (X₁ X₂ : J -> C) [HasCoproduct X₁] [HasCoproduct X₂]
      (f : forall j, X₁ j ⟶ X₂ j) (_ : forall (j : J), W (f j)),
      W (Limits.Sigma.map f)) : W.IsStableUnderCoproductsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf α hα := by
    let φ := fun j => f.app (Discrete.mk j)
    have : HasColimit X₁ := ⟨c₁, hc₁⟩
    have : HasColimit X₂ := ⟨c₂, hc₂⟩
    have : HasCoproduct fun j => X₁.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₁.obj j)))
    have : HasCoproduct fun j => X₂.obj (Discrete.mk j) :=
      hasColimit_of_iso (Discrete.natIso (fun j => Iso.refl (X₂.obj j)))
    have hf' := hW _ _ φ (fun j => hf (Discrete.mk j))
    refine (W.arrow_mk_iso_iff ?_).1 hf'
    refine Arrow.isoMk
      ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₁) hc₁)
      ((Sigma.isoColimit _) ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit X₂) hc₂) ?_
    apply colimit.hom_ext
    rintro ⟨j⟩
    simp [φ, hα]

instance (J : Type*) [(monomorphisms C).IsStableUnderCoproductsOfShape J]
    {X₁ X₂ : J -> C} (f : forall j, X₁ j ⟶ X₂ j) [HasCoproduct X₁] [HasCoproduct X₂]
    [forall j, Mono (f j)] :
    Mono (Limits.Sigma.map f) :=
  MorphismProperty.colimMap _ (fun ⟨j⟩ => inferInstanceAs (Mono (f j)))

/--
Definition of `IsStableUnderFiniteProducts` / `IsStableUnderFiniteProducts` 的定义

English:
class IsStableUnderFiniteProducts
  parameters: : Prop where
  axioms and operations (1):
    - isStableUnderProductsOfShape((J : Type) [Finite J]) : W.IsStableUnderProductsOfShape J

中文:
类 是StableUnderFiniteProducts
  参数: : 命题 where
  公理与运算 (1 个):
    - isStableUnderProductsOfShape((J : 类型) [有限 J]) : W.IsStableUnderProductsOfShape J
-/
class IsStableUnderFiniteProducts : Prop where
  isStableUnderProductsOfShape (J : Type) [Finite J] : W.IsStableUnderProductsOfShape J

attribute [instance] IsStableUnderFiniteProducts.isStableUnderProductsOfShape

/--
Definition of `IsStableUnderFiniteCoproducts` / `IsStableUnderFiniteCoproducts` 的定义

English:
class IsStableUnderFiniteCoproducts
  parameters: : Prop where
  axioms and operations (1):
    - isStableUnderCoproductsOfShape((J : Type) [Finite J]) : W.IsStableUnderCoproductsOfShape J

中文:
类 是StableUnderFiniteCoproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - isStableUnderCoproductsOfShape((J : 类型) [有限 J]) : W.IsStableUnderCoproductsOfShape J
-/
class IsStableUnderFiniteCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type) [Finite J] : W.IsStableUnderCoproductsOfShape J

attribute [instance] IsStableUnderFiniteCoproducts.isStableUnderCoproductsOfShape

/-- The condition that a property of morphisms is stable by coproducts. -/
@[pp_with_univ]
/--
Definition of `IsStableUnderCoproducts` / `IsStableUnderCoproducts` 的定义

English:
class IsStableUnderCoproducts
  parameters: : Prop where
  axioms and operations (1):
    - isStableUnderCoproductsOfShape((J : Type w)) : W.IsStableUnderCoproductsOfShape J  [default: by infer_instance]

中文:
类 是StableUnderCoproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - isStableUnderCoproductsOfShape((J : 类型 w)) : W.IsStableUnderCoproductsOfShape J  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsStableUnderCoproducts : Prop where
  isStableUnderCoproductsOfShape (J : Type w) : W.IsStableUnderCoproductsOfShape J := by
    infer_instance

attribute [instance] IsStableUnderCoproducts.isStableUnderCoproductsOfShape

/--
lemma `coproducts_le` / 引理 `coproducts_le`

English:
lemma coproducts_le
  given: [IsStableUnderCoproducts.{w} W]
  proof: by
  intro X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact colimitsOfShape_le _ hf

@[simp]

中文:
引理 coproducts_le
  条件: [是StableUnderCoproducts.{w} W]
  证明: by
  intro X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact colimitsOfShape_le _ hf

@[simp]

Depends on / 依赖: Nat.le_induction, colimitsOfShape_le, coproducts_iff, extensionProductIter_succ, le_extensionProduct_right, le_induction, le_trans
-/
lemma coproducts_le [IsStableUnderCoproducts.{w} W] :
    coproducts.{w} W <= W := by
  intro X Y f hf
  rw [coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact colimitsOfShape_le _ hf

@[simp]
/--
lemma `coproducts_eq_self` / 引理 `coproducts_eq_self`

English:
lemma coproducts_eq_self
  given: [IsStableUnderCoproducts.{w} W]
  proof: le_antisymm W.coproducts_le W.le_coproducts

@[simp]

中文:
引理 coproducts_eq_self
  条件: [是StableUnderCoproducts.{w} W]
  证明: le_antisymm W.coproducts_le W.le_coproducts

@[simp]

Depends on / 依赖: W.coproducts_le, W.le_coproducts, coproducts_le, le_antisymm, le_coproducts
-/
lemma coproducts_eq_self [IsStableUnderCoproducts.{w} W] :
    coproducts.{w} W = W :=
  le_antisymm W.coproducts_le W.le_coproducts

@[simp]
/--
lemma `coproducts_le_iff` / 引理 `coproducts_le_iff`

English:
lemma coproducts_le_iff
  given: {P Q : MorphismProperty C} [IsStableUnderCoproducts.{w} Q]
  proof: by
  constructor
  · exact le_trans P.le_coproducts
  · intro h
    exact le_trans (coproducts_monotone h) Q.coproducts_le

中文:
引理 coproducts_le_iff
  条件: {P Q : MorphismProperty C} [是StableUnderCoproducts.{w} Q]
  证明: by
  constructor
  · exact le_trans P.le_coproducts
  · intro h
    exact le_trans (coproducts_monotone h) Q.coproducts_le

Depends on / 依赖: P.le_coproducts, Q.coproducts_le, coproducts_le, coproducts_monotone, le_coproducts, le_trans
-/
lemma coproducts_le_iff {P Q : MorphismProperty C} [IsStableUnderCoproducts.{w} Q] :
    coproducts.{w} P <= Q ↔ P <= Q := by
  constructor
  · exact le_trans P.le_coproducts
  · intro h
    exact le_trans (coproducts_monotone h) Q.coproducts_le

end Products

section Diagonal

variable [HasPullbacks C] {P : MorphismProperty C}

/--
Definition of `diagonal` / `diagonal` 的定义

English:
definition diagonal
  signature: (P : MorphismProperty C)
  body: fun _ _ f => P (pullback.diagonal f)

中文:
定义 diagonal
  签名: (P : MorphismProperty C)
  定义体: fun _ _ f => P (pullback.diagonal f)

Depends on / 依赖: diagonal, pullback, pullback.diagonal
-/
def diagonal (P : MorphismProperty C) : MorphismProperty C := fun _ _ f => P (pullback.diagonal f)

/--
theorem `diagonal_iff` / 定理 `diagonal_iff`

English:
theorem diagonal_iff
  given: {X Y : C} {f : X ⟶ Y}
  statement: P.diagonal f ↔ P (pullback.diagonal f)
  proof: Iff.rfl

中文:
定理 diagonal_iff
  条件: {X Y : C} {f : X ⟶ Y}
  结论: P.diagonal f ↔ P (pullback.diagonal f)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f) :=
  Iff.rfl

/--
Instance `RespectsIso.diagonal` / 实例 `RespectsIso.diagonal`

English:
instance RespectsIso.diagonal
  signature: [P.RespectsIso]
  body: by
  apply RespectsIso.mk
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, P.cancel_left_of_respectsIso,
      P.cancel_left_of_respectsIso, ← P.cancel_right_of_respectsIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.conditi

中文:
实例 RespectsIso.diagonal
  签名: [P.RespectsIso]
  定义体: by
  apply RespectsIso.mk
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, P.cancel_left_of_respectsIso,
      P.cancel_left_of_respectsIso, ← P.cancel_right_of_respectsIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.conditi

Depends on / 依赖: P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso, RespectsIso, RespectsIso.mk, cancel_left_of_respectsIso, cancel_right_of_respectsIso, condition, diagonal, diagonal_comp, diagonal_iff, e.hom, introv, pullback, pullback.condition, pullback.diagonal_comp, pullback.map
-/
instance RespectsIso.diagonal [P.RespectsIso] : P.diagonal.RespectsIso := by
  apply RespectsIso.mk
  · introv H
    rwa [diagonal_iff, pullback.diagonal_comp, P.cancel_left_of_respectsIso,
      P.cancel_left_of_respectsIso, ← P.cancel_right_of_respectsIso _
        (pullback.map (e.hom ≫ f) (e.hom ≫ f) f f e.hom e.hom (𝟙 Z) (by simp) (by simp)),
      ← pullback.condition, P.cancel_left_of_respectsIso]
  · introv H
    delta diagonal
    rwa [pullback.diagonal_comp, P.cancel_right_of_respectsIso]

/--
Instance `diagonal_isStableUnderComposition` / 实例 `diagonal_isStableUnderComposition`

English:
instance diagonal_isStableUnderComposition
  signature: [P.IsStableUnderComposition] [RespectsIso P]
  body: by
    rw [diagonal_iff]; rw [pullback.diagonal_comp]
    exact P.comp_mem _ _ h₁
      (by simpa only [cancel_left_of_respectsIso] using P.pullback_snd _ _ h₂)

中文:
实例 diagonal_isStableUnderComposition
  签名: [P.是StableUnderComposition] [RespectsIso P]
  定义体: by
    rw [diagonal_iff]; rw [pullback.diagonal_comp]
    exact P.comp_mem _ _ h₁
      (by simpa only [cancel_left_of_respectsIso] using P.pullback_snd _ _ h₂)

Depends on / 依赖: P.comp_mem, P.pullback_snd, cancel_left_of_respectsIso, comp_mem, diagonal_comp, diagonal_iff, pullback, pullback.diagonal_comp, pullback_snd
-/
instance diagonal_isStableUnderComposition [P.IsStableUnderComposition] [RespectsIso P]
    [IsStableUnderBaseChange P] : P.diagonal.IsStableUnderComposition where
  comp_mem _ _ h₁ h₂ := by
    rw [diagonal_iff]; rw [pullback.diagonal_comp]
    exact P.comp_mem _ _ h₁
      (by simpa only [cancel_left_of_respectsIso] using P.pullback_snd _ _ h₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: [P.RespectsIso]
  body: P.of_isIso _

中文:
实例 [P.余ntainsIdentities]
  签名: [P.RespectsIso]
  定义体: P.of_isIso _

Depends on / 依赖: P.of_isIso, of_isIso
-/
instance [P.ContainsIdentities] [P.RespectsIso] : P.diagonal.ContainsIdentities where
  id_mem _ := P.of_isIso _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsMultiplicative]
  signature: [P.IsStableUnderBaseChange]

中文:
实例 [P.是Multiplicative]
  签名: [P.是StableUnderBaseChange]
-/
instance [P.IsMultiplicative] [P.IsStableUnderBaseChange] : P.diagonal.IsMultiplicative where

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsStableUnderBaseChange.diagonal` / 实例 `IsStableUnderBaseChange.diagonal`

English:
instance IsStableUnderBaseChange.diagonal
  signature: [IsStableUnderBaseChange P] [P.RespectsIso]
  body: IsStableUnderBaseChange.mk'
    (by
      introv h
      rw [diagonal_iff]; rw [diagonal_pullback_fst]; rw [P.cancel_left_of_respectsIso]; rw [P.cancel_right_of_respectsIso]
      exact P.overPullbackMap f _ (by simpa))

中文:
实例 是StableUnderBaseChange.diagonal
  签名: [是StableUnderBaseChange P] [P.RespectsIso]
  定义体: IsStableUnderBaseChange.mk'
    (by
      introv h
      rw [diagonal_iff]; rw [diagonal_pullback_fst]; rw [P.cancel_left_of_respectsIso]; rw [P.cancel_right_of_respectsIso]
      exact P.overPullbackMap f _ (by simpa))

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso, P.overPullbackMap, cancel_left_of_respectsIso, cancel_right_of_respectsIso, diagonal_iff, diagonal_pullback_fst, introv, overPullbackMap
-/
instance IsStableUnderBaseChange.diagonal [IsStableUnderBaseChange P] [P.RespectsIso] :
    P.diagonal.IsStableUnderBaseChange :=
  IsStableUnderBaseChange.mk'
    (by
      introv h
      rw [diagonal_iff]; rw [diagonal_pullback_fst]; rw [P.cancel_left_of_respectsIso]; rw [P.cancel_right_of_respectsIso]
      exact P.overPullbackMap f _ (by simpa))

/--
lemma `diagonal_isomorphisms` / 引理 `diagonal_isomorphisms`

English:
lemma diagonal_isomorphisms
  statement: (isomorphisms C).diagonal = monomorphisms C
  proof: ext _ _ fun _ _ _ => pullback.isIso_diagonal_iff _

中文:
引理 diagonal_isomorphisms
  结论: (isomorphisms C).diagonal = monomorphisms C
  证明: ext _ _ fun _ _ _ => pullback.isIso_diagonal_iff _

Depends on / 依赖: isIso_diagonal_iff, pullback, pullback.isIso_diagonal_iff
-/
lemma diagonal_isomorphisms : (isomorphisms C).diagonal = monomorphisms C :=
  ext _ _ fun _ _ _ => pullback.isIso_diagonal_iff _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasOfPostcompProperty_iff_le_diagonal` / 引理 `hasOfPostcompProperty_iff_le_diagonal`

English:
lemma hasOfPostcompProperty_iff_le_diagonal
  statement: [P.IsStableUnderBaseChange]
  proof: by
  refine ⟨fun hP X Y f hf => ?_, fun hP => ⟨fun {Y X S} g f hf hcomp => ?_⟩⟩
  · exact hP.of_postcomp _ _ (Q.pullback_fst _ _ hf) (by simpa using P.id_mem X)
  · set gr : Y ⟶ pullback (g ≫ f) f := pullback.lift (𝟙 Y) g (by simp)
    have : g = gr ≫ pullback.snd _ _ := by simp [gr]
    rw [this]
 

中文:
引理 hasOfPostcompProperty_iff_le_diagonal
  结论: [P.是StableUnderBaseChange]
  证明: by
  refine ⟨fun hP X Y f hf => ?_, fun hP => ⟨fun {Y X S} g f hf hcomp => ?_⟩⟩
  · exact hP.of_postcomp _ _ (Q.pullback_fst _ _ hf) (by simpa using P.id_mem X)
  · set gr : Y ⟶ pullback (g ≫ f) f := pullback.lift (𝟙 Y) g (by simp)
    have : g = gr ≫ pullback.snd _ _ := by simp [gr]
    rw [this]
 

Depends on / 依赖: P.comp_mem, P.id_mem, P.of_isPullback, P.pullback_snd, Q.pullback_fst, comp_mem, hP.of_postcomp, id_mem, of_isPullback, of_postcomp, pullback, pullback.lift, pullback.snd, pullback_fst, pullback_lift_diagonal_isPullback, pullback_snd
-/
lemma hasOfPostcompProperty_iff_le_diagonal [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] {Q : MorphismProperty C} [Q.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty Q ↔ Q <= P.diagonal := by
  refine ⟨fun hP X Y f hf => ?_, fun hP => ⟨fun {Y X S} g f hf hcomp => ?_⟩⟩
  · exact hP.of_postcomp _ _ (Q.pullback_fst _ _ hf) (by simpa using P.id_mem X)
  · set gr : Y ⟶ pullback (g ≫ f) f := pullback.lift (𝟙 Y) g (by simp)
    have : g = gr ≫ pullback.snd _ _ := by simp [gr]
    rw [this]
    apply P.comp_mem
    · exact P.of_isPullback (pullback_lift_diagonal_isPullback g f) (hP _ hf)
    · exact P.pullback_snd _ _ hcomp

end Diagonal

section Universally

/--
Definition of `universally` / `universally` 的定义

English:
definition universally
  signature: (P : MorphismProperty C)
  body: fun X Y f =>
  forall ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'

中文:
定义 universally
  签名: (P : MorphismProperty C)
  定义体: fun X Y f =>
  forall ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'
-/
def universally (P : MorphismProperty C) : MorphismProperty C := fun X Y f =>
  forall ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y') (_ : IsPullback f' i₁ i₂ f), P f'

/--
Instance `universally_respectsIso` / 实例 `universally_respectsIso`

English:
instance universally_respectsIso
  signature: (P : MorphismProperty C)
  body: by
  apply RespectsIso.mk
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    exact hf _ _ _
      (by simpa only [Iso.inv_hom_id_assoc, Cat

中文:
实例 universally_respectsIso
  签名: (P : MorphismProperty C)
  定义体: by
  apply RespectsIso.mk
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    exact hf _ _ _
      (by simpa only [Iso.inv_hom_id_assoc, Cat

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, IsPullback, IsPullback.of_horiz_isIso, Iso.hom_in, Iso.inv_hom_id_assoc, RespectsIso, RespectsIso.mk, comp_id, e.hom, e.hom_inv_id, e.inv, hom_in, hom_inv_id, id_comp, inv_hom_id_assoc, of_horiz_isIso, paste_horiz
-/
instance universally_respectsIso (P : MorphismProperty C) : P.universally.RespectsIso := by
  apply RespectsIso.mk
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv :=
      IsPullback.of_horiz_isIso
        ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    exact hf _ _ _
      (by simpa only [Iso.inv_hom_id_assoc, Category.id_comp] using this.paste_horiz H)
  · intro X Y Z e f hf X' Z' i₁ i₂ f' H
    have : IsPullback (𝟙 _) i₂ (i₂ ≫ e.inv) e.inv :=
      IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩
    exact hf _ _ _ (by simpa only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.comp_id] using H.paste_horiz this)

/--
Instance `universally_isStableUnderBaseChange` / 实例 `universally_isStableUnderBaseChange`

English:
instance universally_isStableUnderBaseChange
  signature: (P : MorphismProperty C)
  body: h₁ _ _ _ (H'.paste_vert H.flip)

中文:
实例 universally_isStableUnderBaseChange
  签名: (P : MorphismProperty C)
  定义体: h₁ _ _ _ (H'.paste_vert H.flip)

Depends on / 依赖: H.flip, paste_vert
-/
instance universally_isStableUnderBaseChange (P : MorphismProperty C) :
    P.universally.IsStableUnderBaseChange where
  of_isPullback H h₁ _ _ _ _ _ H' := h₁ _ _ _ (H'.paste_vert H.flip)

/--
Instance `IsStableUnderComposition.universally` / 实例 `IsStableUnderComposition.universally`

English:
instance IsStableUnderComposition.universally
  signature: [HasPullbacks C] (P : MorphismProperty C)
  body: by
    have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
    rw [← this] at H ⊢
    apply P.comp_mem _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
    exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))

中文:
实例 是StableUnderComposition.universally
  签名: [有Pullbacks C] (P : MorphismProperty C)
  定义体: by
    have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
    rw [← this] at H ⊢
    apply P.comp_mem _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
    exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))

Depends on / 依赖: Category, Category.assoc, H.of_right, H.w.trans, IsPullback, IsPullback.of_hasPullback, P.comp_mem, comp_mem, lift_fst, lift_snd, of_hasPullback, of_right, pullback, pullback.lift_fst, pullback.lift_snd
-/
instance IsStableUnderComposition.universally [HasPullbacks C] (P : MorphismProperty C)
    [hP : P.IsStableUnderComposition] : P.universally.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg X' Z' i₁ i₂ f' H := by
    have := pullback.lift_fst _ _ (H.w.trans (Category.assoc _ _ _).symm)
    rw [← this] at H ⊢
    apply P.comp_mem _ _ _ (hg _ _ _ <| IsPullback.of_hasPullback _ _)
    exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i₂ g))

/--
theorem `universally_le` / 定理 `universally_le`

English:
theorem universally_le
  given: (P : MorphismProperty C)
  statement: P.universally <= P
  proof: by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)

中文:
定理 universally_le
  条件: (P : MorphismProperty C)
  结论: P.universally <= P
  证明: by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, IsPullback, IsPullback.of_vert_isIso, comp_id, id_comp, of_vert_isIso
-/
theorem universally_le (P : MorphismProperty C) : P.universally <= P := by
  intro X Y f hf
  exact hf (𝟙 _) (𝟙 _) _ (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩)

/--
theorem `universally_inf` / 定理 `universally_inf`

English:
theorem universally_inf
  given: (P Q : MorphismProperty C)
  proof: by
  ext X Y f
  change _ ↔ _ ∧ _
  simp_rw [universally, ← forall_and]
  rfl

中文:
定理 universally_inf
  条件: (P Q : MorphismProperty C)
  证明: by
  ext X Y f
  change _ ↔ _ ∧ _
  simp_rw [universally, ← forall_and]
  rfl

Depends on / 依赖: forall_and, simp_rw, universally
-/
theorem universally_inf (P Q : MorphismProperty C) :
    (P ⊓ Q).universally = P.universally ⊓ Q.universally := by
  ext X Y f
  change _ ↔ _ ∧ _
  simp_rw [universally, ← forall_and]
  rfl

/--
theorem `universally_eq_iff` / 定理 `universally_eq_iff`

English:
theorem universally_eq_iff
  given: {P : MorphismProperty C}
  proof: ⟨(· ▸ P.universally_isStableUnderBaseChange),
    fun hP => P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP.of_isPullback H.flip hf⟩

中文:
定理 universally_eq_iff
  条件: {P : MorphismProperty C}
  证明: ⟨(· ▸ P.universally_isStableUnderBaseChange),
    fun hP => P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP.of_isPullback H.flip hf⟩

Depends on / 依赖: H.flip, P.universally_isStableUnderBaseChange, P.universally_le.antisymm, antisymm, hP.of_isPullback, of_isPullback, universally_isStableUnderBaseChange, universally_le
-/
theorem universally_eq_iff {P : MorphismProperty C} :
    P.universally = P ↔ P.IsStableUnderBaseChange :=
  ⟨(· ▸ P.universally_isStableUnderBaseChange),
    fun hP => P.universally_le.antisymm fun _ _ _ hf _ _ _ _ _ H => hP.of_isPullback H.flip hf⟩

/--
theorem `IsStableUnderBaseChange.universally_eq` / 定理 `IsStableUnderBaseChange.universally_eq`

English:
theorem IsStableUnderBaseChange.universally_eq
  statement: {P : MorphismProperty C}
  proof: universally_eq_iff.mpr hP

中文:
定理 是StableUnderBaseChange.universally_eq
  结论: {P : MorphismProperty C}
  证明: universally_eq_iff.mpr hP

Depends on / 依赖: universally_eq_iff, universally_eq_iff.mpr
-/
theorem IsStableUnderBaseChange.universally_eq {P : MorphismProperty C}
    [hP : P.IsStableUnderBaseChange] : P.universally = P := universally_eq_iff.mpr hP

/--
theorem `universally_mono` / 定理 `universally_mono`

English:
theorem universally_mono
  statement: Monotone (universally : MorphismProperty C -> MorphismProperty C)
  proof: fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ (h₁ _ _ _ H)

中文:
定理 universally_mono
  结论: 递增 (universally : MorphismProperty C -> MorphismProperty C)
  证明: fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ (h₁ _ _ _ H)
-/
theorem universally_mono : Monotone (universally : MorphismProperty C -> MorphismProperty C) :=
  fun _ _ h _ _ _ h₁ _ _ _ _ _ H => h _ (h₁ _ _ _ H)

/--
lemma `universally_mk'` / 引理 `universally_mk'`

English:
lemma universally_mk'
  statement: (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y)
  proof: by
  introv X' h
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]; rw [P.cancel_left_of_respectsIso]
  exact H ..

中文:
引理 universally_mk'
  结论: (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y)
  证明: by
  introv X' h
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]; rw [P.cancel_left_of_respectsIso]
  exact H ..

Depends on / 依赖: P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, h.hasPullback, h.isoPullback_hom_fst, hasPullback, introv, isoPullback_hom_fst
-/
lemma universally_mk' (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y)
    (H : forall {T : C} (f : T ⟶ Y) [HasPullback f g], P (pullback.fst f g)) :
    universally P g := by
  introv X' h
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]; rw [P.cancel_left_of_respectsIso]
  exact H ..

end Universally

variable (P : MorphismProperty C)

/--
Definition of `HasPullbacks` / `HasPullbacks` 的定义

English:
class HasPullbacks
  parameters: : Prop where
  axioms and operations (1):
    - hasPullback({X Y S : C} {f : X ⟶ S} (g : Y ⟶ S)) : P f -> HasPullback f g  [default: by infer_instance]

中文:
类 有Pullbacks
  参数: : 命题 where
  公理与运算 (1 个):
    - hasPullback({X Y S : C} {f : X ⟶ S} (g : Y ⟶ S)) : P f -> HasPullback f g  [默认: by infer_instance]
-/
protected class HasPullbacks : Prop where
  hasPullback {X Y S : C} {f : X ⟶ S} (g : Y ⟶ S) : P f -> HasPullback f g := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullbacks
  signature: C] : P.HasPullbacks where
  body: HasPullbacks.hasPullback

中文:
实例 [有Pullbacks
  签名: C] : P.有Pullbacks where
  定义体: HasPullbacks.hasPullback

Depends on / 依赖: HasPullbacks, HasPullbacks.hasPullback, hasPullback
-/
instance [HasPullbacks C] : P.HasPullbacks where

alias hasPullback := HasPullbacks.hasPullback

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.HasPullbacks]
  signature: {X Y : C} {f : X ⟶ Y}
  body: hasPullback _

中文:
实例 [P.有Pullbacks]
  签名: {X Y : C} {f : X ⟶ Y}
  定义体: hasPullback _

Depends on / 依赖: hasPullback
-/
instance [P.HasPullbacks] {X Y : C} {f : X ⟶ Y} : P.HasPullbacksAlong f where
  hasPullback _ := hasPullback _

/--
Definition of `HasPushouts` / `HasPushouts` 的定义

English:
class HasPushouts
  parameters: : Prop where
  axioms and operations (1):
    - hasPushout({X Y S : C} {f : S ⟶ X} (g : S ⟶ Y)) : P f -> HasPushout f g  [default: by infer_instance]

中文:
类 有Pushouts
  参数: : 命题 where
  公理与运算 (1 个):
    - hasPushout({X Y S : C} {f : S ⟶ X} (g : S ⟶ Y)) : P f -> HasPushout f g  [默认: by infer_instance]
-/
protected class HasPushouts : Prop where
  hasPushout {X Y S : C} {f : S ⟶ X} (g : S ⟶ Y) : P f -> HasPushout f g := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPushouts
  signature: C] : P.HasPushouts where
  body: HasPushouts.hasPushout

中文:
实例 [有Pushouts
  签名: C] : P.有Pushouts where
  定义体: HasPushouts.hasPushout

Depends on / 依赖: HasPushouts, HasPushouts.hasPushout, hasPushout
-/
instance [HasPushouts C] : P.HasPushouts where

alias hasPushout := HasPushouts.hasPushout

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.HasPushouts]
  signature: {X Y : C} {f : X ⟶ Y}
  body: hasPushout _

中文:
实例 [P.有Pushouts]
  签名: {X Y : C} {f : X ⟶ Y}
  定义体: hasPushout _

Depends on / 依赖: hasPushout
-/
instance [P.HasPushouts] {X Y : C} {f : X ⟶ Y} : P.HasPushoutsAlong f where
  hasPushout _ := hasPushout _

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] : P.HasPullbacksAlong (f ≫ g) where
  hasPullback h p :=
    have : HasPullback h g := HasPullbacksAlong.hasPullback h p
    have : HasPullback (pullback.snd h g) f := HasPullbacksAlong.hasPullback (pullback.snd h g)
      (P.pullback_snd h g p)
    IsPullback.hasPullback (IsPullback.paste_horiz (IsPullback.of_hasPullback
      (pullback.snd h g) f) (IsPullback.of_hasPullback h g))

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong g] :
    P.IsStableUnderBaseChangeAlong (f ≫ g) where
  of_isPullback {_ _ _ _ p} pb hp :=
    have : HasPullback p g := HasPullbacksAlong.hasPullback p hp
    have right := IsPullback.of_hasPullback p g
    IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_right' pb right)
      (IsStableUnderBaseChangeAlong.of_isPullback right hp)

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderCobaseChangeAlong f]
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] : P.HasPushoutsAlong (f ≫ g) where
  hasPushout h p :=
    have : HasPushout h f := HasPushoutsAlong.hasPushout h p
    have : HasPushout (pushout.inr h f) g := HasPushoutsAlong.hasPushout _
      (P.pushout_inr _ _ p)
    IsPushout.hasPushout (IsPushout.paste_vert (.of_hasPushout _ _) (.of_hasPushout _ _))

instance {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderCobaseChangeAlong f]
    [P.IsStableUnderCobaseChangeAlong g] [P.HasPushoutsAlong f] :
    P.IsStableUnderCobaseChangeAlong (f ≫ g) where
  of_isPushout {_ _ _ _ p} pb hp :=
    have : HasPushout p f := HasPushoutsAlong.hasPushout p hp
    have right := IsPushout.of_hasPushout p f
    IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_left' pb right.flip)
      (IsStableUnderCobaseChangeAlong.of_isPushout right.flip hp)

/--
Definition of `IsStableUnderBaseChangeAgainst` / `IsStableUnderBaseChangeAgainst` 的定义

English:
class IsStableUnderBaseChangeAgainst
  axioms and operations (1):
    - isStableUnderBaseChangeAlong(⦃X Y) : C⦄ (f : X ⟶ Y) (hf : P' f) : P.IsStableUnderBaseChangeAlong f

中文:
类 是StableUnderBaseChangeAgainst
  公理与运算 (1 个):
    - isStableUnderBaseChangeAlong(⦃X Y) : C⦄ (f : X ⟶ Y) (hf : P' f) : P.是StableUnderBaseChangeAlong f
-/
class IsStableUnderBaseChangeAgainst
    (P P' : MorphismProperty C) : Prop where
  isStableUnderBaseChangeAlong ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P' f) :
    P.IsStableUnderBaseChangeAlong f

instance (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    (P' : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst P' where
  isStableUnderBaseChangeAlong := inferInstance

/--
lemma `isStableUnderBaseChangeAgainst_top_iff` / 引理 `isStableUnderBaseChangeAgainst_top_iff`

English:
lemma isStableUnderBaseChangeAgainst_top_iff
  proof: ⟨fun {_ _ _ _} _ _ _ _ h' h'' =>
      (h.isStableUnderBaseChangeAlong _ (by tauto)).of_isPullback h' h''⟩
  mpr _ := inferInstance

中文:
引理 isStableUnderBaseChangeAgainst_top_iff
  证明: ⟨fun {_ _ _ _} _ _ _ _ h' h'' =>
      (h.isStableUnderBaseChangeAlong _ (by tauto)).of_isPullback h' h''⟩
  mpr _ := inferInstance

Depends on / 依赖: h.isStableUnderBaseChangeAlong, isStableUnderBaseChangeAlong, of_isPullback
-/
lemma isStableUnderBaseChangeAgainst_top_iff
    (P : MorphismProperty C) :
    P.IsStableUnderBaseChangeAgainst ⊤ ↔ P.IsStableUnderBaseChange where
  mp h :=
    ⟨fun {_ _ _ _} _ _ _ _ h' h'' =>
      (h.isStableUnderBaseChangeAlong _ (by tauto)).of_isPullback h' h''⟩
  mpr _ := inferInstance

/--
Definition of `HasPullbacksAgainst` / `HasPullbacksAgainst` 的定义

English:
class HasPullbacksAgainst
  axioms and operations (1):
    - hasPullbacksAlong(⦃X Y) : C ⦄ (f : X ⟶ Y) (hf : P' f) : P.HasPullbacksAlong f

中文:
类 有PullbacksAgainst
  公理与运算 (1 个):
    - hasPullbacksAlong(⦃X Y) : C ⦄ (f : X ⟶ Y) (hf : P' f) : P.有PullbacksAlong f
-/
class HasPullbacksAgainst
    (P P' : MorphismProperty C) : Prop where
  hasPullbacksAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.HasPullbacksAlong f

instance (P : MorphismProperty C) [P.HasPullbacks] (P' : MorphismProperty C) :
    P.HasPullbacksAgainst P' where
  hasPullbacksAlong := inferInstance

/--
lemma `hasPullbacksAgainst_top_iff` / 引理 `hasPullbacksAgainst_top_iff`

English:
lemma hasPullbacksAgainst_top_iff
  proof: ⟨fun _ h' =>
      (h.hasPullbacksAlong _ (by tauto)).hasPullback _ h'⟩
  mpr _ := inferInstance

中文:
引理 hasPullbacksAgainst_top_iff
  证明: ⟨fun _ h' =>
      (h.hasPullbacksAlong _ (by tauto)).hasPullback _ h'⟩
  mpr _ := inferInstance

Depends on / 依赖: h.hasPullbacksAlong, hasPullback, hasPullbacksAlong
-/
lemma hasPullbacksAgainst_top_iff
    (P : MorphismProperty C) :
    P.HasPullbacksAgainst ⊤ ↔ P.HasPullbacks where
  mp h :=
    ⟨fun _ h' =>
      (h.hasPullbacksAlong _ (by tauto)).hasPullback _ h'⟩
  mpr _ := inferInstance

/--
lemma `_root_.CategoryTheory.Limits.hasPullback_ofHasPullbacksAgainst` / 引理 `_root_.CategoryTheory.Limits.hasPullback_ofHasPullbacksAgainst`

English:
lemma _root_.CategoryTheory.Limits.hasPullback_ofHasPullbacksAgainst
  proof: letI : P.HasPullbacksAlong g :=
    MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong g hg
  MorphismProperty.HasPullbacksAlong.hasPullback f hf

中文:
引理 _root_.范畴论.Limits.hasPullback_ofHasPullbacksAgainst
  证明: letI : P.HasPullbacksAlong g :=
    MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong g hg
  MorphismProperty.HasPullbacksAlong.hasPullback f hf

Depends on / 依赖: HasPullbacksAgainst, HasPullbacksAlong, MorphismProperty, MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong, MorphismProperty.HasPullbacksAlong.hasPullback, P.HasPullbacksAlong, hasPullback, hasPullbacksAlong
-/
lemma _root_.CategoryTheory.Limits.hasPullback_ofHasPullbacksAgainst
    {P : MorphismProperty C} {P' : MorphismProperty C} {c c' c'' : C}
    {f : c ⟶ c'} {g : c'' ⟶ c'} [P.HasPullbacksAgainst P'] (hf : P f) (hg : P' g) :
    Limits.HasPullback f g :=
  letI : P.HasPullbacksAlong g :=
    MorphismProperty.HasPullbacksAgainst.hasPullbacksAlong g hg
  MorphismProperty.HasPullbacksAlong.hasPullback f hf

/--
Definition of `IsStableUnderCobaseChangeAgainst` / `IsStableUnderCobaseChangeAgainst` 的定义

English:
class IsStableUnderCobaseChangeAgainst
  axioms and operations (1):
    - isStableUnderCobaseChangeAlong(⦃X Y) : C ⦄ (f : X ⟶ Y) (hf : P' f) : P.IsStableUnderCobaseChangeAlong f

中文:
类 是StableUnderCobaseChangeAgainst
  公理与运算 (1 个):
    - isStableUnderCobaseChangeAlong(⦃X Y) : C ⦄ (f : X ⟶ Y) (hf : P' f) : P.是StableUnderCobaseChangeAlong f

Depends on / 依赖: P.ext_of_isTriangulatedClosed, P.prop_of_iso, prop_of_iso
-/
class IsStableUnderCobaseChangeAgainst
    (P P' : MorphismProperty C) : Prop where
  isStableUnderCobaseChangeAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.IsStableUnderCobaseChangeAlong f

instance (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (P' : MorphismProperty C) :
    P.IsStableUnderCobaseChangeAgainst P' where
  isStableUnderCobaseChangeAlong := inferInstance

/--
lemma `isStableUnderCobaseChangeAgainst_top_iff` / 引理 `isStableUnderCobaseChangeAgainst_top_iff`

English:
lemma isStableUnderCobaseChangeAgainst_top_iff
  proof: ⟨fun {_ _ _ _} _ _ _ _ h' h'' =>
      (h.isStableUnderCobaseChangeAlong _ (by tauto)).of_isPushout h' h''⟩
  mpr _ := inferInstance

中文:
引理 isStableUnderCobaseChangeAgainst_top_iff
  证明: ⟨fun {_ _ _ _} _ _ _ _ h' h'' =>
      (h.isStableUnderCobaseChangeAlong _ (by tauto)).of_isPushout h' h''⟩
  mpr _ := inferInstance

Depends on / 依赖: h.isStableUnderCobaseChangeAlong, isStableUnderCobaseChangeAlong, of_isPushout
-/
lemma isStableUnderCobaseChangeAgainst_top_iff
    (P : MorphismProperty C) :
    P.IsStableUnderCobaseChangeAgainst ⊤ ↔ P.IsStableUnderCobaseChange where
  mp h :=
    ⟨fun {_ _ _ _} _ _ _ _ h' h'' =>
      (h.isStableUnderCobaseChangeAlong _ (by tauto)).of_isPushout h' h''⟩
  mpr _ := inferInstance

/--
Definition of `HasPushoutsAgainst` / `HasPushoutsAgainst` 的定义

English:
class HasPushoutsAgainst
  axioms and operations (1):
    - hasPushoutsAlong(⦃X Y) : C ⦄ (f : X ⟶ Y) (hf : P' f) : P.HasPushoutsAlong f

中文:
类 有PushoutsAgainst
  公理与运算 (1 个):
    - hasPushoutsAlong(⦃X Y) : C ⦄ (f : X ⟶ Y) (hf : P' f) : P.有PushoutsAlong f
-/
class HasPushoutsAgainst
    (P P' : MorphismProperty C) : Prop where
  hasPushoutsAlong ⦃X Y : C ⦄ (f : X ⟶ Y) (hf : P' f) :
    P.HasPushoutsAlong f

instance (P : MorphismProperty C) [P.HasPushouts] (P' : MorphismProperty C) :
    P.HasPushoutsAgainst P' where
  hasPushoutsAlong := inferInstance

/--
lemma `hasPushoutsAgainst_top_iff` / 引理 `hasPushoutsAgainst_top_iff`

English:
lemma hasPushoutsAgainst_top_iff
  proof: ⟨fun _ h' =>
      (h.hasPushoutsAlong _ (by tauto)).hasPushout _ h'⟩
  mpr _ := inferInstance

中文:
引理 hasPushoutsAgainst_top_iff
  证明: ⟨fun _ h' =>
      (h.hasPushoutsAlong _ (by tauto)).hasPushout _ h'⟩
  mpr _ := inferInstance

Depends on / 依赖: h.hasPushoutsAlong, hasPushout, hasPushoutsAlong
-/
lemma hasPushoutsAgainst_top_iff
    (P : MorphismProperty C) :
    P.HasPushoutsAgainst ⊤ ↔ P.HasPushouts where
  mp h :=
    ⟨fun _ h' =>
      (h.hasPushoutsAlong _ (by tauto)).hasPushout _ h'⟩
  mpr _ := inferInstance

/--
lemma `_root_.CategoryTheory.Limits.hasPushout_ofHasPushoutsAgainst` / 引理 `_root_.CategoryTheory.Limits.hasPushout_ofHasPushoutsAgainst`

English:
lemma _root_.CategoryTheory.Limits.hasPushout_ofHasPushoutsAgainst
  proof: letI : P.HasPushoutsAlong g :=
    MorphismProperty.HasPushoutsAgainst.hasPushoutsAlong g hg
  MorphismProperty.HasPushoutsAlong.hasPushout f hf

中文:
引理 _root_.范畴论.Limits.hasPushout_ofHasPushoutsAgainst
  证明: letI : P.HasPushoutsAlong g :=
    MorphismProperty.HasPushoutsAgainst.hasPushoutsAlong g hg
  MorphismProperty.HasPushoutsAlong.hasPushout f hf

Depends on / 依赖: HasPushoutsAgainst, HasPushoutsAlong, MorphismProperty, MorphismProperty.HasPushoutsAgainst.hasPushoutsAlong, MorphismProperty.HasPushoutsAlong.hasPushout, P.HasPushoutsAlong, hasPushout, hasPushoutsAlong
-/
lemma _root_.CategoryTheory.Limits.hasPushout_ofHasPushoutsAgainst
    {P : MorphismProperty C} {P' : MorphismProperty C} {c c' c'' : C}
    {f : c ⟶ c'} {g : c ⟶ c''} [P.HasPushoutsAgainst P'] (hf : P f) (hg : P' g) :
    Limits.HasPushout f g :=
  letI : P.HasPushoutsAlong g :=
    MorphismProperty.HasPushoutsAgainst.hasPushoutsAlong g hg
  MorphismProperty.HasPushoutsAlong.hasPushout f hf

end MorphismProperty

end CategoryTheory
