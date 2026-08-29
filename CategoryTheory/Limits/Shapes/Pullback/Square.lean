/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Square

/-!
# Commutative squares that are pushout or pullback squares

In this file, we translate the `IsPushout` and `IsPullback`
API for the objects of the category `Square C` of commutative
squares in a category `C`. We also obtain lemmas which state
in this language that a pullback of a monomorphism is
a monomorphism (and similarly for pushouts of epimorphisms).

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Square

variable (sq : Square C)

/--
Definition of `pullbackCone` / `pullbackCone` 的定义

English:
abbreviation pullbackCone
  signature: : PullbackCone sq.f₂₄ sq.f₃₄
  body: PullbackCone.mk sq.f₁₂ sq.f₁₃ sq.fac

中文:
缩写 pullbackCone
  签名: : PullbackCone sq.f₂₄ sq.f₃₄
  定义体: PullbackCone.mk sq.f₁₂ sq.f₁₃ sq.fac

Depends on / 依赖: PullbackCone, PullbackCone.mk, sq.f, sq.fac
-/
abbrev pullbackCone : PullbackCone sq.f₂₄ sq.f₃₄ :=
  PullbackCone.mk sq.f₁₂ sq.f₁₃ sq.fac

/--
Definition of `pushoutCocone` / `pushoutCocone` 的定义

English:
abbreviation pushoutCocone
  signature: : PushoutCocone sq.f₁₂ sq.f₁₃
  body: PushoutCocone.mk sq.f₂₄ sq.f₃₄ sq.fac

中文:
缩写 pushoutCocone
  签名: : PushoutCocone sq.f₁₂ sq.f₁₃
  定义体: PushoutCocone.mk sq.f₂₄ sq.f₃₄ sq.fac

Depends on / 依赖: ContainsZero, Nonempty, P.ContainsZero, P.Nonempty, PushoutCocone, PushoutCocone.mk, sq.f, sq.fac
-/
abbrev pushoutCocone : PushoutCocone sq.f₁₂ sq.f₁₃ :=
  PushoutCocone.mk sq.f₂₄ sq.f₃₄ sq.fac

/--
Definition of `IsPullback` / `IsPullback` 的定义

English:
definition IsPullback
  signature: : Prop
  body: IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

中文:
定义 IsPullback
  签名: : 命题
  定义体: IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄
-/
protected def IsPullback : Prop :=
  IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

/--
Definition of `IsPushout` / `IsPushout` 的定义

English:
definition IsPushout
  signature: : Prop
  body: IsPushout sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

中文:
定义 IsPushout
  签名: : 命题
  定义体: IsPushout sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄
-/
protected def IsPushout : Prop :=
  IsPushout sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

/--
lemma `isPullback_iff` / 引理 `isPullback_iff`

English:
lemma isPullback_iff
  proof: ⟨fun h => ⟨h.isLimit⟩, fun h => { w := sq.fac, isLimit' := h }⟩

中文:
引理 isPullback_iff
  证明: ⟨fun h => ⟨h.isLimit⟩, fun h => { w := sq.fac, isLimit' := h }⟩

Depends on / 依赖: h.isLimit, isLimit, sq.fac
-/
lemma isPullback_iff :
    sq.IsPullback ↔ Nonempty (IsLimit sq.pullbackCone) :=
  ⟨fun h => ⟨h.isLimit⟩, fun h => { w := sq.fac, isLimit' := h }⟩

/--
lemma `isPushout_iff` / 引理 `isPushout_iff`

English:
lemma isPushout_iff
  proof: ⟨fun h => ⟨h.isColimit⟩, fun h => { w := sq.fac, isColimit' := h }⟩

中文:
引理 isPushout_iff
  证明: ⟨fun h => ⟨h.isColimit⟩, fun h => { w := sq.fac, isColimit' := h }⟩

Depends on / 依赖: h.isColimit, isColimit, sq.fac
-/
lemma isPushout_iff :
    sq.IsPushout ↔ Nonempty (IsColimit sq.pushoutCocone) :=
  ⟨fun h => ⟨h.isColimit⟩, fun h => { w := sq.fac, isColimit' := h }⟩

/--
lemma `IsPullback.mk` / 引理 `IsPullback.mk`

English:
lemma IsPullback.mk
  given: (h : IsLimit sq.pullbackCone)
  statement: sq.IsPullback
  proof: sq.isPullback_iff.2 ⟨h⟩

中文:
引理 IsPullback.mk
  条件: (h : IsLimit sq.pullbackCone)
  结论: sq.IsPullback
  证明: sq.isPullback_iff.2 ⟨h⟩

Depends on / 依赖: isPullback_iff, sq.isPullback_iff
-/
lemma IsPullback.mk (h : IsLimit sq.pullbackCone) : sq.IsPullback :=
  sq.isPullback_iff.2 ⟨h⟩

/--
lemma `IsPushout.mk` / 引理 `IsPushout.mk`

English:
lemma IsPushout.mk
  given: (h : IsColimit sq.pushoutCocone)
  statement: sq.IsPushout
  proof: sq.isPushout_iff.2 ⟨h⟩

中文:
引理 IsPushout.mk
  条件: (h : IsColimit sq.pushoutCocone)
  结论: sq.IsPushout
  证明: sq.isPushout_iff.2 ⟨h⟩

Depends on / 依赖: isPushout_iff, sq.isPushout_iff
-/
lemma IsPushout.mk (h : IsColimit sq.pushoutCocone) : sq.IsPushout :=
  sq.isPushout_iff.2 ⟨h⟩

variable {sq}

/--
Definition of `IsPullback.isLimit` / `IsPullback.isLimit` 的定义

English:
definition IsPullback.isLimit
  signature: (h : sq.IsPullback)
  body: CategoryTheory.IsPullback.isLimit h

中文:
定义 IsPullback.isLimit
  签名: (h : sq.IsPullback)
  定义体: CategoryTheory.IsPullback.isLimit h

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.isLimit, IsPullback, isLimit
-/
noncomputable def IsPullback.isLimit (h : sq.IsPullback) :
    IsLimit sq.pullbackCone :=
  CategoryTheory.IsPullback.isLimit h

/--
Definition of `IsPushout.isColimit` / `IsPushout.isColimit` 的定义

English:
definition IsPushout.isColimit
  signature: (h : sq.IsPushout)
  body: CategoryTheory.IsPushout.isColimit h

中文:
定义 IsPushout.isColimit
  签名: (h : sq.IsPushout)
  定义体: CategoryTheory.IsPushout.isColimit h

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPushout.isColimit, IsPushout, isColimit
-/
noncomputable def IsPushout.isColimit (h : sq.IsPushout) :
    IsColimit sq.pushoutCocone :=
  CategoryTheory.IsPushout.isColimit h

/--
lemma `IsPullback.of_iso` / 引理 `IsPullback.of_iso`

English:
lemma IsPullback.of_iso
  statement: {sq₁ sq₂ : Square C} (h : sq₁.IsPullback)
  proof: by
  refine CategoryTheory.IsPullback.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp

中文:
引理 IsPullback.of_iso
  结论: {sq₁ sq₂ : Square C} (h : sq₁.IsPullback)
  证明: by
  refine CategoryTheory.IsPullback.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.of_iso, IsPullback, all_goals, mapIso, of_iso
-/
lemma IsPullback.of_iso {sq₁ sq₂ : Square C} (h : sq₁.IsPullback)
    (e : sq₁ ≅ sq₂) : sq₂.IsPullback := by
  refine CategoryTheory.IsPullback.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp

/--
lemma `IsPullback.iff_of_iso` / 引理 `IsPullback.iff_of_iso`

English:
lemma IsPullback.iff_of_iso
  given: {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂)
  proof: ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

中文:
引理 IsPullback.iff_of_iso
  条件: {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂)
  证明: ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

Depends on / 依赖: P.exists_prop_of_containsZero, Z.unop, e.symm, exists_prop_of_containsZero, h.of_iso, hZ.unop, of_iso
-/
lemma IsPullback.iff_of_iso {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂) :
    sq₁.IsPullback ↔ sq₂.IsPullback :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/--
lemma `IsPushout.of_iso` / 引理 `IsPushout.of_iso`

English:
lemma IsPushout.of_iso
  statement: {sq₁ sq₂ : Square C} (h : sq₁.IsPushout)
  proof: by
  refine CategoryTheory.IsPushout.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp

中文:
引理 IsPushout.of_iso
  结论: {sq₁ sq₂ : Square C} (h : sq₁.IsPushout)
  证明: by
  refine CategoryTheory.IsPushout.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPushout.of_iso, IsPushout, all_goals, mapIso, of_iso
-/
lemma IsPushout.of_iso {sq₁ sq₂ : Square C} (h : sq₁.IsPushout)
    (e : sq₁ ≅ sq₂) : sq₂.IsPushout := by
  refine CategoryTheory.IsPushout.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals simp

/--
lemma `IsPushout.iff_of_iso` / 引理 `IsPushout.iff_of_iso`

English:
lemma IsPushout.iff_of_iso
  given: {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂)
  proof: ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

中文:
引理 IsPushout.iff_of_iso
  条件: {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂)
  证明: ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

Depends on / 依赖: e.symm, h.of_iso, of_iso
-/
lemma IsPushout.iff_of_iso {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂) :
    sq₁.IsPushout ↔ sq₂.IsPushout :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/--
lemma `IsPushout.op` / 引理 `IsPushout.op`

English:
lemma IsPushout.op
  given: {sq : Square C} (h : sq.IsPushout)
  statement: sq.op.IsPullback
  proof: CategoryTheory.IsPushout.op h.flip

中文:
引理 IsPushout.op
  条件: {sq : Square C} (h : sq.IsPushout)
  结论: sq.op.IsPullback
  证明: CategoryTheory.IsPushout.op h.flip

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPushout.op, IsPushout, h.flip
-/
lemma IsPushout.op {sq : Square C} (h : sq.IsPushout) : sq.op.IsPullback :=
  CategoryTheory.IsPushout.op h.flip

/--
lemma `IsPushout.unop` / 引理 `IsPushout.unop`

English:
lemma IsPushout.unop
  given: {sq : Square Cᵒᵖ} (h : sq.IsPushout)
  statement: sq.unop.IsPullback
  proof: CategoryTheory.IsPushout.unop h.flip

中文:
引理 IsPushout.unop
  条件: {sq : Square Cᵒᵖ} (h : sq.IsPushout)
  结论: sq.unop.IsPullback
  证明: CategoryTheory.IsPushout.unop h.flip

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPushout.unop, IsPushout, h.flip
-/
lemma IsPushout.unop {sq : Square Cᵒᵖ} (h : sq.IsPushout) : sq.unop.IsPullback :=
  CategoryTheory.IsPushout.unop h.flip

/--
lemma `IsPullback.op` / 引理 `IsPullback.op`

English:
lemma IsPullback.op
  given: {sq : Square C} (h : sq.IsPullback)
  statement: sq.op.IsPushout
  proof: CategoryTheory.IsPullback.op h.flip

中文:
引理 IsPullback.op
  条件: {sq : Square C} (h : sq.IsPullback)
  结论: sq.op.IsPushout
  证明: CategoryTheory.IsPullback.op h.flip

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.op, IsPullback, h.flip
-/
lemma IsPullback.op {sq : Square C} (h : sq.IsPullback) : sq.op.IsPushout :=
  CategoryTheory.IsPullback.op h.flip

/--
lemma `IsPullback.unop` / 引理 `IsPullback.unop`

English:
lemma IsPullback.unop
  given: {sq : Square Cᵒᵖ} (h : sq.IsPullback)
  statement: sq.unop.IsPushout
  proof: CategoryTheory.IsPullback.unop h.flip

中文:
引理 IsPullback.unop
  条件: {sq : Square Cᵒᵖ} (h : sq.IsPullback)
  结论: sq.unop.IsPushout
  证明: CategoryTheory.IsPullback.unop h.flip

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.unop, IsPullback, h.flip
-/
lemma IsPullback.unop {sq : Square Cᵒᵖ} (h : sq.IsPullback) : sq.unop.IsPushout :=
  CategoryTheory.IsPullback.unop h.flip

namespace IsPullback

variable (h : sq.IsPullback)

include h

/--
lemma `flip` / 引理 `flip`

English:
lemma flip
  statement: sq.flip.IsPullback
  proof: CategoryTheory.IsPullback.flip h

中文:
引理 flip
  结论: sq.flip.IsPullback
  证明: CategoryTheory.IsPullback.flip h

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.flip, F.map, IsPullback, P.prop_of_mono, prop_of_mono
-/
lemma flip : sq.flip.IsPullback := CategoryTheory.IsPullback.flip h

/--
lemma `mono_f₁₃` / 引理 `mono_f₁₃`

English:
lemma mono_f₁₃
  given: [Mono sq.f₂₄]
  statement: Mono sq.f₁₃
  proof: (MorphismProperty.monomorphisms C).of_isPullback h (by assumption)

中文:
引理 mono_f₁₃
  条件: [Mono sq.f₂₄]
  结论: Mono sq.f₁₃
  证明: (MorphismProperty.monomorphisms C).of_isPullback h (by assumption)

Depends on / 依赖: MorphismProperty, MorphismProperty.monomorphisms, monomorphisms, of_isPullback
-/
lemma mono_f₁₃ [Mono sq.f₂₄] : Mono sq.f₁₃ :=
  (MorphismProperty.monomorphisms C).of_isPullback h (by assumption)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mono_f₁₂` / 引理 `mono_f₁₂`

English:
lemma mono_f₁₂
  given: [Mono sq.f₃₄]
  statement: Mono sq.f₁₂
  proof: by
  have : Mono sq.flip.f₂₄ := by dsimp; infer_instance
  exact h.flip.mono_f₁₃

中文:
引理 mono_f₁₂
  条件: [Mono sq.f₃₄]
  结论: Mono sq.f₁₂
  证明: by
  have : Mono sq.flip.f₂₄ := by dsimp; infer_instance
  exact h.flip.mono_f₁₃

Depends on / 依赖: h.flip.mono_f, infer_instance, sq.flip.f
-/
lemma mono_f₁₂ [Mono sq.f₃₄] : Mono sq.f₁₂ := by
  have : Mono sq.flip.f₂₄ := by dsimp; infer_instance
  exact h.flip.mono_f₁₃

end IsPullback

namespace IsPushout

variable (h : sq.IsPushout)

include h

/--
lemma `flip` / 引理 `flip`

English:
lemma flip
  statement: sq.flip.IsPushout
  proof: CategoryTheory.IsPushout.flip h

中文:
引理 flip
  结论: sq.flip.IsPushout
  证明: CategoryTheory.IsPushout.flip h

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPushout.flip, IsPushout
-/
lemma flip : sq.flip.IsPushout := CategoryTheory.IsPushout.flip h

/--
lemma `epi_f₂₄` / 引理 `epi_f₂₄`

English:
lemma epi_f₂₄
  given: [Epi sq.f₁₃]
  statement: Epi sq.f₂₄
  proof: (MorphismProperty.epimorphisms C).of_isPushout h (by assumption)

中文:
引理 epi_f₂₄
  条件: [Epi sq.f₁₃]
  结论: Epi sq.f₂₄
  证明: (MorphismProperty.epimorphisms C).of_isPushout h (by assumption)

Depends on / 依赖: F.map, MorphismProperty, MorphismProperty.epimorphisms, P.prop_of_epi, epimorphisms, of_isPushout, prop_of_epi
-/
lemma epi_f₂₄ [Epi sq.f₁₃] : Epi sq.f₂₄ :=
  (MorphismProperty.epimorphisms C).of_isPushout h (by assumption)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `epi_f₃₄` / 引理 `epi_f₃₄`

English:
lemma epi_f₃₄
  given: [Epi sq.f₁₂]
  statement: Epi sq.f₃₄
  proof: by
  have : Epi sq.flip.f₁₃ := by dsimp; infer_instance
  exact h.flip.epi_f₂₄

中文:
引理 epi_f₃₄
  条件: [Epi sq.f₁₂]
  结论: Epi sq.f₃₄
  证明: by
  have : Epi sq.flip.f₁₃ := by dsimp; infer_instance
  exact h.flip.epi_f₂₄

Depends on / 依赖: h.flip.epi_f, infer_instance, sq.flip.f
-/
lemma epi_f₃₄ [Epi sq.f₁₂] : Epi sq.f₃₄ := by
  have : Epi sq.flip.f₁₃ := by dsimp; infer_instance
  exact h.flip.epi_f₂₄

end IsPushout

end Square

end CategoryTheory
