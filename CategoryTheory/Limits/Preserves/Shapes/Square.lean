/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Preservation of pullback/pushout squares

If a functor `F : C ⥤ D` preserves suitable cospans (resp. spans),
and `sq : Square C` is a pullback square (resp. a pushout square)
then so is the square `sq.map F`.

The lemma `Square.isPullback_iff_map_coyoneda_isPullback` also
shows that a square is a pullback square iff it is so after the
application of the functor `coyoneda.obj X` for all `X : Cᵒᵖ`.
Similarly, a square is a pushout square iff the opposite
square becomes a pullback square after the application of the
functor `yoneda.obj X` for all `X : C`.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Square

variable {sq : Square C}

/--
lemma `IsPullback.map` / 引理 `IsPullback.map`

English:
lemma IsPullback.map
  given: (h : sq.IsPullback) (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F]
  proof: Square.IsPullback.mk _ (isLimitPullbackConeMapOfIsLimit F sq.fac h.isLimit)

中文:
引理 是拉回.map
  条件: (h : sq.是拉回) (F : C ⥤ D) [保持极限 (cospan sq.f₂₄ sq.f₃₄) F]
  证明: Square.IsPullback.mk _ (isLimitPullbackConeMapOfIsLimit F sq.fac h.isLimit)

Depends on / 依赖: IsPullback, Square, Square.IsPullback.mk, h.isLimit, isLimit, isLimitPullbackConeMapOfIsLimit, sq.fac
-/
lemma IsPullback.map (h : sq.IsPullback) (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback :=
  Square.IsPullback.mk _ (isLimitPullbackConeMapOfIsLimit F sq.fac h.isLimit)

/--
lemma `IsPullback.of_map` / 引理 `IsPullback.of_map`

English:
lemma IsPullback.of_map
  statement: (F : C ⥤ D) [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F]
  proof: CategoryTheory.IsPullback.of_map F sq.fac h

中文:
引理 是拉回.of_map
  结论: (F : C ⥤ D) [反映极限 (cospan sq.f₂₄ sq.f₃₄) F]
  证明: CategoryTheory.IsPullback.of_map F sq.fac h

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.of_map, IsPullback, of_map, sq.fac
-/
lemma IsPullback.of_map (F : C ⥤ D) [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F]
    (h : (sq.map F).IsPullback) : sq.IsPullback :=
  CategoryTheory.IsPullback.of_map F sq.fac h

variable (sq) in
/--
lemma `IsPullback.map_iff` / 引理 `IsPullback.map_iff`

English:
lemma IsPullback.map_iff
  statement: (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F]
  proof: ⟨fun h => of_map F h, fun h => h.map F⟩

中文:
引理 是拉回.map_iff
  结论: (F : C ⥤ D) [保持极限 (cospan sq.f₂₄ sq.f₃₄) F]
  证明: ⟨fun h => of_map F h, fun h => h.map F⟩

Depends on / 依赖: h.map, of_map
-/
lemma IsPullback.map_iff (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F]
    [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback ↔ sq.IsPullback :=
  ⟨fun h => of_map F h, fun h => h.map F⟩

/--
lemma `IsPushout.map` / 引理 `IsPushout.map`

English:
lemma IsPushout.map
  given: (h : sq.IsPushout) (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F]
  proof: Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)

中文:
引理 是推出.map
  条件: (h : sq.是推出) (F : C ⥤ D) [保持余极限 (span sq.f₁₂ sq.f₁₃) F]
  证明: Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)

Depends on / 依赖: IsPushout, Square, Square.IsPushout.mk, h.isColimit, isColimit, isColimitPushoutCoconeMapOfIsColimit, sq.fac
-/
lemma IsPushout.map (h : sq.IsPushout) (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout :=
  Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)

/--
lemma `IsPushout.of_map` / 引理 `IsPushout.of_map`

English:
lemma IsPushout.of_map
  statement: (F : C ⥤ D) [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F]
  proof: CategoryTheory.IsPushout.of_map F sq.fac h

中文:
引理 是推出.of_map
  结论: (F : C ⥤ D) [反映余极限 (span sq.f₁₂ sq.f₁₃) F]
  证明: CategoryTheory.IsPushout.of_map F sq.fac h

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPushout.of_map, IsPushout, of_map, sq.fac
-/
lemma IsPushout.of_map (F : C ⥤ D) [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F]
    (h : (sq.map F).IsPushout) : sq.IsPushout :=
  CategoryTheory.IsPushout.of_map F sq.fac h

variable (sq) in
/--
lemma `IsPushout.map_iff` / 引理 `IsPushout.map_iff`

English:
lemma IsPushout.map_iff
  statement: (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F]
  proof: ⟨fun h => of_map F h, fun h => h.map F⟩

中文:
引理 是推出.map_iff
  结论: (F : C ⥤ D) [保持余极限 (span sq.f₁₂ sq.f₁₃) F]
  证明: ⟨fun h => of_map F h, fun h => h.map F⟩

Depends on / 依赖: h.map, of_map
-/
lemma IsPushout.map_iff (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F]
    [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout ↔ sq.IsPushout :=
  ⟨fun h => of_map F h, fun h => h.map F⟩

variable (sq)

/--
lemma `isPullback_iff_map_coyoneda_isPullback` / 引理 `isPullback_iff_map_coyoneda_isPullback`

English:
lemma isPullback_iff_map_coyoneda_isPullback
  proof: ⟨fun h _ => h.map _, fun h => IsPullback.mk _
    ((sq.pullbackCone.isLimitCoyonedaEquiv).symm (fun X => (h X).isLimit))⟩

中文:
引理 isPullback_iff_map_coyoneda_isPullback
  证明: ⟨fun h _ => h.map _, fun h => IsPullback.mk _
    ((sq.pullbackCone.isLimitCoyonedaEquiv).symm (fun X => (h X).isLimit))⟩

Depends on / 依赖: IsPullback, IsPullback.mk, h.map, isLimit, isLimitCoyonedaEquiv, pullbackCone, sq.pullbackCone.isLimitCoyonedaEquiv
-/
lemma isPullback_iff_map_coyoneda_isPullback :
    sq.IsPullback ↔ forall (X : Cᵒᵖ), (sq.map (coyoneda.obj X)).IsPullback :=
  ⟨fun h _ => h.map _, fun h => IsPullback.mk _
    ((sq.pullbackCone.isLimitCoyonedaEquiv).symm (fun X => (h X).isLimit))⟩

/--
lemma `isPushout_iff_op_map_yoneda_isPullback` / 引理 `isPushout_iff_op_map_yoneda_isPullback`

English:
lemma isPushout_iff_op_map_yoneda_isPullback
  proof: ⟨fun h _ => h.op.map _, fun h => IsPushout.mk _
    ((sq.pushoutCocone.isColimitYonedaEquiv).symm
      (fun X => IsLimit.ofIsoLimit (h X).isLimit (PullbackCone.ext (Iso.refl _))))⟩

中文:
引理 isPushout_iff_op_map_yoneda_isPullback
  证明: ⟨fun h _ => h.op.map _, fun h => IsPushout.mk _
    ((sq.pushoutCocone.isColimitYonedaEquiv).symm
      (fun X => IsLimit.ofIsoLimit (h X).isLimit (PullbackCone.ext (Iso.refl _))))⟩

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, IsPushout, IsPushout.mk, Iso.refl, PullbackCone, PullbackCone.ext, h.op.map, isColimitYonedaEquiv, isLimit, ofIsoLimit, pushoutCocone, sq.pushoutCocone.isColimitYonedaEquiv
-/
lemma isPushout_iff_op_map_yoneda_isPullback :
    sq.IsPushout ↔ forall (X : C), (sq.op.map (yoneda.obj X)).IsPullback :=
  ⟨fun h _ => h.op.map _, fun h => IsPushout.mk _
    ((sq.pushoutCocone.isColimitYonedaEquiv).symm
      (fun X => IsLimit.ofIsoLimit (h X).isLimit (PullbackCone.ext (Iso.refl _))))⟩

section

variable {sq₁ : Square (Type v)} {sq₂ : Square (Type u)}
  (e₁ : sq₁.X₁ ≃ sq₂.X₁) (e₂ : sq₁.X₂ ≃ sq₂.X₂)
  (e₃ : sq₁.X₃ ≃ sq₂.X₃) (e₄ : sq₁.X₄ ≃ sq₂.X₄)
  (comm₁₂ : e₂ ∘ sq₁.f₁₂ = sq₂.f₁₂ ∘ e₁)
  (comm₁₃ : e₃ ∘ sq₁.f₁₃ = sq₂.f₁₃ ∘ e₁)
  (comm₂₄ : e₄ ∘ sq₁.f₂₄ = sq₂.f₂₄ ∘ e₂)
  (comm₃₄ : e₄ ∘ sq₁.f₃₄ = sq₂.f₃₄ ∘ e₃)
include comm₁₂ comm₁₃ comm₂₄ comm₃₄

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (sq₁ sq₂) in
/--
lemma `IsPullback.iff_of_equiv` / 引理 `IsPullback.iff_of_equiv`

English:
lemma IsPullback.iff_of_equiv
  statement: sq₁.IsPullback ↔ sq₂.IsPullback
  proof: by
  rw [← IsPullback.map_iff sq₁ uliftFunctor.{max u v}]; rw [← IsPullback.map_iff sq₂ uliftFunctor.{max u v}]
  refine iff_of_iso (Square.isoMk
    (((Equiv.trans Equiv.ulift e₁).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₂).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equ

中文:
引理 是拉回.iff_of_equiv
  结论: sq₁.是拉回 ↔ sq₂.是拉回
  证明: by
  rw [← IsPullback.map_iff sq₁ uliftFunctor.{max u v}]; rw [← IsPullback.map_iff sq₂ uliftFunctor.{max u v}]
  refine iff_of_iso (Square.isoMk
    (((Equiv.trans Equiv.ulift e₁).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₂).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equ

Depends on / 依赖: Equiv.trans, Equiv.ulift, Equiv.ulift.symm, IsPullback, IsPullback.map_iff, Square, Square.isoMk, ULift.down_injective, all_goals, down_injective, iff_of_iso, map_iff, types_comp, uliftFunctor, uliftFunctor_map
-/
lemma IsPullback.iff_of_equiv : sq₁.IsPullback ↔ sq₂.IsPullback := by
  rw [← IsPullback.map_iff sq₁ uliftFunctor.{max u v}]; rw [← IsPullback.map_iff sq₂ uliftFunctor.{max u v}]
  refine iff_of_iso (Square.isoMk
    (((Equiv.trans Equiv.ulift e₁).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₂).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₃).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₄).trans Equiv.ulift.symm).toIso)
    ?_ ?_ ?_ ?_)
  all_goals ext; apply ULift.down_injective
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₁₂ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₁₃ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₂₄ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₃₄ _

/--
lemma `IsPullback.of_equiv` / 引理 `IsPullback.of_equiv`

English:
lemma IsPullback.of_equiv
  given: (h₁ : sq₁.IsPullback)
  statement: sq₂.IsPullback
  proof: (iff_of_equiv sq₁ sq₂ e₁ e₂ e₃ e₄ comm₁₂ comm₁₃ comm₂₄ comm₃₄).1 h₁

中文:
引理 是拉回.of_equiv
  条件: (h₁ : sq₁.是拉回)
  结论: sq₂.是拉回
  证明: (iff_of_equiv sq₁ sq₂ e₁ e₂ e₃ e₄ comm₁₂ comm₁₃ comm₂₄ comm₃₄).1 h₁

Depends on / 依赖: iff_of_equiv
-/
lemma IsPullback.of_equiv (h₁ : sq₁.IsPullback) : sq₂.IsPullback :=
  (iff_of_equiv sq₁ sq₂ e₁ e₂ e₃ e₄ comm₁₂ comm₁₃ comm₂₄ comm₃₄).1 h₁

end

end Square

end CategoryTheory
