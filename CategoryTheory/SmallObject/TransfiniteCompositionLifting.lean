/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The left lifting property is stable under transfinite composition

In this file, we show that if `W : MorphismProperty C`, then
`W.llp.IsStableUnderTransfiniteCompositionOfShape J`, i.e.
the class of morphisms which have the left lifting property with
respect to `W` is stable under transfinite composition.

The main technical lemma is
`HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot`.
It corresponds to the particular case `W` contains only one morphism `p : X ⟶ Y`:
it shows that a transfinite composition of morphisms that have the left
lifting property with respect to `p` also has the left lifting property
with respect to `p`.

About the proof, given a colimit cocone `c` for a well-order-continuous
functor `F : J ⥤ C` from a well-ordered type `J`, we introduce a projective
system `sqFunctor c p f g : Jᵒᵖ ⥤ Type _` which associates to any `j : J`
the structure `SqStruct c p f g j` which consists of those morphisms `f'`
which makes the diagram below commute. The data of such compatible `f'` for
all `j` shall give the expected lifting `c.pt ⟶ X` for the outer square.

```
         f
F.obj ⊥ --> X
   | Λ |
   | f'╱ |
   v ╱ |
F.obj j | p
   | |
   | |
   v g v
  c.pt ---> Y
```
This is constructed by transfinite induction on `j`:
* When `j = ⊥`, this is `f`;
* In order to pass from `j` to `Order.succ j`, we use the assumption that
  `F.obj j ⟶ F.obj (Order.succ j)` has the left lifting property with respect to `p`;
* When `j` is a limit element, we use the "continuity" of `F`.

-/

@[expose] public section

universe t w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace HasLiftingProperty

variable {J : Type w} [LinearOrder J] [OrderBot J]

namespace transfiniteComposition

variable {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  {X Y : C} (p : X ⟶ Y) (f : F.obj ⊥ ⟶ X) (g : c.pt ⟶ Y)

/-- Given a cocone `c` for a functor `F : J ⥤ C` from a well-ordered type,
and maps `p : X ⟶ Y`, `f : F.obj ⊥ ⟶ X`, `g : c.pt ⟶ Y`, this structure
contains the data of a map `F.obj j ⟶ X` such that `F.map (homOfLE bot_le) ≫ f' = f`
and `f' ≫ p = c.ι.app j ≫ g`. (This implies that the outer square below
commutes, see `SqStruct.w`.)

```
         f
F.obj ⊥ --> X
   | Λ |
   | f'╱ |
   v ╱ |
F.obj j | p
   | |
   | |
   v g v
  c.pt ---> Y
```
-/
@[ext]
/--
Definition of `SqStruct` / `SqStruct` 的定义

English:
structure SqStruct
  parameters: (j : J)
  axioms and operations (3):
    - f' : F.obj j ⟶ X
    - w₁ : F.map (homOfLE bot_le) ≫ f' = f  [default: by cat_disch]
    - w₂ : f' ≫ p = c.ι.app j ≫ g  [default: by cat_disch]

中文:
结构 SqStruct
  参数: (j : J)
  公理与运算 (3 个):
    - f' : F.obj j ⟶ X
    - w₁ : F.map (homOfLE bot_le) ≫ f' = f  [默认: by cat_disch]
    - w₂ : f' ≫ p = c.ι.app j ≫ g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure SqStruct (j : J) where
  /-- a morphism `F.obj j ⟶ X` -/
  f' : F.obj j ⟶ X
  w₁ : F.map (homOfLE bot_le) ≫ f' = f := by cat_disch
  w₂ : f' ≫ p = c.ι.app j ≫ g := by cat_disch

namespace SqStruct

attribute [reassoc (attr := simp)] w₁ w₂

variable {c p f g} {j : J} (sq' : SqStruct c p f g j)

set_option backward.isDefEq.respectTransparency false in
include sq' in
@[reassoc]
/--
lemma `w` / 引理 `w`

English:
lemma w
  statement: f ≫ p = c.ι.app ⊥ ≫ g
  proof: by
  rw [← sq'.w₁]; rw [assoc]; rw [sq'.w₂]; rw [Cocone.w_assoc]

中文:
引理 w
  结论: f ≫ p = c.ι.app ⊥ ≫ g
  证明: by
  rw [← sq'.w₁]; rw [assoc]; rw [sq'.w₂]; rw [Cocone.w_assoc]

Depends on / 依赖: Cocone, Cocone.w_assoc, w_assoc
-/
lemma w : f ≫ p = c.ι.app ⊥ ≫ g := by
  rw [← sq'.w₁]; rw [assoc]; rw [sq'.w₂]; rw [Cocone.w_assoc]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `sq` / 引理 `sq`

English:
lemma sq
  given: [SuccOrder J]
  proof: by simp

中文:
引理 sq
  条件: [SuccOrder J]
  证明: by simp
-/
lemma sq [SuccOrder J] :
    CommSq sq'.f' (F.map (homOfLE (Order.le_succ j))) p (c.ι.app _ ≫ g) where
  w := by simp

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `sqFunctor`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {j' : J} (α : j' ⟶ j)
  body: F.map α ≫ sq'.f'
  w₁ := by
    rw [← F.map_comp_assoc]
    exact sq'.w₁

中文:
定义 map
  签名: {j' : J} (α : j' ⟶ j)
  定义体: F.map α ≫ sq'.f'
  w₁ := by
    rw [← F.map_comp_assoc]
    exact sq'.w₁

Depends on / 依赖: F.map
-/
def map {j' : J} (α : j' ⟶ j) : SqStruct c p f g j' where
  f' := F.map α ≫ sq'.f'
  w₁ := by
    rw [← F.map_comp_assoc]
    exact sq'.w₁

end SqStruct

/-- The projective system `j ↦ SqStruct c p f g j.unop`. -/
@[simps]
/--
Definition of `sqFunctor` / `sqFunctor` 的定义

English:
definition sqFunctor
  signature: : Jᵒᵖ ⥤ Type _ where
  body: SqStruct c p f g j.unop
  map α := ↾fun sq' => sq'.map α.unop

中文:
定义 sqFunctor
  签名: : Jᵒᵖ ⥤ Type _ where
  定义体: SqStruct c p f g j.unop
  map α := ↾fun sq' => sq'.map α.unop

Depends on / 依赖: SqStruct, j.unop
-/
def sqFunctor : Jᵒᵖ ⥤ Type _ where
  obj j := SqStruct c p f g j.unop
  map α := ↾fun sq' => sq'.map α.unop

variable [F.IsWellOrderContinuous]

namespace wellOrderInductionData

variable {p c f g} {j : J} (hj : Order.IsSuccLimit j)
  (s : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ sqFunctor c p f g).sections)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftHom` / `liftHom` 的定义

English:
definition liftHom
  signature: : F.obj j ⟶ X
  body: (F.isColimitOfIsWellOrderContinuous j hj).desc
    (Cocone.mk _
      { app := fun i => (s.1 ⟨i⟩).f'
        naturality i i' g := by
          have := congr_arg SqStruct.f' (s.2 g.op)
          dsimp at this ⊢
          rw [this]; rw [comp_id] })

@[reassoc]

中文:
定义 liftHom
  签名: : F.obj j ⟶ X
  定义体: (F.isColimitOfIsWellOrderContinuous j hj).desc
    (Cocone.mk _
      { app := fun i => (s.1 ⟨i⟩).f'
        naturality i i' g := by
          have := congr_arg SqStruct.f' (s.2 g.op)
          dsimp at this ⊢
          rw [this]; rw [comp_id] })

@[reassoc]

Depends on / 依赖: Cocone, Cocone.mk, F.isColimitOfIsWellOrderContinuous, SqStruct, SqStruct.f, comp_id, congr_arg, g.op, isColimitOfIsWellOrderContinuous, naturality
-/
noncomputable def liftHom : F.obj j ⟶ X :=
  (F.isColimitOfIsWellOrderContinuous j hj).desc
    (Cocone.mk _
      { app := fun i => (s.1 ⟨i⟩).f'
        naturality i i' g := by
          have := congr_arg SqStruct.f' (s.2 g.op)
          dsimp at this ⊢
          rw [this]; rw [comp_id] })

@[reassoc]
/--
lemma `liftHom_fac` / 引理 `liftHom_fac`

English:
lemma liftHom_fac
  given: (i : J) (hi : i < j)
  proof: (F.isColimitOfIsWellOrderContinuous j hj).fac _ ⟨i, hi⟩

中文:
引理 liftHom_fac
  条件: (i : J) (hi : i < j)
  证明: (F.isColimitOfIsWellOrderContinuous j hj).fac _ ⟨i, hi⟩

Depends on / 依赖: F.isColimitOfIsWellOrderContinuous, isColimitOfIsWellOrderContinuous
-/
lemma liftHom_fac (i : J) (hi : i < j) :
    F.map (homOfLE hi.le) ≫ liftHom hj s = (s.1 ⟨⟨i, hi⟩⟩).f' :=
  (F.isColimitOfIsWellOrderContinuous j hj).fac _ ⟨i, hi⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `transfiniteComposition.wellOrderInductionData`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (sqFunctor c p f g).obj (Opposite.op j) where
  body: liftHom hj s
  w₁ := by
    have h : ⊥ < j := Ne.bot_lt' (by
      rintro rfl
      exact Order.not_isSuccLimit_bot hj)
    rw [liftHom_fac hj s ⊥ h]
    simpa using (s.1 ⟨⊥, h⟩).w₁
  w₂ := (F.isColimitOfIsWellOrderContinuous j hj).hom_ext (fun ⟨i, hij⟩ => by
    have := (s.1 ⟨i, hij⟩).w₂
    dsimp 

中文:
定义 lift
  签名: : (sqFunctor c p f g).obj (Opposite.op j) where
  定义体: liftHom hj s
  w₁ := by
    have h : ⊥ < j := Ne.bot_lt' (by
      rintro rfl
      exact Order.not_isSuccLimit_bot hj)
    rw [liftHom_fac hj s ⊥ h]
    simpa using (s.1 ⟨⊥, h⟩).w₁
  w₂ := (F.isColimitOfIsWellOrderContinuous j hj).hom_ext (fun ⟨i, hij⟩ => by
    have := (s.1 ⟨i, hij⟩).w₂
    dsimp 

Depends on / 依赖: liftHom
-/
noncomputable def lift : (sqFunctor c p f g).obj (Opposite.op j) where
  f' := liftHom hj s
  w₁ := by
    have h : ⊥ < j := Ne.bot_lt' (by
      rintro rfl
      exact Order.not_isSuccLimit_bot hj)
    rw [liftHom_fac hj s ⊥ h]
    simpa using (s.1 ⟨⊥, h⟩).w₁
  w₂ := (F.isColimitOfIsWellOrderContinuous j hj).hom_ext (fun ⟨i, hij⟩ => by
    have := (s.1 ⟨i, hij⟩).w₂
    dsimp at this ⊢
    rw [liftHom_fac_assoc _ _ _ hij]; rw [this]; rw [Cocone.w_assoc])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `map_lift` / 引理 `map_lift`

English:
lemma map_lift
  given: {i : J} (hij : i < j)
  proof: by
  ext
  apply liftHom_fac

中文:
引理 map_lift
  条件: {i : J} (hij : i < j)
  证明: by
  ext
  apply liftHom_fac

Depends on / 依赖: liftHom_fac
-/
lemma map_lift {i : J} (hij : i < j) :
    (lift hj s).map (homOfLE hij.le) = s.1 ⟨⟨i, hij⟩⟩ := by
  ext
  apply liftHom_fac

end wellOrderInductionData

variable {p} [SuccOrder J] [WellFoundedLT J]

section

variable (hF : forall (j : J) (_ : ¬IsMax j),
  HasLiftingPropertyFixedBot (F.map (homOfLE (Order.le_succ j))) p (c.ι.app _ ≫ g))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open wellOrderInductionData in
/--
Definition of `wellOrderInductionData` / `wellOrderInductionData` 的定义

English:
definition wellOrderInductionData
  signature: :
  body: have := hF j hj sq'.f'
    have := hF j hj
    { f' := sq'.sq.lift
      w₁ := by
        dsimp
        simp only [← sq'.w₁]
        conv_rhs => rw [← sq'.sq.fac_left, ← F.map_comp_assoc]
        rfl }
  map_succ j hj sq' := by cat_disch
  lift j hj s := lift hj s
  map_lift j hj s i hij := map_lift

中文:
定义 wellOrderInductionData
  签名: :
  定义体: have := hF j hj sq'.f'
    have := hF j hj
    { f' := sq'.sq.lift
      w₁ := by
        dsimp
        simp only [← sq'.w₁]
        conv_rhs => rw [← sq'.sq.fac_left, ← F.map_comp_assoc]
        rfl }
  map_succ j hj sq' := by cat_disch
  lift j hj s := lift hj s
  map_lift j hj s i hij := map_lift

Depends on / 依赖: F.map_comp_assoc, cat_disch, conv_rhs, fac_left, map_comp_assoc, map_lift, map_succ, sq.fac_left, sq.lift
-/
noncomputable def wellOrderInductionData :
    (sqFunctor c p f g).WellOrderInductionData where
  succ j hj sq' :=
    have := hF j hj sq'.f'
    have := hF j hj
    { f' := sq'.sq.lift
      w₁ := by
        dsimp
        simp only [← sq'.w₁]
        conv_rhs => rw [← sq'.sq.fac_left, ← F.map_comp_assoc]
        rfl }
  map_succ j hj sq' := by cat_disch
  lift j hj s := lift hj s
  map_lift j hj s i hij := map_lift hj s hij

include hF hc

variable {c f g} (sq : CommSq f (c.ι.app ⊥) p g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasLift` / 引理 `hasLift`

English:
lemma hasLift
  statement: sq.HasLift
  proof: by
  obtain ⟨s, hs⟩ := (wellOrderInductionData c f g hF).surjective { w₂ := sq.w, .. }
  replace hs := congr_arg SqStruct.f' hs
  dsimp at hs
  let t : Cocone F := Cocone.mk X
    { app j := (s.1 ⟨j⟩).f'
      naturality j j' g := by simpa using congr_arg SqStruct.f' (s.2 g.op) }
  let l := hc.desc 

中文:
引理 hasLift
  结论: sq.HasLift
  证明: by
  obtain ⟨s, hs⟩ := (wellOrderInductionData c f g hF).surjective { w₂ := sq.w, .. }
  replace hs := congr_arg SqStruct.f' hs
  dsimp at hs
  let t : Cocone F := Cocone.mk X
    { app j := (s.1 ⟨j⟩).f'
      naturality j j' g := by simpa using congr_arg SqStruct.f' (s.2 g.op) }
  let l := hc.desc 

Depends on / 依赖: Cocone, Cocone.mk, SqStruct, SqStruct.f, SqStruct.w, congr_arg, fac_left, fac_right, g.op, hc.desc, hc.fac, hc.hom_ext, hom_ext, naturality, reassoc_of, replace, sq.w, surjective, wellOrderInductionData
-/
lemma hasLift : sq.HasLift := by
  obtain ⟨s, hs⟩ := (wellOrderInductionData c f g hF).surjective { w₂ := sq.w, .. }
  replace hs := congr_arg SqStruct.f' hs
  dsimp at hs
  let t : Cocone F := Cocone.mk X
    { app j := (s.1 ⟨j⟩).f'
      naturality j j' g := by simpa using congr_arg SqStruct.f' (s.2 g.op) }
  let l := hc.desc t
  have hl (j : J) : c.ι.app j ≫ l = (s.1 ⟨j⟩).f' := hc.fac t j
  exact ⟨⟨{
    l := l
    fac_left := by rw [hl, hs]
    fac_right := hc.hom_ext (fun j => by rw [reassoc_of% (hl j), SqStruct.w₂])}⟩⟩

/--
lemma `hasLiftingPropertyFixedBot_ι_app_bot` / 引理 `hasLiftingPropertyFixedBot_ι_app_bot`

English:
lemma hasLiftingPropertyFixedBot_ι_app_bot
  statement: HasLiftingPropertyFixedBot (c.ι.app ⊥) p g
  proof: fun _ sq => hasLift hc hF sq

中文:
引理 hasLiftingPropertyFixedBot_ι_app_bot
  结论: HasLifting命题ertyFixedBot (c.ι.app ⊥) p g
  证明: fun _ sq => hasLift hc hF sq

Depends on / 依赖: hasLift
-/
lemma hasLiftingPropertyFixedBot_ι_app_bot : HasLiftingPropertyFixedBot (c.ι.app ⊥) p g :=
  fun _ sq => hasLift hc hF sq

end

variable {c} (hF : forall (j : J) (_ : ¬IsMax j),
  HasLiftingProperty (F.map (homOfLE (Order.le_succ j))) p)

include hc hF
/--
lemma `hasLiftingProperty_ι_app_bot` / 引理 `hasLiftingProperty_ι_app_bot`

English:
lemma hasLiftingProperty_ι_app_bot
  statement: HasLiftingProperty (c.ι.app ⊥) p where
  proof: hasLift hc (fun j hj _ _ => by have := hF j hj; infer_instance) sq

中文:
引理 hasLiftingProperty_ι_app_bot
  结论: HasLifting命题erty (c.ι.app ⊥) p where
  证明: hasLift hc (fun j hj _ _ => by have := hF j hj; infer_instance) sq

Depends on / 依赖: hasLift, infer_instance
-/
lemma hasLiftingProperty_ι_app_bot : HasLiftingProperty (c.ι.app ⊥) p where
  sq_hasLift sq := hasLift hc (fun j hj _ _ => by have := hF j hj; infer_instance) sq

end transfiniteComposition

end HasLiftingProperty

namespace MorphismProperty

variable (W : MorphismProperty C)
  (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isStableUnderTransfiniteCompositionOfShape_llp` / 实例 `isStableUnderTransfiniteCompositionOfShape_llp`

English:
instance isStableUnderTransfiniteCompositionOfShape_llp
  signature: :
  body: by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  have : W.llp (h.incl.app ⊥) := fun _ _ p hp =>
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := h.isColimit) (fun j hj => h.map_mem j hj _ hp)
  exact (MorphismProperty.arrow_mk_iso_i

中文:
实例 isStableUnderTransfiniteCompositionOfShape_llp
  签名: :
  定义体: by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  have : W.llp (h.incl.app ⊥) := fun _ _ p hp =>
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := h.isColimit) (fun j hj => h.map_mem j hj _ hp)
  exact (MorphismProperty.arrow_mk_iso_i

Depends on / 依赖: Arrow.isoMk, HasLiftingProperty, HasLiftingProperty.transfiniteComposition.hasLiftingProperty_, Iso.refl, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, W.llp, arrow_mk_iso_iff, h.incl.app, h.isColimit, h.isoBot.symm, h.map_mem, isColimit, isStableUnderTransfiniteCompositionOfShape_iff, isoBot, map_mem, transfiniteComposition
-/
instance isStableUnderTransfiniteCompositionOfShape_llp :
    W.llp.IsStableUnderTransfiniteCompositionOfShape J := by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  have : W.llp (h.incl.app ⊥) := fun _ _ p hp =>
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := h.isColimit) (fun j hj => h.map_mem j hj _ hp)
  exact (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk h.isoBot.symm (Iso.refl _))).2 this

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderTransfiniteComposition.{w} W.llp

中文:
实例 :
  签名: Morphism命题erty.IsStableUnderTransfiniteComposition.{w} W.llp
-/
instance : MorphismProperty.IsStableUnderTransfiniteComposition.{w} W.llp where

/--
lemma `transfiniteCompositionsOfShape_le_llp_rlp` / 引理 `transfiniteCompositionsOfShape_le_llp_rlp`

English:
lemma transfiniteCompositionsOfShape_le_llp_rlp
  proof: by
  have := W.rlp.isStableUnderTransfiniteCompositionOfShape_llp J
  rw [isStableUnderTransfiniteCompositionOfShape_iff] at this
  exact le_trans (transfiniteCompositionsOfShape_monotone J W.le_llp_rlp) this

中文:
引理 transfiniteCompositionsOfShape_le_llp_rlp
  证明: by
  have := W.rlp.isStableUnderTransfiniteCompositionOfShape_llp J
  rw [isStableUnderTransfiniteCompositionOfShape_iff] at this
  exact le_trans (transfiniteCompositionsOfShape_monotone J W.le_llp_rlp) this

Depends on / 依赖: W.le_llp_rlp, W.rlp.isStableUnderTransfiniteCompositionOfShape_llp, isStableUnderTransfiniteCompositionOfShape_iff, isStableUnderTransfiniteCompositionOfShape_llp, le_llp_rlp, le_trans, transfiniteCompositionsOfShape_monotone
-/
lemma transfiniteCompositionsOfShape_le_llp_rlp :
    W.transfiniteCompositionsOfShape J <= W.rlp.llp := by
  have := W.rlp.isStableUnderTransfiniteCompositionOfShape_llp J
  rw [isStableUnderTransfiniteCompositionOfShape_iff] at this
  exact le_trans (transfiniteCompositionsOfShape_monotone J W.le_llp_rlp) this

/--
lemma `transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp` / 引理 `transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp`

English:
lemma transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
  proof: by
  simpa using transfiniteCompositionsOfShape_le_llp_rlp (coproducts.{t} W).pushouts J

中文:
引理 transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
  证明: by
  simpa using transfiniteCompositionsOfShape_le_llp_rlp (coproducts.{t} W).pushouts J

Depends on / 依赖: coproducts, pushouts, transfiniteCompositionsOfShape_le_llp_rlp
-/
lemma transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp :
    (coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J <= W.rlp.llp := by
  simpa using transfiniteCompositionsOfShape_le_llp_rlp (coproducts.{t} W).pushouts J

/--
lemma `retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp` / 引理 `retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp`

English:
lemma retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
  proof: by
  rw [le_llp_iff_le_rlp]; rw [rlp_retracts]; rw [← le_llp_iff_le_rlp]
  apply transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp

中文:
引理 retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
  证明: by
  rw [le_llp_iff_le_rlp]; rw [rlp_retracts]; rw [← le_llp_iff_le_rlp]
  apply transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp

Depends on / 依赖: le_llp_iff_le_rlp, rlp_retracts, transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
-/
lemma retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp :
    ((coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J).retracts <= W.rlp.llp := by
  rw [le_llp_iff_le_rlp]; rw [rlp_retracts]; rw [← le_llp_iff_le_rlp]
  apply transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp

/--
lemma `transfiniteCompositions_le_llp_rlp` / 引理 `transfiniteCompositions_le_llp_rlp`

English:
lemma transfiniteCompositions_le_llp_rlp
  proof: by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨_, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le_llp_rlp _ _ hf

中文:
引理 transfiniteCompositions_le_llp_rlp
  证明: by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨_, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le_llp_rlp _ _ hf

Depends on / 依赖: W.transfiniteCompositionsOfShape_le_llp_rlp, transfiniteCompositionsOfShape_le_llp_rlp, transfiniteCompositions_iff
-/
lemma transfiniteCompositions_le_llp_rlp :
    transfiniteCompositions.{w} W <= W.rlp.llp := by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨_, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le_llp_rlp _ _ hf

/--
lemma `transfiniteCompositions_pushouts_coproducts_le_llp_rlp` / 引理 `transfiniteCompositions_pushouts_coproducts_le_llp_rlp`

English:
lemma transfiniteCompositions_pushouts_coproducts_le_llp_rlp
  proof: by
  simpa using transfiniteCompositions_le_llp_rlp.{w} (coproducts.{w} W).pushouts

中文:
引理 transfiniteCompositions_pushouts_coproducts_le_llp_rlp
  证明: by
  simpa using transfiniteCompositions_le_llp_rlp.{w} (coproducts.{w} W).pushouts

Depends on / 依赖: coproducts, pushouts, transfiniteCompositions_le_llp_rlp
-/
lemma transfiniteCompositions_pushouts_coproducts_le_llp_rlp :
    (transfiniteCompositions.{w} (coproducts.{w} W).pushouts) <= W.rlp.llp := by
  simpa using transfiniteCompositions_le_llp_rlp.{w} (coproducts.{w} W).pushouts

/--
lemma `retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp` / 引理 `retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp`

English:
lemma retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp
  proof: by
  rw [le_llp_iff_le_rlp]; rw [rlp_retracts]; rw [← le_llp_iff_le_rlp]
  apply transfiniteCompositions_pushouts_coproducts_le_llp_rlp

中文:
引理 retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp
  证明: by
  rw [le_llp_iff_le_rlp]; rw [rlp_retracts]; rw [← le_llp_iff_le_rlp]
  apply transfiniteCompositions_pushouts_coproducts_le_llp_rlp

Depends on / 依赖: le_llp_iff_le_rlp, rlp_retracts, transfiniteCompositions_pushouts_coproducts_le_llp_rlp
-/
lemma retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp :
    (transfiniteCompositions.{w} (coproducts.{w} W).pushouts).retracts <= W.rlp.llp := by
  rw [le_llp_iff_le_rlp]; rw [rlp_retracts]; rw [← le_llp_iff_le_rlp]
  apply transfiniteCompositions_pushouts_coproducts_le_llp_rlp

end MorphismProperty

end CategoryTheory
