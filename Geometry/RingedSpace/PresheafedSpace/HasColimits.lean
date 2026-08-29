/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `TopCat` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheafed spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/

@[expose] public section


noncomputable section

universe v' u' v u

open CategoryTheory Opposite CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  TopCat TopCat.Presheaf TopologicalSpace

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eqToHom_map

-- We could enable the following attribute:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `map_id_c_app` / 定理 `map_id_c_app`

English:
theorem map_id_c_app
  given: (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U)
  proof: by
  simp [PresheafedSpace.congr_app (F.map_id j)]

中文:
定理 map_id_c_app
  条件: (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U)
  证明: by
  simp [PresheafedSpace.congr_app (F.map_id j)]

Depends on / 依赖: F.map_id, PresheafedSpace, PresheafedSpace.congr_app, congr_app, map_id
-/
theorem map_id_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U) :
    (F.map (𝟙 j)).c.app U =
      (Pushforward.id (F.obj j).presheaf).inv.app U ≫
        (pushforwardEq (by simp) (F.obj j).presheaf).hom.app U := by
  simp [PresheafedSpace.congr_app (F.map_id j)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `map_comp_c_app` / 定理 `map_comp_c_app`

English:
theorem map_comp_c_app
  statement: (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃}
  proof: by
  simp [PresheafedSpace.congr_app (F.map_comp f g)]

中文:
定理 map_comp_c_app
  结论: (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃}
  证明: by
  simp [PresheafedSpace.congr_app (F.map_comp f g)]

Depends on / 依赖: F.map_comp, PresheafedSpace, PresheafedSpace.congr_app, congr_app, map_comp
-/
theorem map_comp_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃}
    (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
    (F.map (f ≫ g)).c.app U =
      (F.map g).c.app U ≫
        ((pushforward C (F.map g).base).map (F.map f).c).app U ≫
          (pushforwardEq (congr_arg Hom.base (F.map_comp f g).symm) _).hom.app U := by
  simp [PresheafedSpace.congr_app (F.map_comp f g)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the underlying spaces.
-/
@[simps]
/--
Definition of `componentwiseDiagram` / `componentwiseDiagram` 的定义

English:
definition componentwiseDiagram
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
  body: (F.obj (unop j)).presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map {j k} f := (F.map f.unop).c.app _ ≫
    (F.obj (unop k)).presheaf.map (eqToHom (by rw [← colimit.w F f.unop, comp_base]; rfl))
  map_comp {i j k} f g := by
    simp only [assoc, CategoryTheory.NatTrans.naturalit

中文:
定义 componentwiseDiagram
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
  定义体: (F.obj (unop j)).presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map {j k} f := (F.map f.unop).c.app _ ≫
    (F.obj (unop k)).presheaf.map (eqToHom (by rw [← colimit.w F f.unop, comp_base]; rfl))
  map_comp {i j k} f g := by
    simp only [assoc, CategoryTheory.NatTrans.naturalit

Depends on / 依赖: F.obj, Opens.map, colimit, presheaf, presheaf.obj
-/
def componentwiseDiagram (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) : Jᵒᵖ ⥤ C where
  obj j := (F.obj (unop j)).presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map {j k} f := (F.map f.unop).c.app _ ≫
    (F.obj (unop k)).presheaf.map (eqToHom (by rw [← colimit.w F f.unop, comp_base]; rfl))
  map_comp {i j k} f g := by
    simp only [assoc, CategoryTheory.NatTrans.naturality_assoc]
    simp

variable [HasColimitsOfShape J TopCat.{v}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(Presheaf C X)ᵒᵖ`.
-/
@[simps]
/--
Definition of `pushforwardDiagramToColimit` / `pushforwardDiagramToColimit` 的定义

English:
definition pushforwardDiagramToColimit
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  body: op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).presheaf)
  map {j j'} f :=
    ((pushforward C (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).map (F.map f).c ≫
      (Pushforward.comp ((F ⋙ PresheafedSpace.forget C).map f)
        (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.obj j).

中文:
定义 pushforwardDiagramToColimit
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  定义体: op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).presheaf)
  map {j j'} f :=
    ((pushforward C (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).map (F.map f).c ≫
      (Pushforward.comp ((F ⋙ PresheafedSpace.forget C).map f)
        (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.obj j).

Depends on / 依赖: F.obj, PresheafedSpace, PresheafedSpace.forget, colimit, forget, presheaf
-/
def pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    J ⥤ (Presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ where
  obj j := op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).presheaf)
  map {j j'} f :=
    ((pushforward C (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).map (F.map f).c ≫
      (Pushforward.comp ((F ⋙ PresheafedSpace.forget C).map f)
        (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.obj j).presheaf).inv ≫
      (pushforwardEq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).presheaf).hom).op
  map_id j := by
    apply (opEquiv _ _).injective
    refine NatTrans.ext (funext fun U => ?_)
    induction U with
    | op U =>
      simp [opEquiv]
      rfl
  map_comp {j₁ j₂ j₃} f g := by
    apply (opEquiv _ _).injective
    refine NatTrans.ext (funext fun U => ?_)
    dsimp [opEquiv]
    have :
      op ((Opens.map (F.map g).base).obj
          ((Opens.map (colimit.ι (F ⋙ forget C) j₃)).obj U.unop)) =
        op ((Opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U)) := by
      apply unop_injective
      rw [← Opens.map_comp_obj]
      congr
      exact colimit.w (F ⋙ PresheafedSpace.forget C) g
    simp only [map_comp_c_app, pushforward_obj_obj, pushforward_map_app, comp_base,
      pushforwardEq_hom_app, op_obj, Opens.map_comp_obj, id_comp, assoc, eqToHom_map_comp,
      NatTrans.naturality_assoc, pushforward_obj_map, eqToHom_unop]
    simp [NatTrans.congr (α := (F.map f).c) this]

variable [forall X : TopCat.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  body: Limits.colimit (F ⋙ PresheafedSpace.forget C)
  presheaf := limit (pushforwardDiagramToColimit F).leftOp

@[simp]

中文:
定义 colimit
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  定义体: Limits.colimit (F ⋙ PresheafedSpace.forget C)
  presheaf := limit (pushforwardDiagramToColimit F).leftOp

@[simp]

Depends on / 依赖: Limits, Limits.colimit, PresheafedSpace, PresheafedSpace.forget, colimit, forget
-/
def colimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : PresheafedSpace C where
  carrier := Limits.colimit (F ⋙ PresheafedSpace.forget C)
  presheaf := limit (pushforwardDiagramToColimit F).leftOp

@[simp]
/--
theorem `colimit_carrier` / 定理 `colimit_carrier`

English:
theorem colimit_carrier
  given: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  proof: rfl

@[simp]

中文:
定理 colimit_carrier
  条件: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  证明: rfl

@[simp]
-/
theorem colimit_carrier (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).carrier = Limits.colimit (F ⋙ PresheafedSpace.forget C) :=
  rfl

@[simp]
/--
theorem `colimit_presheaf` / 定理 `colimit_presheaf`

English:
theorem colimit_presheaf
  given: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  proof: rfl

中文:
定理 colimit_presheaf
  条件: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  证明: rfl
-/
theorem colimit_presheaf (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).presheaf = limit (pushforwardDiagramToColimit F).leftOp :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
@[simps]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  body: colimit F
  ι :=
    { app := fun j =>
        { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j
          c := limit.π _ (op j) }
      naturality := fun {j j'} f => by
        ext1
        · ext x
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
        · ext ⟨⟩
          simp

中文:
定义 colimitCocone
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  定义体: colimit F
  ι :=
    { app := fun j =>
        { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j
          c := limit.π _ (op j) }
      naturality := fun {j j'} f => by
        ext1
        · ext x
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
        · ext ⟨⟩
          simp

Depends on / 依赖: colimit
-/
def colimitCocone (F : J ⥤ PresheafedSpace.{_, _, v} C) : Cocone F where
  pt := colimit F
  ι :=
    { app := fun j =>
        { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j
          c := limit.π _ (op j) }
      naturality := fun {j j'} f => by
        ext1
        · ext x
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
        · ext ⟨⟩
          simp [← congr_arg NatTrans.app (limit.w (pushforwardDiagramToColimit F).leftOp f.op)] }

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `descCApp` / `descCApp` 的定义

English:
definition descCApp
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ)
  body: by
  refine
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => ?_
              naturality := fun j j' f => ?_ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · ref

中文:
定义 descCApp
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ)
  定义体: by
  refine
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => ?_
              naturality := fun j j' f => ?_ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · ref

Depends on / 依赖: limit.lift, limitObjIsoLimitCompEvaluation, naturality, presheaf, s.pt.presheaf.obj
-/
def descCApp (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ) :
    s.pt.presheaf.obj U ⟶
      (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U := by
  refine
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => ?_
              naturality := fun j j' f => ?_ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eqToHom ?_)
    dsimp
    rw [← Opens.map_comp_obj]
    simp
  · dsimp
    rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    have w :=
      Functor.congr_obj
        (congr_arg Opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        (unop U)
    simp only [Opens.map_comp_obj_unop] at w
    replace w := congr_arg op w
    have w' := NatTrans.congr (F.map f.unop).c w
    rw [w']
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `desc_c_naturality` / 定理 `desc_c_naturality`

English:
theorem desc_c_naturality
  statement: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
  proof: by
  dsimp [descCApp]
  refine limit_obj_ext (fun j => ?_)
  have w := Functor.congr_hom (congr_arg Opens.map
    (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j))) i.unop
  simp only [Opens.map_comp_map] at w
  simp [congr_arg Quiver.Hom.op w]

中文:
定理 desc_c_naturality
  结论: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
  证明: by
  dsimp [descCApp]
  refine limit_obj_ext (fun j => ?_)
  have w := Functor.congr_hom (congr_arg Opens.map
    (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j))) i.unop
  simp only [Opens.map_comp_map] at w
  simp [congr_arg Quiver.Hom.op w]

Depends on / 依赖: Functor, Functor.congr_hom, Opens.map, Opens.map_comp_map, PresheafedSpace, PresheafedSpace.forget, Quiver, Quiver.Hom.op, colimit, congr_arg, congr_hom, descCApp, forget, i.unop, limit_obj_ext, mapCocone, map_comp_map
-/
theorem desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
    {U V : (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) :
    s.pt.presheaf.map i ≫ descCApp F s V =
      descCApp F s U ≫
        (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (colimitCocone F).pt.presheaf).map
          i := by
  dsimp [descCApp]
  refine limit_obj_ext (fun j => ?_)
  have w := Functor.congr_hom (congr_arg Opens.map
    (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j))) i.unop
  simp only [Opens.map_comp_map] at w
  simp [congr_arg Quiver.Hom.op w]

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
  body: colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c :=
    { app := fun U => descCApp F s U
      naturality := fun _ _ i => desc_c_naturality F s i }

中文:
定义 desc
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
  定义体: colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c :=
    { app := fun U => descCApp F s U
      naturality := fun _ _ i => desc_c_naturality F s i }

Depends on / 依赖: PresheafedSpace, PresheafedSpace.forget, colimit, colimit.desc, forget, mapCocone
-/
def desc (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) : colimit F ⟶ s.pt where
  base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c :=
    { app := fun U => descCApp F s U
      naturality := fun _ _ i => desc_c_naturality F s i }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `desc_fac` / 定理 `desc_fac`

English:
theorem desc_fac
  given: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J)
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the original proof is just
  -- `ext <;> dsimp [desc, descCApp] <;> simpa`,
  -- but this has to be expanded a bit
  ext U
  · simp [desc]
  · simp only [op_obj, desc, descCApp, Presheaf.comp_app, comp_c_app, colim

中文:
定理 desc_fac
  条件: (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J)
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the original proof is just
  -- `ext <;> dsimp [desc, descCApp] <;> simpa`,
  -- but this has to be expanded a bit
  ext U
  · simp [desc]
  · simp only [op_obj, desc, descCApp, Presheaf.comp_app, comp_c_app, colim
-/
theorem desc_fac (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ desc F s = s.ι.app j := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the original proof is just
  -- `ext <;> dsimp [desc, descCApp] <;> simpa`,
  -- but this has to be expanded a bit
  ext U
  · simp [desc]
  · simp only [op_obj, desc, descCApp, Presheaf.comp_app, comp_c_app, colimitCocone_ι_app_c, assoc]
    rw [limitObjIsoLimitCompEvaluation_inv_π_app_assoc]
    simp

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  body: desc F s
  fac s := desc_fac F s
  uniq s m w := by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base =
        colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) := by
      dsimp
      -- `colimit.

中文:
定义 colimitCoconeIsColimit
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  定义体: desc F s
  fac s := desc_fac F s
  uniq s m w := by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base =
        colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) := by
      dsimp
      -- `colimit.
-/
def colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    IsColimit (colimitCocone F) where
  desc s := desc F s
  fac s := desc_fac F s
  uniq s m w := by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base =
        colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) := by
      dsimp
      -- `colimit.hom_ext` used to be automatically applied by `ext` before https://github.com/leanprover-community/mathlib4/pull/21302
      apply colimit.hom_ext fun j => ?_
      ext
      rw [colimit.ι_desc]; rw [mapCocone_ι_app]; rw [← w j]
      simp
    ext : 1
    · exact t
    · refine NatTrans.ext (funext fun U => limit_obj_ext fun j => ?_)
      simp [desc, descCApp,
        PresheafedSpace.congr_app (w (unop j)).symm U,
        NatTrans.congr (limit.π (pushforwardDiagramToColimit F).leftOp j)
        (congr_arg op (Functor.congr_obj (congr_arg Opens.map t) (unop U)))]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimitsOfShape J (PresheafedSpace.{_, _, v} C)
  body: ⟨colimitCocone F, colimitCoconeIsColimit F⟩

中文:
实例 :
  签名: HasColimitsOfShape J (PresheafedSpace.{_, _, v} C)
  定义体: ⟨colimitCocone F, colimitCoconeIsColimit F⟩

Depends on / 依赖: colimitCocone, colimitCoconeIsColimit
-/
instance : HasColimitsOfShape J (PresheafedSpace.{_, _, v} C) where
  has_colimit F := ⟨colimitCocone F, colimitCoconeIsColimit F⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (PresheafedSpace.forget.{v, u, v} C)
  body: ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F) by
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    fapply Cocone.ext
    · rfl
    · simp⟩

中文:
实例 :
  签名: PreservesColimitsOfShape J (PresheafedSpace.forget.{v, u, v} C)
  定义体: ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F) by
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    fapply Cocone.ext
    · rfl
    · simp⟩

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, colimit, colimit.isColimit, colimitCoconeIsColimit, fapply, isColimit, ofIsoColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance : PreservesColimitsOfShape J (PresheafedSpace.forget.{v, u, v} C) :=
⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F) by
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    fapply Cocone.ext
    · rfl
    · simp⟩

/--
Instance `instHasColimits` / 实例 `instHasColimits`

English:
instance instHasColimits
  signature: [HasLimits C]
  body: ⟨fun {_ _} => ⟨fun {F} => ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩⟩

中文:
实例 instHasColimits
  签名: [HasLimits C]
  定义体: ⟨fun {_ _} => ⟨fun {F} => ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩⟩

Depends on / 依赖: colimitCocone, colimitCoconeIsColimit
-/
instance instHasColimits [HasLimits C] : HasColimits (PresheafedSpace.{_, _, v} C) :=
  ⟨fun {_ _} => ⟨fun {F} => ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩⟩

/--
Instance `forget_preservesColimits` / 实例 `forget_preservesColimits`

English:
instance forget_preservesColimits
  signature: [HasLimits C]
  body: { preservesColimit := fun {F} => preservesColimit_of_preserves_colimit_cocone
          (colimitCoconeIsColimit F)
          (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _))) }

中文:
实例 forget_preservesColimits
  签名: [HasLimits C]
  定义体: { preservesColimit := fun {F} => preservesColimit_of_preserves_colimit_cocone
          (colimitCoconeIsColimit F)
          (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _))) }

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, colimit, colimit.isColimit, colimitCoconeIsColimit, isColimit, ofIsoColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance forget_preservesColimits [HasLimits C] :
    PreservesColimits (PresheafedSpace.forget.{_, _, v} C) where
  preservesColimitsOfShape {J 𝒥} :=
    { preservesColimit := fun {F} => preservesColimit_of_preserves_colimit_cocone
          (colimitCoconeIsColimit F)
          (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _))) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitPresheafObjIsoComponentwiseLimit` / `colimitPresheafObjIsoComponentwiseLimit` 的定义

English:
definition colimitPresheafObjIsoComponentwiseLimit
  signature: (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
  body: by
  refine
    ((sheafIsoOfIso (colimit.isoColimitCocone ⟨_, colimitCoconeIsColimit F⟩).symm).app
          (op U)).trans
      ?_
  refine (limitObjIsoLimitCompEvaluation _ _).trans (Limits.lim.mapIso ?_)
  fapply NatIso.ofComponents
  · intro X
    refine (F.obj (unop X)).presheaf.mapIso (eqToIso

中文:
定义 colimitPresheafObjIsoComponentwiseLimit
  签名: (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
  定义体: by
  refine
    ((sheafIsoOfIso (colimit.isoColimitCocone ⟨_, colimitCoconeIsColimit F⟩).symm).app
          (op U)).trans
      ?_
  refine (limitObjIsoLimitCompEvaluation _ _).trans (Limits.lim.mapIso ?_)
  fapply NatIso.ofComponents
  · intro X
    refine (F.obj (unop X)).presheaf.mapIso (eqToIso

Depends on / 依赖: F.obj, Functor, Functor.op_obj, Limits, Limits.lim.mapIso, NatIso, NatIso.ofComponents, Opens.map_coe, Set.preimage, Set.preimage_preimage, SetLike, SetLike.ext, TopCat, TopCat.comp_app, _iff, colimit, colimit.isoColimitCocone, colimitCocone, colimitCoconeIsColimit, comp_app
-/
def colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) :
    (Limits.colimit F).presheaf.obj (op U) ≅ limit (componentwiseDiagram F U) := by
  refine
    ((sheafIsoOfIso (colimit.isoColimitCocone ⟨_, colimitCoconeIsColimit F⟩).symm).app
          (op U)).trans
      ?_
  refine (limitObjIsoLimitCompEvaluation _ _).trans (Limits.lim.mapIso ?_)
  fapply NatIso.ofComponents
  · intro X
    refine (F.obj (unop X)).presheaf.mapIso (eqToIso ?_)
    simp only [Functor.op_obj, op_inj_iff, Opens.map_coe, SetLike.ext'_iff,
      Set.preimage_preimage]
    refine congr_arg (Set.preimage · U.1) (funext fun x => ?_)
    simp only [colimitCocone, colimit, ← TopCat.comp_app]
    congr
    exact ι_preservesColimitIso_inv (forget C) F (unop X)
  · intro X Y f
    change ((F.map f.unop).c.app _ ≫ _ ≫ _) ≫ (F.obj (unop Y)).presheaf.map _ = _ ≫ _
    rw [TopCat.Presheaf.Pushforward.comp_inv_app]
    erw [Category.id_comp]
    rw [Category.assoc]
    erw [← (F.obj (unop Y)).presheaf.map_comp, (F.map f.unop).c.naturality_assoc,
      ← (F.obj (unop Y)).presheaf.map_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `colimitPresheafObjIsoComponentwiseLimit_inv_ι_app` / 定理 `colimitPresheafObjIsoComponentwiseLimit_inv_ι_app`

English:
theorem colimitPresheafObjIsoComponentwiseLimit_inv_ι_app
  statement: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  proof: by
  delta colimitPresheafObjIsoComponentwiseLimit
  rw [Iso.trans_inv]; rw [Iso.trans_inv]; rw [Iso.app_inv]; rw [sheafIsoOfIso_inv]; rw [pushforwardToOfIso_app]; rw [congr_app (Iso.symm_inv _)]
  dsimp
  rw [map_id]; rw [comp_id]; rw [assoc]; rw [assoc]; rw [assoc]; rw [NatTrans.naturality]; rw [←

中文:
定理 colimitPresheafObjIsoComponentwiseLimit_inv_ι_app
  结论: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  证明: by
  delta colimitPresheafObjIsoComponentwiseLimit
  rw [Iso.trans_inv]; rw [Iso.trans_inv]; rw [Iso.app_inv]; rw [sheafIsoOfIso_inv]; rw [pushforwardToOfIso_app]; rw [congr_app (Iso.symm_inv _)]
  dsimp
  rw [map_id]; rw [comp_id]; rw [assoc]; rw [assoc]; rw [assoc]; rw [NatTrans.naturality]; rw [←

Depends on / 依赖: Iso.app_inv, Iso.symm_inv, Iso.trans_inv, NatTrans, NatTrans.naturality, app_inv, colimit, colimit.isoColimitCocone_, colimitPresheafObjIsoComponentwiseLimit, comp_c_app_assoc, comp_id, congr_app, map_id, naturality, pushforwardToOfIso_app, sheafIsoOfIso_inv, symm_inv, trans_inv
-/
theorem colimitPresheafObjIsoComponentwiseLimit_inv_ι_app (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).inv ≫ (colimit.ι F j).c.app (op U) =
      limit.π _ (op j) := by
  delta colimitPresheafObjIsoComponentwiseLimit
  rw [Iso.trans_inv]; rw [Iso.trans_inv]; rw [Iso.app_inv]; rw [sheafIsoOfIso_inv]; rw [pushforwardToOfIso_app]; rw [congr_app (Iso.symm_inv _)]
  dsimp
  rw [map_id]; rw [comp_id]; rw [assoc]; rw [assoc]; rw [assoc]; rw [NatTrans.naturality]; rw [← comp_c_app_assoc]; rw [congr_app (colimit.isoColimitCocone_ι_hom _ _)]; rw [assoc]; rw [colimitCocone_ι_app_c]; rw [limitObjIsoLimitCompEvaluation_inv_π_app_assoc]; rw [limMap_π_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `colimitPresheafObjIsoComponentwiseLimit_hom_π` / 定理 `colimitPresheafObjIsoComponentwiseLimit_hom_π`

English:
theorem colimitPresheafObjIsoComponentwiseLimit_hom_π
  statement: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  proof: by
  rw [← Iso.eq_inv_comp]; rw [colimitPresheafObjIsoComponentwiseLimit_inv_ι_app]

中文:
定理 colimitPresheafObjIsoComponentwiseLimit_hom_π
  结论: (F : J ⥤ PresheafedSpace.{_, _, v} C)
  证明: by
  rw [← Iso.eq_inv_comp]; rw [colimitPresheafObjIsoComponentwiseLimit_inv_ι_app]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
theorem colimitPresheafObjIsoComponentwiseLimit_hom_π (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).hom ≫ limit.π _ (op j) =
      (colimit.ι F j).c.app (op U) := by
  rw [← Iso.eq_inv_comp]; rw [colimitPresheafObjIsoComponentwiseLimit_inv_ι_app]

end PresheafedSpace

end AlgebraicGeometry
