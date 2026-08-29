/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# `IsRepresentedBy` predicate

In this file we define the predicate `IsRepresentedBy`: A presheaf `F` is represented by `X`
with universal element `x : F.obj X` if the natural transformation `yoneda.obj X ⟶ F` induced
by `x` is an isomorphism.

For other declarations expressing a functor is representable, see also:

- `CategoryTheory.Functor.RepresentableBy`:
  Structure bundling an explicit natural isomorphism `yoneda.obj X ⟶ F`.
- `CategoryTheory.Functor.IsRepresentable`:
  Predicate asserting the existence of a representing object.

The relations to these other notions are given as
`CategoryTheory.Functor.IsRepresentable.iff_exists_isRepresentedBy` and
`CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy`.

## TODOs

- Dualize to `IsCorepresentedBy`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u} [Category.{v} C]

/--
A presheaf `F` is represented by `X` with universal element `x : F.obj X`
if the natural transformation `yoneda.obj X ⟶ F` induced by `x` is an isomorphism.
For better universe generality, we state this manually as for every `Y`, the
induced map `(Y ⟶ X) → F.obj Y` is bijective.
-/
@[mk_iff]
/--
Definition of `IsRepresentedBy` / `IsRepresentedBy` 的定义

English:
structure IsRepresentedBy
  parameters: (F : Cᵒᵖ ⥤ Type w) {X : C} (x : F.obj (op X))
  axioms and operations (1):
    - map_bijective({Y : C}) : Function.Bijective (fun f : Y ⟶ X => F.map f.op x)

中文:
结构 IsRepresentedBy
  参数: (F : Cᵒᵖ ⥤ Type w) {X : C} (x : F.obj (op X))
  公理与运算 (1 个):
    - map_bijective({Y : C}) : Function.Bijective (fun f : Y ⟶ X => F.map f.op x)
-/
structure IsRepresentedBy (F : Cᵒᵖ ⥤ Type w) {X : C} (x : F.obj (op X)) : Prop where
  map_bijective {Y : C} : Function.Bijective (fun f : Y ⟶ X => F.map f.op x)

variable {F : Cᵒᵖ ⥤ Type w} {X : C} {x : F.obj (op X)}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsRepresentedBy.iff_isIso_uliftYonedaEquiv` / 引理 `IsRepresentedBy.iff_isIso_uliftYonedaEquiv`

English:
lemma IsRepresentedBy.iff_isIso_uliftYonedaEquiv
  proof: by
  rw [isRepresentedBy_iff]; rw [NatTrans.isIso_iff_isIso_app]; rw [Opposite.op_surjective.forall]
  refine forall_congr' fun Y => ?_
  rw [isIso_iff_bijective]; rw [← Function.Bijective.of_comp_iff _ Equiv.ulift.{w}.symm.bijective]; rw [← Function.Bijective.of_comp_iff' Equiv.ulift.{v}.bijective]

中文:
引理 IsRepresentedBy.iff_isIso_uliftYonedaEquiv
  证明: by
  rw [isRepresentedBy_iff]; rw [NatTrans.isIso_iff_isIso_app]; rw [Opposite.op_surjective.forall]
  refine forall_congr' fun Y => ?_
  rw [isIso_iff_bijective]; rw [← Function.Bijective.of_comp_iff _ Equiv.ulift.{w}.symm.bijective]; rw [← Function.Bijective.of_comp_iff' Equiv.ulift.{v}.bijective]

Depends on / 依赖: Bijective, Equiv.ulift, Function, Function.Bijective.of_comp_iff, NatTrans, NatTrans.isIso_iff_isIso_app, Opposite, Opposite.op_surjective.forall, bijective, forall_congr, isIso_iff_bijective, isIso_iff_isIso_app, isRepresentedBy_iff, of_comp_iff, op_surjective, symm.bijective, uliftFunctor
-/
lemma IsRepresentedBy.iff_isIso_uliftYonedaEquiv :
    F.IsRepresentedBy x ↔
      IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
  rw [isRepresentedBy_iff]; rw [NatTrans.isIso_iff_isIso_app]; rw [Opposite.op_surjective.forall]
  refine forall_congr' fun Y => ?_
  rw [isIso_iff_bijective]; rw [← Function.Bijective.of_comp_iff _ Equiv.ulift.{w}.symm.bijective]; rw [← Function.Bijective.of_comp_iff' Equiv.ulift.{v}.bijective]
  rfl

/-- If `F` is represented by `X` with universal element `x : F.obj X`, modulo universe
lifting, it is isomorphic to `yoneda.obj X`. -/
@[simps! hom]
/--
Definition of `IsRepresentedBy.uliftYonedaIso` / `IsRepresentedBy.uliftYonedaIso` 的定义

English:
definition IsRepresentedBy.uliftYonedaIso
  signature: (h : F.IsRepresentedBy x)
  body: haveI : IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
    rwa [IsRepresentedBy.iff_isIso_uliftYonedaEquiv] at h
asIso (uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩

中文:
定义 IsRepresentedBy.uliftYonedaIso
  签名: (h : F.IsRepresentedBy x)
  定义体: haveI : IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
    rwa [IsRepresentedBy.iff_isIso_uliftYonedaEquiv] at h
asIso (uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩

Depends on / 依赖: IsRepresentedBy, IsRepresentedBy.iff_isIso_uliftYonedaEquiv, iff_isIso_uliftYonedaEquiv, uliftFunctor, uliftYonedaEquiv
-/
noncomputable def IsRepresentedBy.uliftYonedaIso (h : F.IsRepresentedBy x) :
    uliftYoneda.obj X ≅ F ⋙ uliftFunctor.{v} :=
  haveI : IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
    rwa [IsRepresentedBy.iff_isIso_uliftYonedaEquiv] at h
asIso (uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩

/--
Definition of `IsRepresentedBy.representableBy` / `IsRepresentedBy.representableBy` 的定义

English:
definition IsRepresentedBy.representableBy
  signature: (h : F.IsRepresentedBy x)
  body: Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYonedaIso _ _).symm <| h.uliftYonedaIso)

@[simp]

中文:
定义 IsRepresentedBy.representableBy
  签名: (h : F.IsRepresentedBy x)
  定义体: Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYonedaIso _ _).symm <| h.uliftYonedaIso)

@[simp]

Depends on / 依赖: Functor, Functor.representableByUliftFunctorEquiv, RepresentableBy, RepresentableBy.equivUliftYonedaIso, equivUliftYonedaIso, h.uliftYonedaIso, representableByUliftFunctorEquiv, uliftYonedaIso
-/
noncomputable def IsRepresentedBy.representableBy (h : F.IsRepresentedBy x) :
    F.RepresentableBy X :=
  Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYonedaIso _ _).symm <| h.uliftYonedaIso)

@[simp]
/--
lemma `IsRepresentedBy.representableBy_homEquiv_apply` / 引理 `IsRepresentedBy.representableBy_homEquiv_apply`

English:
lemma IsRepresentedBy.representableBy_homEquiv_apply
  statement: (h : F.IsRepresentedBy x)
  proof: rfl

中文:
引理 IsRepresentedBy.representableBy_homEquiv_apply
  结论: (h : F.IsRepresentedBy x)
  证明: rfl
-/
lemma IsRepresentedBy.representableBy_homEquiv_apply (h : F.IsRepresentedBy x)
    {Y : C} (f : Y ⟶ X) :
    h.representableBy.homEquiv f = F.map f.op x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `RepresentableBy.isRepresentedBy` / 引理 `RepresentableBy.isRepresentedBy`

English:
lemma RepresentableBy.isRepresentedBy
  given: (R : F.RepresentableBy X)
  proof: by
  rw [IsRepresentedBy.iff_isIso_uliftYonedaEquiv]
  convert!
    (RepresentableBy.equivUliftYonedaIso _ _ <|
        representableByUliftFunctorEquiv.{v}.symm R).isIso_hom
  ext
  simpa [uliftYonedaEquiv] using (homEquiv_eq _ _).symm

中文:
引理 RepresentableBy.isRepresentedBy
  条件: (R : F.RepresentableBy X)
  证明: by
  rw [IsRepresentedBy.iff_isIso_uliftYonedaEquiv]
  convert!
    (RepresentableBy.equivUliftYonedaIso _ _ <|
        representableByUliftFunctorEquiv.{v}.symm R).isIso_hom
  ext
  simpa [uliftYonedaEquiv] using (homEquiv_eq _ _).symm

Depends on / 依赖: IsRepresentedBy, IsRepresentedBy.iff_isIso_uliftYonedaEquiv, RepresentableBy, RepresentableBy.equivUliftYonedaIso, convert, equivUliftYonedaIso, homEquiv_eq, iff_isIso_uliftYonedaEquiv, isIso_hom, representableByUliftFunctorEquiv, uliftYonedaEquiv
-/
lemma RepresentableBy.isRepresentedBy (R : F.RepresentableBy X) :
    F.IsRepresentedBy (R.homEquiv (𝟙 X)) := by
  rw [IsRepresentedBy.iff_isIso_uliftYonedaEquiv]
  convert!
    (RepresentableBy.equivUliftYonedaIso _ _ <|
        representableByUliftFunctorEquiv.{v}.symm R).isIso_hom
  ext
  simpa [uliftYonedaEquiv] using (homEquiv_eq _ _).symm

/--
lemma `IsRepresentedBy.iff_exists_representableBy` / 引理 `IsRepresentedBy.iff_exists_representableBy`

English:
lemma IsRepresentedBy.iff_exists_representableBy
  proof: ⟨fun h => ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ => h ▸ R.isRepresentedBy⟩

中文:
引理 IsRepresentedBy.iff_exists_representableBy
  证明: ⟨fun h => ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ => h ▸ R.isRepresentedBy⟩

Depends on / 依赖: R.isRepresentedBy, h.representableBy, isRepresentedBy, representableBy
-/
lemma IsRepresentedBy.iff_exists_representableBy :
    F.IsRepresentedBy x ↔ exists (R : F.RepresentableBy X), R.homEquiv (𝟙 X) = x :=
  ⟨fun h => ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ => h ▸ R.isRepresentedBy⟩

/--
lemma `IsRepresentedBy.of_natIso` / 引理 `IsRepresentedBy.of_natIso`

English:
lemma IsRepresentedBy.of_natIso
  statement: (h : F.IsRepresentedBy x) {F' : Cᵒᵖ ⥤ Type w}
  proof: by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIso e
  simp [RepresentableBy.ofIso]

中文:
引理 IsRepresentedBy.of_natIso
  结论: (h : F.IsRepresentedBy x) {F' : Cᵒᵖ ⥤ Type w}
  证明: by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIso e
  simp [RepresentableBy.ofIso]

Depends on / 依赖: RepresentableBy, RepresentableBy.ofIso, h.representableBy.ofIso, iff_exists_representableBy, representableBy
-/
lemma IsRepresentedBy.of_natIso (h : F.IsRepresentedBy x) {F' : Cᵒᵖ ⥤ Type w}
    (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIso e
  simp [RepresentableBy.ofIso]

/--
lemma `IsRepresentedBy.iff_natIso` / 引理 `IsRepresentedBy.iff_natIso`

English:
lemma IsRepresentedBy.iff_natIso
  given: {F' : Cᵒᵖ ⥤ Type w} (e : F ≅ F')
  proof: ⟨fun h => by simpa using h.of_natIso e.symm, fun h => .of_natIso h _⟩

中文:
引理 IsRepresentedBy.iff_natIso
  条件: {F' : Cᵒᵖ ⥤ Type w} (e : F ≅ F')
  证明: ⟨fun h => by simpa using h.of_natIso e.symm, fun h => .of_natIso h _⟩

Depends on / 依赖: e.symm, h.of_natIso, of_natIso
-/
lemma IsRepresentedBy.iff_natIso {F' : Cᵒᵖ ⥤ Type w} (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) ↔ F.IsRepresentedBy x :=
  ⟨fun h => by simpa using h.of_natIso e.symm, fun h => .of_natIso h _⟩

/--
lemma `IsRepresentedBy.of_isoObj` / 引理 `IsRepresentedBy.of_isoObj`

English:
lemma IsRepresentedBy.of_isoObj
  given: (h : F.IsRepresentedBy x) {Y : C} (e : Y ≅ X)
  proof: by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIsoObj e
  simp

中文:
引理 IsRepresentedBy.of_isoObj
  条件: (h : F.IsRepresentedBy x) {Y : C} (e : Y ≅ X)
  证明: by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIsoObj e
  simp

Depends on / 依赖: h.representableBy.ofIsoObj, iff_exists_representableBy, ofIsoObj, representableBy
-/
lemma IsRepresentedBy.of_isoObj (h : F.IsRepresentedBy x) {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIsoObj e
  simp

/--
lemma `IsRepresentedBy.iff_of_isoObj` / 引理 `IsRepresentedBy.iff_of_isoObj`

English:
lemma IsRepresentedBy.iff_of_isoObj
  given: {Y : C} (e : Y ≅ X)
  proof: by
  refine ⟨fun h => ?_, fun h => h.of_isoObj e⟩
  have : x = F.map e.inv.op (F.map e.hom.op x) := by
    simp [← comp_apply, ← map_comp, ← op_comp]
  exact this ▸ .of_isoObj h e.symm

中文:
引理 IsRepresentedBy.iff_of_isoObj
  条件: {Y : C} (e : Y ≅ X)
  证明: by
  refine ⟨fun h => ?_, fun h => h.of_isoObj e⟩
  have : x = F.map e.inv.op (F.map e.hom.op x) := by
    simp [← comp_apply, ← map_comp, ← op_comp]
  exact this ▸ .of_isoObj h e.symm

Depends on / 依赖: F.map, comp_apply, e.hom.op, e.inv.op, e.symm, h.of_isoObj, map_comp, of_isoObj, op_comp
-/
lemma IsRepresentedBy.iff_of_isoObj {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) ↔ F.IsRepresentedBy x := by
  refine ⟨fun h => ?_, fun h => h.of_isoObj e⟩
  have : x = F.map e.inv.op (F.map e.hom.op x) := by
    simp [← comp_apply, ← map_comp, ← op_comp]
  exact this ▸ .of_isoObj h e.symm

/--
lemma `IsRepresentedBy.of_isRepresentable` / 引理 `IsRepresentedBy.of_isRepresentable`

English:
lemma IsRepresentedBy.of_isRepresentable
  given: [F.IsRepresentable]
  statement: F.IsRepresentedBy F.reprx
  proof: F.representableBy.isRepresentedBy

中文:
引理 IsRepresentedBy.of_isRepresentable
  条件: [F.IsRepresentable]
  结论: F.IsRepresentedBy F.reprx
  证明: F.representableBy.isRepresentedBy

Depends on / 依赖: F.representableBy.isRepresentedBy, isRepresentedBy, representableBy
-/
lemma IsRepresentedBy.of_isRepresentable [F.IsRepresentable] : F.IsRepresentedBy F.reprx :=
  F.representableBy.isRepresentedBy

/--
lemma `IsRepresentable.iff_exists_isRepresentedBy` / 引理 `IsRepresentable.iff_exists_isRepresentedBy`

English:
lemma IsRepresentable.iff_exists_isRepresentedBy
  proof: ⟨fun _ => ⟨F.reprX, F.reprx, .of_isRepresentable⟩,
    fun ⟨_, _, h⟩ => h.representableBy.isRepresentable⟩

中文:
引理 IsRepresentable.iff_exists_isRepresentedBy
  证明: ⟨fun _ => ⟨F.reprX, F.reprx, .of_isRepresentable⟩,
    fun ⟨_, _, h⟩ => h.representableBy.isRepresentable⟩

Depends on / 依赖: F.reprX, F.reprx, h.representableBy.isRepresentable, isRepresentable, of_isRepresentable, representableBy
-/
lemma IsRepresentable.iff_exists_isRepresentedBy :
    F.IsRepresentable ↔ exists (X : C) (x : F.obj (op X)), F.IsRepresentedBy x :=
  ⟨fun _ => ⟨F.reprX, F.reprx, .of_isRepresentable⟩,
    fun ⟨_, _, h⟩ => h.representableBy.isRepresentable⟩

end CategoryTheory.Functor
