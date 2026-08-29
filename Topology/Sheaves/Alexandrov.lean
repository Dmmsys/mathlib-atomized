/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Curry, Adam Topaz
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

/-!

Let `X` be a preorder `≤`, and consider the associated Alexandrov topology on `X`.
Given a functor `F : X ⥤ C` to a complete category, we can extend `F` to a
presheaf on (the topological space) `X` by taking the right Kan extension along the canonical
functor `X ⥤ (Opens X)ᵒᵖ` sending `x : X` to the principal open `{y | x ≤ y}` in the
Alexandrov topology.

This file proves that this presheaf is a sheaf.

-/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory Limits Functor
open TopCat Presheaf SheafCondition
open TopologicalSpace Topology

variable
  {X : Type v} [TopologicalSpace X] [Preorder X] [Topology.IsUpperSet X]
  {C : Type u} [Category.{v} C] [HasLimits C]
  (F : X ⥤ C)

namespace Alexandrov

/--
Definition of `principalOpen` / `principalOpen` 的定义

English:
definition principalOpen
  signature: (x : X)
  body: .mk { y | x <= y } by
  rw [IsUpperSet.isOpen_iff_isUpperSet]
  intro y z h1 h2
  exact le_trans h2 h1

中文:
定义 principalOpen
  签名: (x : X)
  定义体: .mk { y | x <= y } by
  rw [IsUpperSet.isOpen_iff_isUpperSet]
  intro y z h1 h2
  exact le_trans h2 h1

Depends on / 依赖: IsUpperSet, IsUpperSet.isOpen_iff_isUpperSet, isOpen_iff_isUpperSet, le_trans
-/
def principalOpen (x : X) : Opens X := .mk { y | x <= y } by
  rw [IsUpperSet.isOpen_iff_isUpperSet]
  intro y z h1 h2
  exact le_trans h2 h1

/--
lemma `self_mem_principalOpen` / 引理 `self_mem_principalOpen`

English:
lemma self_mem_principalOpen
  given: (x : X)
  statement: x in principalOpen x
  proof: le_refl _

@[simp]

中文:
引理 self_mem_principalOpen
  条件: (x : X)
  结论: x in principalOpen x
  证明: le_refl _

@[simp]

Depends on / 依赖: le_refl
-/
lemma self_mem_principalOpen (x : X) : x in principalOpen x := le_refl _

@[simp]
/--
lemma `principalOpen_le_iff` / 引理 `principalOpen_le_iff`

English:
lemma principalOpen_le_iff
  given: {x : X} (U : Opens X)
  proof: by
refine ⟨fun h => h self_mem_principalOpen _, fun hx y hy => ?_⟩
  · have := U.isOpen
    rw [IsUpperSet.isOpen_iff_isUpperSet] at this
    exact this hy hx

中文:
引理 principalOpen_le_iff
  条件: {x : X} (U : Opens X)
  证明: by
refine ⟨fun h => h self_mem_principalOpen _, fun hx y hy => ?_⟩
  · have := U.isOpen
    rw [IsUpperSet.isOpen_iff_isUpperSet] at this
    exact this hy hx

Depends on / 依赖: IsUpperSet, IsUpperSet.isOpen_iff_isUpperSet, U.isOpen, isOpen, isOpen_iff_isUpperSet, self_mem_principalOpen
-/
lemma principalOpen_le_iff {x : X} (U : Opens X) :
    principalOpen x <= U ↔ x in U := by
refine ⟨fun h => h self_mem_principalOpen _, fun hx y hy => ?_⟩
  · have := U.isOpen
    rw [IsUpperSet.isOpen_iff_isUpperSet] at this
    exact this hy hx

/--
lemma `principalOpen_le` / 引理 `principalOpen_le`

English:
lemma principalOpen_le
  given: {x y : X} (h : x <= y)
  proof: fun _ hc => le_trans h hc

中文:
引理 principalOpen_le
  条件: {x y : X} (h : x <= y)
  证明: fun _ hc => le_trans h hc

Depends on / 依赖: le_trans
-/
lemma principalOpen_le {x y : X} (h : x <= y) :
    principalOpen y <= principalOpen x :=
  fun _ hc => le_trans h hc

variable (X) in
/-- The functor sending `x : X` to the principal open associated with `x`. -/
@[simps]
/--
Definition of `principals` / `principals` 的定义

English:
definition principals
  signature: : X ⥤ (Opens X)ᵒᵖ where
  body: .op principalOpen x
map {x y} f := .op .hom principalOpen_le f.le

中文:
定义 principals
  签名: : X ⥤ (Opens X)ᵒᵖ where
  定义体: .op principalOpen x
map {x y} f := .op .hom principalOpen_le f.le

Depends on / 依赖: principalOpen
-/
def principals : X ⥤ (Opens X)ᵒᵖ where
obj x := .op principalOpen x
map {x y} f := .op .hom principalOpen_le f.le

/--
lemma `exists_le_of_le_sup` / 引理 `exists_le_of_le_sup`

English:
lemma exists_le_of_le_sup
  statement: {ι : Type v} {x : X}
  proof: by
  grind [principalOpen_le_iff, Opens.mem_iSup]

中文:
引理 存在_le_of_le_sup
  结论: {ι : 类型v} {x : X}
  证明: by
  grind [principalOpen_le_iff, Opens.mem_iSup]

Depends on / 依赖: Opens.mem_iSup, mem_iSup, principalOpen_le_iff
-/
lemma exists_le_of_le_sup {ι : Type v} {x : X}
    (Us : ι -> Opens X) (h : principalOpen x <= iSup Us) :
    exists i : ι, principalOpen x <= Us i := by
  grind [principalOpen_le_iff, Opens.mem_iSup]

/--
Definition of `principalsKanExtension` / `principalsKanExtension` 的定义

English:
abbreviation principalsKanExtension
  signature: : (Opens X)ᵒᵖ ⥤ C
  body: (principals X).pointwiseRightKanExtension F

中文:
缩写 principalsKanExtension
  签名: : (Opens X)ᵒᵖ ⥤ C
  定义体: (principals X).pointwiseRightKanExtension F

Depends on / 依赖: pointwiseRightKanExtension, principals
-/
abbrev principalsKanExtension : (Opens X)ᵒᵖ ⥤ C :=
  (principals X).pointwiseRightKanExtension F

/--
Definition of `generator` / `generator` 的定义

English:
abbreviation generator
  signature: (U : Opens X)
  body: StructuredArrow.proj (.op U) (principals X)

中文:
缩写 generator
  签名: (U : Opens X)
  定义体: StructuredArrow.proj (.op U) (principals X)

Depends on / 依赖: StructuredArrow, StructuredArrow.proj, principals
-/
abbrev generator (U : Opens X) :
    StructuredArrow (.op U) (principals X) ⥤ X :=
  StructuredArrow.proj (.op U) (principals X)

/-- Given a structured arrow `f` with domain `iSup Us` over `principals X`,
where `Us` is a family of `Opens X`, this functor sends `f` to the principal open
associated with it, considered as an object in the full subcategory of all `V : Opens X`
such that `V ≤ Us i` for some `i`.

This definition is primarily meant to be used in `lowerCone`, and `isLimit` below.
-/
@[simps]
/--
Definition of `projSup` / `projSup` 的定义

English:
definition projSup
  signature: {ι : Type v} (Us : ι -> Opens X)
  body: .op .mk (principalOpen f.right) exists_le_of_le_sup Us f.hom.unop.le
  map e := (ObjectProperty.homMk (homOfLE (principalOpen_le e.right.le))).op

中文:
定义 projSup
  签名: {ι : 类型v} (Us : ι -> Opens X)
  定义体: .op .mk (principalOpen f.right) exists_le_of_le_sup Us f.hom.unop.le
  map e := (ObjectProperty.homMk (homOfLE (principalOpen_le e.right.le))).op
-/
def projSup {ι : Type v} (Us : ι -> Opens X) :
    StructuredArrow (.op <| iSup Us) (principals X) ⥤
      (OpensLeCover (X := .of X) Us)ᵒᵖ where
obj f := .op .mk (principalOpen f.right) exists_le_of_le_sup Us f.hom.unop.le
  map e := (ObjectProperty.homMk (homOfLE (principalOpen_le e.right.le))).op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
/-- This is an auxiliary definition which is only meant to be used in `isLimit` below. -/
@[simps]
/--
Definition of `lowerCone` / `lowerCone` 的定义

English:
definition lowerCone
  body: S.pt
  π := {
    app := fun f =>
      S.π.app ((projSup Us).obj f) ≫ limit.π (generator (principalOpen f.right) ⋙ F)
        ⟨.mk .unit, f.right, 𝟙 _⟩
    naturality := by
      rintro x y e
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
        Functor.op_obj, Functor.pointwiseRightKanExtension_obj,
        Category.id_comp, Functor.comp_map, Category.assoc]
      rw [← S.w ((projSup Us).map e)]; rw [Category.assoc]
      congr 1
      let xx : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
        ⟨.mk .unit, x.right, 𝟙 _⟩
      let yy : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
⟨.mk .unit, y.right, .op LE.le.hom principalOpen_le e.right.le⟩
      let ee : xx ⟶ yy := { left := 𝟙 _, right := e.right }
      exact (limit.lift_π _ _).trans (limit.w
        (StructuredArrow.proj _ (principals X) ⋙ F) ee).symm
  }

中文:
定义 lowerCone
  定义体: S.pt
  π := {
    app := fun f =>
      S.π.app ((projSup Us).obj f) ≫ limit.π (generator (principalOpen f.right) ⋙ F)
        ⟨.mk .unit, f.right, 𝟙 _⟩
    naturality := by
      rintro x y e
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
        Functor.op_obj, Functor.pointwiseRightKanExtension_obj,
        Category.id_comp, Functor.comp_map, Category.assoc]
      rw [← S.w ((projSup Us).map e)]; rw [Category.assoc]
      congr 1
      let xx : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
        ⟨.mk .unit, x.right, 𝟙 _⟩
      let yy : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
⟨.mk .unit, y.right, .op LE.le.hom principalOpen_le e.right.le⟩
      let ee : xx ⟶ yy := { left := 𝟙 _, right := e.right }
      exact (limit.lift_π _ _).trans (limit.w
        (StructuredArrow.proj _ (principals X) ⋙ F) ee).symm
  }
-/
def lowerCone
    {α : Type v} (Us : α -> Opens X)
    (S : Cone ((ObjectProperty.ι _ : OpensLeCover (X := .of X) Us ⥤ _).op ⋙
      principalsKanExtension F)) :
    Cone (generator (iSup Us) ⋙ F) where
  pt := S.pt
  π := {
    app := fun f =>
      S.π.app ((projSup Us).obj f) ≫ limit.π (generator (principalOpen f.right) ⋙ F)
        ⟨.mk .unit, f.right, 𝟙 _⟩
    naturality := by
      rintro x y e
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
        Functor.op_obj, Functor.pointwiseRightKanExtension_obj,
        Category.id_comp, Functor.comp_map, Category.assoc]
      rw [← S.w ((projSup Us).map e)]; rw [Category.assoc]
      congr 1
      let xx : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
        ⟨.mk .unit, x.right, 𝟙 _⟩
      let yy : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
⟨.mk .unit, y.right, .op LE.le.hom principalOpen_le e.right.le⟩
      let ee : xx ⟶ yy := { left := 𝟙 _, right := e.right }
      exact (limit.lift_π _ _).trans (limit.w
        (StructuredArrow.proj _ (principals X) ⋙ F) ee).symm
  }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimit` / `isLimit` 的定义

English:
definition isLimit
  signature: {X : TopCat.{v}} [Preorder X] [Topology.IsUpperSet X]
  body: limit.lift _ (lowerCone Us S)
  fac := by
    rintro S ⟨V, i, hV⟩
    dsimp [forget, opensLeCoverCocone]
    ext ⟨_, x, f⟩
    simp only [Category.assoc, limit.lift_π, lowerCone_pt, lowerCone_π_app, const_obj_obj,
      projSup_obj, StructuredArrow.map_obj_right, comp_obj, op_obj, pointwiseRightKanExtension_obj,
      StructuredArrow.proj_obj]
    have e : principalOpen x <= V := f.unop.le
    let VV : OpensLeCover Us := ⟨V, i, hV⟩
    let xx : OpensLeCover Us := ⟨principalOpen x, i, le_trans e hV⟩
    let ee : xx ⟶ VV := ObjectProperty.homMk e.hom
    rw [← S.w ee.op]; rw [Category.assoc]
    congr 1
    exact (limit.lift_π _ _).trans (by aesop)
  uniq := by
    intro S m hm
    dsimp
    symm
    ext ⟨_, x, f⟩
    simp only [lowerCone_pt, comp_obj, limit.lift_π, lowerCone_π_app, const_obj_obj, projSup_obj,
      op_obj, pointwiseRightKanExtension_obj]
    specialize hm ⟨principalOpen x, ?_⟩
    · apply exists_le_of_le_sup
      exact f.unop.le
    · rw [← hm]
      simp only [Category.assoc]
      congr
      apply limit.lift_π

中文:
定义 isLimit
  签名: {X : 顶元素范畴.{v}} [预序 X] [拓扑.是上集 X]
  定义体: limit.lift _ (lowerCone Us S)
  fac := by
    rintro S ⟨V, i, hV⟩
    dsimp [forget, opensLeCoverCocone]
    ext ⟨_, x, f⟩
    simp only [Category.assoc, limit.lift_π, lowerCone_pt, lowerCone_π_app, const_obj_obj,
      projSup_obj, StructuredArrow.map_obj_right, comp_obj, op_obj, pointwiseRightKanExtension_obj,
      StructuredArrow.proj_obj]
    have e : principalOpen x <= V := f.unop.le
    let VV : OpensLeCover Us := ⟨V, i, hV⟩
    let xx : OpensLeCover Us := ⟨principalOpen x, i, le_trans e hV⟩
    let ee : xx ⟶ VV := ObjectProperty.homMk e.hom
    rw [← S.w ee.op]; rw [Category.assoc]
    congr 1
    exact (limit.lift_π _ _).trans (by aesop)
  uniq := by
    intro S m hm
    dsimp
    symm
    ext ⟨_, x, f⟩
    simp only [lowerCone_pt, comp_obj, limit.lift_π, lowerCone_π_app, const_obj_obj, projSup_obj,
      op_obj, pointwiseRightKanExtension_obj]
    specialize hm ⟨principalOpen x, ?_⟩
    · apply exists_le_of_le_sup
      exact f.unop.le
    · rw [← hm]
      simp only [Category.assoc]
      congr
      apply limit.lift_π

Depends on / 依赖: limit.lift, lowerCone
-/
def isLimit {X : TopCat.{v}} [Preorder X] [Topology.IsUpperSet X]
    (F : X ⥤ C)
    (α : Type v) (Us : α -> Opens X) :
    IsLimit (mapCone (principalsKanExtension F) (opensLeCoverCocone Us).op) where
  lift S := limit.lift _ (lowerCone Us S)
  fac := by
    rintro S ⟨V, i, hV⟩
    dsimp [forget, opensLeCoverCocone]
    ext ⟨_, x, f⟩
    simp only [Category.assoc, limit.lift_π, lowerCone_pt, lowerCone_π_app, const_obj_obj,
      projSup_obj, StructuredArrow.map_obj_right, comp_obj, op_obj, pointwiseRightKanExtension_obj,
      StructuredArrow.proj_obj]
    have e : principalOpen x <= V := f.unop.le
    let VV : OpensLeCover Us := ⟨V, i, hV⟩
    let xx : OpensLeCover Us := ⟨principalOpen x, i, le_trans e hV⟩
    let ee : xx ⟶ VV := ObjectProperty.homMk e.hom
    rw [← S.w ee.op]; rw [Category.assoc]
    congr 1
    exact (limit.lift_π _ _).trans (by aesop)
  uniq := by
    intro S m hm
    dsimp
    symm
    ext ⟨_, x, f⟩
    simp only [lowerCone_pt, comp_obj, limit.lift_π, lowerCone_π_app, const_obj_obj, projSup_obj,
      op_obj, pointwiseRightKanExtension_obj]
    specialize hm ⟨principalOpen x, ?_⟩
    · apply exists_le_of_le_sup
      exact f.unop.le
    · rw [← hm]
      simp only [Category.assoc]
      congr
      apply limit.lift_π

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isSheaf_principalsKanExtension` / 定理 `isSheaf_principalsKanExtension`

English:
theorem isSheaf_principalsKanExtension
  proof: by
  rw [isSheaf_iff_isSheafOpensLeCover]
  intro ι Us
  constructor
  apply isLimit

中文:
定理 isSheaf_principalsKanExtension
  证明: by
  rw [isSheaf_iff_isSheafOpensLeCover]
  intro ι Us
  constructor
  apply isLimit

Depends on / 依赖: isLimit, isSheaf_iff_isSheafOpensLeCover
-/
theorem isSheaf_principalsKanExtension
    {X : TopCat.{v}} [Preorder X] [Topology.IsUpperSet X] (F : X ⥤ C) :
    Presheaf.IsSheaf (principalsKanExtension F) := by
  rw [isSheaf_iff_isSheafOpensLeCover]
  intro ι Us
  constructor
  apply isLimit

end Alexandrov

open Alexandrov

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Topology.IsUpperSet.isSheaf_of_isRightKanExtension` / 定理 `Topology.IsUpperSet.isSheaf_of_isRightKanExtension`

English:
theorem Topology.IsUpperSet.isSheaf_of_isRightKanExtension
  proof: by
  let γ : principals X ⋙ principalsKanExtension F ⟶ F :=
    (principals X).pointwiseRightKanExtensionCounit F
  let _ : (principalsKanExtension F).IsRightKanExtension γ := inferInstance
  have : P ≅ principalsKanExtension F :=
    @rightKanExtensionUnique _ _ _ _ _ _ _ _ _ _ (by assumption) _ _ (by assumption)
  change TopCat.Presheaf.IsSheaf (X := TopCat.of X) P
  rw [isSheaf_iso_iff this]
  exact isSheaf_principalsKanExtension (X := TopCat.of X) F

中文:
定理 拓扑.是上集.isSheaf_of_isRightKanExtension
  证明: by
  let γ : principals X ⋙ principalsKanExtension F ⟶ F :=
    (principals X).pointwiseRightKanExtensionCounit F
  let _ : (principalsKanExtension F).IsRightKanExtension γ := inferInstance
  have : P ≅ principalsKanExtension F :=
    @rightKanExtensionUnique _ _ _ _ _ _ _ _ _ _ (by assumption) _ _ (by assumption)
  change TopCat.Presheaf.IsSheaf (X := TopCat.of X) P
  rw [isSheaf_iso_iff this]
  exact isSheaf_principalsKanExtension (X := TopCat.of X) F

Depends on / 依赖: IsRightKanExtension, IsSheaf, Presheaf, TopCat, TopCat.Presheaf.IsSheaf, TopCat.of, isSheaf_iso_iff, isSheaf_principalsKanExtension, pointwiseRightKanExtensionCounit, principals, principalsKanExtension, rightKanExtensionUnique
-/
theorem Topology.IsUpperSet.isSheaf_of_isRightKanExtension
    (P : (Opens X)ᵒᵖ ⥤ C)
    (η : Alexandrov.principals X ⋙ P ⟶ F)
    [P.IsRightKanExtension η] :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) P := by
  let γ : principals X ⋙ principalsKanExtension F ⟶ F :=
    (principals X).pointwiseRightKanExtensionCounit F
  let _ : (principalsKanExtension F).IsRightKanExtension γ := inferInstance
  have : P ≅ principalsKanExtension F :=
    @rightKanExtensionUnique _ _ _ _ _ _ _ _ _ _ (by assumption) _ _ (by assumption)
  change TopCat.Presheaf.IsSheaf (X := TopCat.of X) P
  rw [isSheaf_iso_iff this]
  exact isSheaf_principalsKanExtension (X := TopCat.of X) F
