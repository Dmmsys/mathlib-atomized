/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Alternative constructor for points

Let `J` be a Grothendieck topology on a category `C`. We provide a constructor
`Point.ofIsCofiltered` for points for `J` which takes as inputs:
- a functor `p : N ⥤ C` where `N` is cofiltered and initially small
- the assumption that for any covering sieve `R` of `X`,
  any morphism `f : p.obj U ⟶ X`, there exists a morphism `g : Y ⟶ X` in `R`,
  a morphism `q : V ⟶ U` in `N` and a morphism `a : p.obj V ⟶ Y` such
  that `a ≫ g = p.map q ≫ f`.
We show that the fiber of a presheaf for the constructed point identifies
to a colimit indexed by the category `N`.

-/

@[expose] public section

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]

variable [LocallySmall.{w} C] {N : Type u'} [Category.{v'} N]
  (p : N ⥤ C) [InitiallySmall.{w} N]
  {J : GrothendieckTopology C}

namespace ofIsCofiltered

local instance : HasColimitsOfShape Nᵒᵖ (Type w) :=
  hasColimitsOfShape_of_finallySmall _ _

/--
Definition of `fiber` / `fiber` 的定义

English:
definition fiber
  signature: : C ⥤ Type w
  body: shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

中文:
定义 fiber
  签名: : C ⥤ 类型 w
  定义体: shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

Depends on / 依赖: Functor, Functor.whiskeringLeft, p.op, shrinkYoneda, whiskeringLeft
-/
noncomputable def fiber : C ⥤ Type w :=
  shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

variable {p} in
/--
Definition of `fiberMk` / `fiberMk` 的定义

English:
definition fiberMk
  signature: {U : N} {X : C} (f : p.obj U ⟶ X)
  body: colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj X) (op U)
    (shrinkYonedaObjObjEquiv.symm f)

中文:
定义 fiberMk
  签名: {U : N} {X : C} (f : p.obj U ⟶ X)
  定义体: colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj X) (op U)
    (shrinkYonedaObjObjEquiv.symm f)

Depends on / 依赖: colimit, p.op, shrinkYoneda, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm
-/
noncomputable def fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) : (fiber.{w} p).obj X :=
  colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj X) (op U)
    (shrinkYonedaObjObjEquiv.symm f)

variable {p} in
/--
lemma `fiberMk_jointly_surjective` / 引理 `fiberMk_jointly_surjective`

English:
lemma fiberMk_jointly_surjective
  given: {X : C} (x : (fiber.{w} p).obj X)
  proof: by
  obtain ⟨U, f, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) x
  obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
  exact ⟨U.unop, f, rfl⟩

中文:
引理 fiberMk_jointly_surjective
  条件: {X : C} (x : (fiber.{w} p).obj X)
  证明: by
  obtain ⟨U, f, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) x
  obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
  exact ⟨U.unop, f, rfl⟩

Depends on / 依赖: Types.jointly_surjective_of_isColimit, U.unop, colimit, colimit.isColimit, isColimit, jointly_surjective_of_isColimit, p.op, shrinkYoneda, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm.surjective, surjective
-/
lemma fiberMk_jointly_surjective {X : C} (x : (fiber.{w} p).obj X) :
    exists (U : N) (f : p.obj U ⟶ X), fiberMk f = x := by
  obtain ⟨U, f, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) x
  obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
  exact ⟨U.unop, f, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {p} in
/--
lemma `exists_of_fiberMk_eq_fiberMk` / 引理 `exists_of_fiberMk_eq_fiberMk`

English:
lemma exists_of_fiberMk_eq_fiberMk
  statement: [IsCofiltered N]
  proof: by
  obtain ⟨V, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simpa [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using hg

中文:
引理 存在_of_fiberMk_eq_fiberMk
  结论: [是余filtered N]
  证明: by
  obtain ⟨V, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simpa [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using hg

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimit_eq_iff, V.unop, colimit, colimit.isColimit, g.unop, isColimit, isColimit_eq_iff, p.op, shrinkYoneda, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
-/
lemma exists_of_fiberMk_eq_fiberMk [IsCofiltered N]
    {U : N} {X : C} {f₁ f₂ : p.obj U ⟶ X} (hf : fiberMk f₁ = fiberMk f₂) :
    exists (V : N) (g : V ⟶ U), p.map g ≫ f₁ = p.map g ≫ f₂ := by
  obtain ⟨V, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simpa [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `fiberMk_map_comp` / 引理 `fiberMk_map_comp`

English:
lemma fiberMk_map_comp
  given: {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X)
  proof: by
  simp [fiberMk, ← dsimp% congr_hom (colimit.w (p.op ⋙ shrinkYoneda.{w}.obj X) g.op)
        (shrinkYonedaObjObjEquiv.symm f),
    fiber, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

@[simp]

中文:
引理 fiberMk_map_comp
  条件: {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X)
  证明: by
  simp [fiberMk, ← dsimp% congr_hom (colimit.w (p.op ⋙ shrinkYoneda.{w}.obj X) g.op)
        (shrinkYonedaObjObjEquiv.symm f),
    fiber, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

@[simp]

Depends on / 依赖: colimit, colimit.w, congr_hom, fiberMk, g.op, p.op, shrinkYoneda, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
-/
lemma fiberMk_map_comp {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X) :
    fiberMk.{w} (p.map g ≫ f) = fiberMk.{w} f := by
  simp [fiberMk, ← dsimp% congr_hom (colimit.w (p.op ⋙ shrinkYoneda.{w}.obj X) g.op)
        (shrinkYonedaObjObjEquiv.symm f),
    fiber, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

@[simp]
/--
lemma `fiberMk_map` / 引理 `fiberMk_map`

English:
lemma fiberMk_map
  given: {U V : N} (g : V ⟶ U)
  proof: by
  simpa using fiberMk_map_comp (p := p) g (𝟙 (p.obj U))

中文:
引理 fiberMk_map
  条件: {U V : N} (g : V ⟶ U)
  证明: by
  simpa using fiberMk_map_comp (p := p) g (𝟙 (p.obj U))

Depends on / 依赖: fiberMk_map_comp, p.obj
-/
lemma fiberMk_map {U V : N} (g : V ⟶ U) :
    fiberMk.{w} (p.map g) = fiberMk.{w} (𝟙 (p.obj U)) := by
  simpa using fiberMk_map_comp (p := p) g (𝟙 (p.obj U))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `fiber_map_fiberMk` / 引理 `fiber_map_fiberMk`

English:
lemma fiber_map_fiberMk
  given: {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y)
  proof: (congr_hom (ι_colimMap (p.op.whiskerLeft (shrinkYoneda.{w}.map g)) (op U))
    (shrinkYonedaObjObjEquiv.symm f)).trans (by
      simp [fiberMk, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])

中文:
引理 fiber_map_fiberMk
  条件: {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y)
  证明: (congr_hom (ι_colimMap (p.op.whiskerLeft (shrinkYoneda.{w}.map g)) (op U))
    (shrinkYonedaObjObjEquiv.symm f)).trans (by
      simp [fiberMk, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])

Depends on / 依赖: congr_hom, fiberMk, p.op.whiskerLeft, shrinkYoneda, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm, whiskerLeft
-/
lemma fiber_map_fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y) :
    (fiber p).map g (fiberMk.{w} f) = fiberMk.{w} (f ≫ g) :=
  (congr_hom (ι_colimMap (p.op.whiskerLeft (shrinkYoneda.{w}.map g)) (op U))
    (shrinkYonedaObjObjEquiv.symm f)).trans (by
      simp [fiberMk, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])

/-- A functor `N ⥤ (fiber p).Elements` which is initial when `N`
is cofiltered and initially small. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : N ⥤ (fiber.{w} p).Elements where
  body: Functor.elementsMk _ (p.obj U) (fiberMk (𝟙 _))
  map {U V} f := CategoryOfElements.homMk _ _ (p.map f) (by simp)

中文:
定义 functor
  签名: : N ⥤ (fiber.{w} p).Elements where
  定义体: Functor.elementsMk _ (p.obj U) (fiberMk (𝟙 _))
  map {U V} f := CategoryOfElements.homMk _ _ (p.map f) (by simp)

Depends on / 依赖: Functor, Functor.elementsMk, elementsMk, fiberMk, p.obj
-/
noncomputable def functor : N ⥤ (fiber.{w} p).Elements where
  obj U := Functor.elementsMk _ (p.obj U) (fiberMk (𝟙 _))
  map {U V} f := CategoryOfElements.homMk _ _ (p.map f) (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: N] : (functor.{w} p).Initial
  body: by
  refine Functor.initial_of_exists_of_isCofiltered _ ?_ ?_
  · rintro ⟨X, x⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    exact ⟨U, f, by simp⟩
  · rintro ⟨X, x⟩ V ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨W, g, hg⟩ := exists_of_fiberMk_e

中文:
实例 [是余filtered
  签名: N] : (functor.{w} p).初始
  定义体: by
  refine Functor.initial_of_exists_of_isCofiltered _ ?_ ?_
  · rintro ⟨X, x⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    exact ⟨U, f, by simp⟩
  · rintro ⟨X, x⟩ V ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨W, g, hg⟩ := exists_of_fiberMk_e

Depends on / 依赖: Functor, Functor.initial_of_exists_of_isCofiltered, cat_disch, exists_of_fiberMk_eq_fiberMk, fiberMk, fiberMk_jointly_surjective, initial_of_exists_of_isCofiltered
-/
instance [IsCofiltered N] : (functor.{w} p).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ ?_ ?_
  · rintro ⟨X, x⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    exact ⟨U, f, by simp⟩
  · rintro ⟨X, x⟩ V ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨W, g, hg⟩ := exists_of_fiberMk_eq_fiberMk
      (show fiberMk.{w} φ₁ = fiberMk.{w} φ₂ by simpa using hφ₁.trans hφ₂.symm)
    exact ⟨_, g, by cat_disch⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: N] :
  body: initiallySmall_of_initial_of_initiallySmall (functor.{w} p)

中文:
实例 [是余filtered
  签名: N] :
  定义体: initiallySmall_of_initial_of_initiallySmall (functor.{w} p)

Depends on / 依赖: functor, initiallySmall_of_initial_of_initiallySmall
-/
instance [IsCofiltered N] :
    InitiallySmall.{w} (fiber.{w} p).Elements :=
  initiallySmall_of_initial_of_initiallySmall (functor.{w} p)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: N] :
  body: IsCofiltered.of_initial (functor.{w} p)

中文:
实例 [是余filtered
  签名: N] :
  定义体: IsCofiltered.of_initial (functor.{w} p)

Depends on / 依赖: IsCofiltered, IsCofiltered.of_initial, functor, of_initial
-/
instance [IsCofiltered N] :
    IsCofiltered (ofIsCofiltered.fiber p).Elements :=
  IsCofiltered.of_initial (functor.{w} p)

end ofIsCofiltered

variable [IsCofiltered N]
  (hp : forall ⦃X : C⦄ (R : Sieve X) (_ : R in J X) ⦃U : N⦄ (f : p.obj U ⟶ X),
    exists (Y : C) (g : Y ⟶ X) (_ : R g) (V : N) (q : V ⟶ U) (a : p.obj V ⟶ Y),
      a ≫ g = p.map q ≫ f)

open ofIsCofiltered

/-- Constructor for points of Grothendieck topologies `J : GrothendieckTopology C`
that are given by a functor `p : N ⥤ C` from a cofiltered and initially small
category `N`. -/
@[simps]
/--
Definition of `ofIsCofiltered` / `ofIsCofiltered` 的定义

English:
definition ofIsCofiltered
  signature: :
  body: ofIsCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

中文:
定义 ofIsCofiltered
  签名: :
  定义体: ofIsCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

Depends on / 依赖: ofIsCofiltered, ofIsCofiltered.fiber
-/
noncomputable def ofIsCofiltered :
    Point.{w} J where
  fiber := ofIsCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/--
Definition of `toPresheafFiberOfIsCofiltered` / `toPresheafFiberOfIsCofiltered` 的定义

English:
definition toPresheafFiberOfIsCofiltered
  signature: (U : N) (P : Cᵒᵖ ⥤ A)
  body: (ofIsCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

中文:
定义 toPresheafFiberOfIsCofiltered
  签名: (U : N) (P : Cᵒᵖ ⥤ A)
  定义体: (ofIsCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

Depends on / 依赖: fiberMk, ofIsCofiltered, toPresheafFiber
-/
noncomputable def toPresheafFiberOfIsCofiltered (U : N) (P : Cᵒᵖ ⥤ A) :
    P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.obj P :=
  (ofIsCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toPresheafFiberOfIsCofiltered_w` / 引理 `toPresheafFiberOfIsCofiltered_w`

English:
lemma toPresheafFiberOfIsCofiltered_w
  given: {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A)
  proof: by
  simp [toPresheafFiberOfIsCofiltered]

中文:
引理 toPresheafFiberOfIsCofiltered_w
  条件: {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A)
  证明: by
  simp [toPresheafFiberOfIsCofiltered]

Depends on / 依赖: toPresheafFiberOfIsCofiltered
-/
lemma toPresheafFiberOfIsCofiltered_w {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A) :
    P.map (p.map f).op ≫ toPresheafFiberOfIsCofiltered p hp V P =
      toPresheafFiberOfIsCofiltered p hp U P := by
  simp [toPresheafFiberOfIsCofiltered]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `toPresheafFiberOfIsCofiltered_naturality` / 引理 `toPresheafFiberOfIsCofiltered_naturality`

English:
lemma toPresheafFiberOfIsCofiltered_naturality
  given: {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (U : N)
  proof: by
  simp [toPresheafFiberOfIsCofiltered]

中文:
引理 toPresheafFiberOfIsCofiltered_naturality
  条件: {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (U : N)
  证明: by
  simp [toPresheafFiberOfIsCofiltered]

Depends on / 依赖: toPresheafFiberOfIsCofiltered
-/
lemma toPresheafFiberOfIsCofiltered_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (U : N) :
    toPresheafFiberOfIsCofiltered p hp U P ≫
      (ofIsCofiltered p hp).presheafFiber.map g =
    g.app (op (p.obj U)) ≫ toPresheafFiberOfIsCofiltered p hp U Q := by
  simp [toPresheafFiberOfIsCofiltered]

set_option backward.defeqAttrib.useBackward true in
/-- The (colimit) cocone which, for a point constructed using `Point.ofIsCofiltered`
and a functor `p : N ⥤ C` expresses the fiber of a presheaf as a colimit
indexed indexed by `N`. -/
@[simps]
/--
Definition of `presheafFiberOfIsCofilteredCocone` / `presheafFiberOfIsCofilteredCocone` 的定义

English:
definition presheafFiberOfIsCofilteredCocone
  signature: (P : Cᵒᵖ ⥤ A)
  body: (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfIsCofiltered _ _ _ _

中文:
定义 presheafFiberOfIsCofilteredCocone
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfIsCofiltered _ _ _ _

Depends on / 依赖: ofIsCofiltered, presheafFiber, presheafFiber.obj
-/
noncomputable def presheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    Cocone (p.op ⋙ P) where
  pt := (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfIsCofiltered _ _ _ _

/--
Definition of `isColimitPresheafFiberOfIsCofilteredCocone` / `isColimitPresheafFiberOfIsCofilteredCocone` 的定义

English:
definition isColimitPresheafFiberOfIsCofilteredCocone
  signature: (P : Cᵒᵖ ⥤ A)
  body: (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

中文:
定义 isColimitPresheafFiberOfIsCofilteredCocone
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

Depends on / 依赖: Functor, Functor.Final.isColimitWhiskerEquiv, functor, isColimitPresheafFiberCocone, isColimitWhiskerEquiv, ofIsCofiltered
-/
noncomputable def isColimitPresheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    IsColimit (presheafFiberOfIsCofilteredCocone p hp P) :=
  (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

end GrothendieckTopology.Point

end CategoryTheory
