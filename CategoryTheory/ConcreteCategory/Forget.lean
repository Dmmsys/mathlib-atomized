/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov, Anne Baanen,
  Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Types.Basic
/-!
# Forgetful functors

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types, see the file
`Mathlib.CategoryTheory.ConcreteCategory.Basic`

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`.
We impose no restrictions on the category `C`, so `Type` has the identity forgetful functor.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`. Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`. Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

@[expose] public section

namespace CategoryTheory

universe w u

variable (C : Type*) [Category* C] {FC : outParam <| C -> C -> Type*} {CC : outParam <| C -> Type w}
    [outParam <| forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/--
Definition of `forget` / `forget` 的定义

English:
abbreviation forget
  signature: : C ⥤ Type w where
  body: ToType X
  map f := ↾f

中文:
缩写 forget
  签名: : C ⥤ 类型 w where
  定义体: ToType X
  map f := ↾f

Depends on / 依赖: ToType
-/
abbrev forget : C ⥤ Type w where
  obj X := ToType X
  map f := ↾f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Faithful
  body: ConcreteCategory.hom_ext _ _ fun x => ConcreteCategory.congr_hom h x

中文:
实例 :
  签名: (forget C).忠实
  定义体: ConcreteCategory.hom_ext _ _ fun x => ConcreteCategory.congr_hom h x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ext, congr_hom, hom_ext, reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
instance : (forget C).Faithful where
  map_injective h := ConcreteCategory.hom_ext _ _ fun x => ConcreteCategory.congr_hom h x

variable {C}

@[simp]
/--
lemma `ConcreteCategory.forget_map_eq_ofHom` / 引理 `ConcreteCategory.forget_map_eq_ofHom`

English:
lemma ConcreteCategory.forget_map_eq_ofHom
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

@[deprecated (since := "2026-04-11")] alias ConcreteCategory.forget_map_eq_coe :=
  ConcreteCategory.forget_map_eq_ofHom

中文:
引理 余ncrete范畴.forget_map_eq_ofHom
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl

@[deprecated (since := "2026-04-11")] alias ConcreteCategory.forget_map_eq_coe :=
  ConcreteCategory.forget_map_eq_ofHom

Depends on / 依赖: evaluation, evaluationJointlyReflectsLimits, isLimitOfPreserves, isLimitOfReflects
-/
lemma ConcreteCategory.forget_map_eq_ofHom {X Y : C} (f : X ⟶ Y) :
    (forget C).map f = ↾f :=
  rfl

@[deprecated (since := "2026-04-11")] alias ConcreteCategory.forget_map_eq_coe :=
  ConcreteCategory.forget_map_eq_ofHom

/--
theorem `forget_obj` / 定理 `forget_obj`

English:
theorem forget_obj
  given: (X : C)
  statement: (forget C).obj X = ToType X
  proof: rfl

中文:
定理 forget_obj
  条件: (X : C)
  结论: (forget C).obj X = ToType X
  证明: rfl
-/
theorem forget_obj (X : C) : (forget C).obj X = ToType X := rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X)
  statement: f x = g x
  proof: congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X -> ToType Y)) h) x

中文:
定理 congr_fun
  条件: {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X)
  结论: f x = g x
  证明: congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X -> ToType Y)) h) x
-/
protected theorem congr_fun {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X -> ToType Y)) h) x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x')
  statement: f x = f x'
  proof: congrArg (f : ToType X -> ToType Y) h

中文:
定理 congr_arg
  条件: {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x')
  结论: f x = f x'
  证明: congrArg (f : ToType X -> ToType Y) h
-/
protected theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X -> ToType Y) h

variable (C)

variable (D : Type*) [Category* D] {FD : outParam <| D -> D -> Type*}
    {CD : outParam <| D -> Type w}
    [outParam <| forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

/--
Definition of `HasForget₂` / `HasForget₂` 的定义

English:
class HasForget₂
  parameters: where
  axioms and operations (2):
    - forget₂ : C ⥤ D
    - forget_comp : forget₂ ⋙ forget D = forget C  [default: by aesop]

中文:
类 有Forget₂
  参数: where
  公理与运算 (2 个):
    - forget₂ : C ⥤ D
    - forget_comp : forget₂ ⋙ forget D = forget C  [默认: by aesop]
-/
class HasForget₂ where
  /-- A functor from `C` to `D` -/
  forget₂ : C ⥤ D
  /-- It covers the `forget` for `C` and `D` -/
  forget_comp : forget₂ ⋙ forget D = forget C := by aesop

/--
Definition of `forget₂` / `forget₂` 的定义

English:
abbreviation forget₂
  signature: [HasForget₂ C D]
  body: HasForget₂.forget₂

中文:
缩写 forget₂
  签名: [有Forget₂ C D]
  定义体: HasForget₂.forget₂
-/
abbrev forget₂ [HasForget₂ C D] : C ⥤ D :=
  HasForget₂.forget₂

variable {C D}

/--
lemma `forget₂_comp_apply` / 引理 `forget₂_comp_apply`

English:
lemma forget₂_comp_apply
  statement: [HasForget₂ C D] {X Y Z : C}
  proof: by
  rw [Functor.map_comp]; rw [CategoryTheory.comp_apply]

中文:
引理 forget₂_comp_apply
  结论: [有Forget₂ C D] {X Y Z : C}
  证明: by
  rw [Functor.map_comp]; rw [CategoryTheory.comp_apply]

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, Functor, Functor.map_comp, comp_apply, map_comp
-/
lemma forget₂_comp_apply [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType <| (forget₂ C D).obj X) :
    ((forget₂ C D).map (f ≫ g) x) = (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp]; rw [CategoryTheory.comp_apply]

/--
Instance `forget₂_faithful` / 实例 `forget₂_faithful`

English:
instance forget₂_faithful
  signature: [HasForget₂ C D]
  body: HasForget₂.forget_comp.faithful_of_comp

中文:
实例 forget₂_faithful
  签名: [有Forget₂ C D]
  定义体: HasForget₂.forget_comp.faithful_of_comp

Depends on / 依赖: faithful_of_comp, forget_comp, forget_comp.faithful_of_comp
-/
instance forget₂_faithful [HasForget₂ C D] : (forget₂ C D).Faithful :=
  HasForget₂.forget_comp.faithful_of_comp

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `InducedCategory.hasForget₂` / 实例 `InducedCategory.hasForget₂`

English:
instance InducedCategory.hasForget₂
  signature: (f : C -> D)
  body: inducedFunctor f
  forget_comp := rfl

中文:
实例 InducedCategory.hasForget₂
  签名: (f : C -> D)
  定义体: inducedFunctor f
  forget_comp := rfl

Depends on / 依赖: inducedFunctor
-/
instance InducedCategory.hasForget₂ (f : C -> D) : HasForget₂ (InducedCategory D f) D where
  forget₂ := inducedFunctor f
  forget_comp := rfl

/--
Instance `ObjectProperty.FullSubcategory.hasForget₂` / 实例 `ObjectProperty.FullSubcategory.hasForget₂`

English:
instance ObjectProperty.FullSubcategory.hasForget₂
  signature: (P : ObjectProperty C)
  body: P.ι
  forget_comp := rfl

@[deprecated (since := "2026-04-18")] alias FullSubcategory.hasForget₂ :=
  ObjectProperty.FullSubcategory.hasForget₂

中文:
实例 ObjectProperty.满子范畴.hasForget₂
  签名: (P : ObjectProperty C)
  定义体: P.ι
  forget_comp := rfl

@[deprecated (since := "2026-04-18")] alias FullSubcategory.hasForget₂ :=
  ObjectProperty.FullSubcategory.hasForget₂
-/
instance ObjectProperty.FullSubcategory.hasForget₂ (P : ObjectProperty C) :
    HasForget₂ P.FullSubcategory C where
  forget₂ := P.ι
  forget_comp := rfl

@[deprecated (since := "2026-04-18")] alias FullSubcategory.hasForget₂ :=
  ObjectProperty.FullSubcategory.hasForget₂

/-- In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
@[instance_reducible]
/--
Definition of `HasForget₂.mk'` / `HasForget₂.mk'` 的定义

English:
definition HasForget₂.mk'
  signature: (obj : C -> D) (h_obj : forall X, (forget D).obj (obj X) = (forget C).obj X)
  body: Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply Functor.Faithful.div_comp

中文:
定义 有Forget₂.mk'
  签名: (obj : C -> D) (h_obj : 对任意 X, (forget D).obj (obj X) = (forget C).obj X)
  定义体: Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply Functor.Faithful.div_comp

Depends on / 依赖: Faithful, Functor, Functor.Faithful.div, h_map, h_obj
-/
def HasForget₂.mk' (obj : C -> D) (h_obj : forall X, (forget D).obj (obj X) = (forget C).obj X)
    (map : forall {X Y}, (X ⟶ Y) -> (obj X ⟶ obj Y))
    (h_map : forall {X Y} {f : X ⟶ Y}, (forget D).map (map f) ≍ (forget C).map f) :
    HasForget₂ C D where
  forget₂ := Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply Functor.Faithful.div_comp


variable (C D) in
/-- Composition of `HasForget₂` instances. -/
@[reducible]
/--
Definition of `HasForget₂.trans` / `HasForget₂.trans` 的定义

English:
definition HasForget₂.trans
  signature: (E : Type*) [Category* E] {FE : outParam <| E -> E -> Type*}
  body: CategoryTheory.forget₂ C D ⋙ CategoryTheory.forget₂ D E
  forget_comp := by
    change (CategoryTheory.forget₂ _ D) ⋙ (CategoryTheory.forget₂ D E ⋙ CategoryTheory.forget E) = _
    simp only [HasForget₂.forget_comp]

中文:
定义 有Forget₂.trans
  签名: (E : 类型) [范畴* E] {FE : outParam <| E -> E -> 类型}
  定义体: CategoryTheory.forget₂ C D ⋙ CategoryTheory.forget₂ D E
  forget_comp := by
    change (CategoryTheory.forget₂ _ D) ⋙ (CategoryTheory.forget₂ D E ⋙ CategoryTheory.forget E) = _
    simp only [HasForget₂.forget_comp]

Depends on / 依赖: CategoryTheory, CategoryTheory.forget
-/
def HasForget₂.trans (E : Type*) [Category* E] {FE : outParam <| E -> E -> Type*}
    {CE : outParam <| E -> Type w}
    [outParam <| forall X Y, FunLike (FE X Y) (CE X) (CE Y)] [ConcreteCategory.{w} E FE]
    [HasForget₂ C D] [HasForget₂ D E] : HasForget₂ C E where
  forget₂ := CategoryTheory.forget₂ C D ⋙ CategoryTheory.forget₂ D E
  forget_comp := by
    change (CategoryTheory.forget₂ _ D) ⋙ (CategoryTheory.forget₂ D E ⋙ CategoryTheory.forget E) = _
    simp only [HasForget₂.forget_comp]

/--
lemma `ConcreteCategory.forget₂_comp_apply` / 引理 `ConcreteCategory.forget₂_comp_apply`

English:
lemma ConcreteCategory.forget₂_comp_apply
  statement: [HasForget₂ C D] {X Y Z : C}
  proof: by
  rw [Functor.map_comp]; rw [CategoryTheory.comp_apply]

中文:
引理 余ncrete范畴.forget₂_comp_apply
  结论: [有Forget₂ C D] {X Y Z : C}
  证明: by
  rw [Functor.map_comp]; rw [CategoryTheory.comp_apply]

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, Functor, Functor.map_comp, comp_apply, map_comp
-/
lemma ConcreteCategory.forget₂_comp_apply [HasForget₂ C D] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ToType ((forget₂ C D).obj X)) :
    ((forget₂ C D).map (f ≫ g) x) =
      (forget₂ C D).map g ((forget₂ C D).map f x) := by
  rw [Functor.map_comp]; rw [CategoryTheory.comp_apply]

/--
Instance `hom_isIso` / 实例 `hom_isIso`

English:
instance hom_isIso
  signature: {X Y : C} (f : X ⟶ Y) [IsIso f]
  body: ((forget C).mapIso (asIso f)).isIso_hom

中文:
实例 hom_isIso
  签名: {X Y : C} (f : X ⟶ Y) [是同构 f]
  定义体: ((forget C).mapIso (asIso f)).isIso_hom

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom
-/
instance hom_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (C := Type _) (↾(ConcreteCategory.hom f)) :=
  ((forget C).mapIso (asIso f)).isIso_hom

end CategoryTheory
