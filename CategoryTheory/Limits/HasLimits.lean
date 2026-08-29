/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Existence of limits and colimits

In `CategoryTheory.Limits.IsLimit` we defined `IsLimit c`,
the data showing that a cone `c` is a limit cone.

The two main structures defined in this file are:
* `LimitCone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `HasLimit F`, asserting the mere existence of some limit cone for `F`.

`HasLimit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).

While `HasLimit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `HasLimit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.pt ⟶ limit F`, the universal morphism from any other `c : Cone F`, etc.

Key to using the `HasLimit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `HasLimitsOfShape J C` and `HasLimits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `IsLimit`,
and then a result in terms of `HasLimit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `HasLimit`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category theory universes].
universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u} [Category.{v} C]
variable {F : J ⥤ C}

to_dual_name_hint Lift Desc

section Limit

/--
Definition of `LimitCone` / `LimitCone` 的定义

English:
structure LimitCone
  parameters: (F : J ⥤ C)
  axioms and operations (2):
    - cone : Cone F
    - isLimit : IsLimit cone

中文:
结构 LimitCone
  参数: (F : J ⥤ C)
  公理与运算 (2 个):
    - cone : Cone F
    - isLimit : IsLimit cone
-/
structure LimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isLimit : IsLimit cone

/-- `ColimitCocone F` contains a cocone over `F` together with the information that it is a
colimit. -/
@[to_dual]
/--
Definition of `ColimitCocone` / `ColimitCocone` 的定义

English:
structure ColimitCocone
  parameters: (F : J ⥤ C)
  axioms and operations (2):
    - cocone : Cocone F
    - isColimit : IsColimit cocone

中文:
结构 ColimitCocone
  参数: (F : J ⥤ C)
  公理与运算 (2 个):
    - cocone : Cocone F
    - isColimit : IsColimit cocone
-/
structure ColimitCocone (F : J ⥤ C) where
  /-- The cocone itself -/
  cocone : Cocone F
  /-- The proof that it is the colimit cocone -/
  isColimit : IsColimit cocone

/--
Definition of `HasLimit` / `HasLimit` 的定义

English:
class HasLimit
  parameters: (F : J ⥤ C)
  (no additional axioms)

中文:
类 HasLimit
  参数: (F : J ⥤ C)
  (无附加公理)
-/
class HasLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (LimitCone F)

/-- `HasColimit F` represents the mere existence of a colimit for `F`. -/
@[to_dual]
/--
Definition of `HasColimit` / `HasColimit` 的定义

English:
class HasColimit
  parameters: (F : J ⥤ C)
  (no additional axioms)

中文:
类 HasColimit
  参数: (F : J ⥤ C)
  (无附加公理)
-/
class HasColimit (F : J ⥤ C) : Prop where mk' ::
  /-- There exists a colimit for `F` -/
  exists_colimit : Nonempty (ColimitCocone F)

@[to_dual]
/--
theorem `HasLimit.mk` / 定理 `HasLimit.mk`

English:
theorem HasLimit.mk
  given: {F : J ⥤ C} (d : LimitCone F)
  statement: HasLimit F
  proof: ⟨Nonempty.intro d⟩

中文:
定理 HasLimit.mk
  条件: {F : J ⥤ C} (d : LimitCone F)
  结论: HasLimit F
  证明: ⟨Nonempty.intro d⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `LimitCone F` from `HasLimit F`. -/
@[no_expose, to_dual
/-- Use the axiom of choice to extract explicit `ColimitCocone F` from `HasColimit F`. -/]
/--
Definition of `getLimitCone` / `getLimitCone` 的定义

English:
definition getLimitCone
  signature: (F : J ⥤ C) [HasLimit F]
  body: Classical.choice HasLimit.exists_limit

中文:
定义 getLimitCone
  签名: (F : J ⥤ C) [HasLimit F]
  定义体: Classical.choice HasLimit.exists_limit

Depends on / 依赖: Classical, Classical.choice, HasLimit, HasLimit.exists_limit, choice, exists_limit
-/
def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
Classical.choice HasLimit.exists_limit

variable (J C)

/--
Definition of `HasLimitsOfShape` / `HasLimitsOfShape` 的定义

English:
class HasLimitsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - has_limit : forall F : J ⥤ C, HasLimit F  [default: by infer_instance]

中文:
类 HasLimitsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - has_limit : 对任意 F : J ⥤ C, HasLimit F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_limit : forall F : J ⥤ C, HasLimit F := by infer_instance

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
@[to_dual]
/--
Definition of `HasColimitsOfShape` / `HasColimitsOfShape` 的定义

English:
class HasColimitsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - has_colimit : forall F : J ⥤ C, HasColimit F  [default: by infer_instance]

中文:
类 HasColimitsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - has_colimit : 对任意 F : J ⥤ C, HasColimit F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasColimitsOfShape : Prop where
  /-- All `F : J ⥤ C` have colimits for a fixed `J` -/
  has_colimit : forall F : J ⥤ C, HasColimit F := by infer_instance

/-- `C` has all limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `HasLimitsOfSize` / `HasLimitsOfSize` 的定义

English:
class HasLimitsOfSize
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - has_limits_of_shape : forall (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C  [default: by infer_instance]

中文:
类 HasLimitsOfSize
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - has_limits_of_shape : 对任意 (J : 类型u₁) [Category.{v₁} J], HasLimitsOfShape J C  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have limits -/
  has_limits_of_shape : forall (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C := by
    infer_instance

/-- `C` has all colimits of size `v₁ u₁` (`HasColimitsOfSize.{v₁ u₁} C`)
if it has colimits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[to_dual, univ_out_params, pp_with_univ]
/--
Definition of `HasColimitsOfSize` / `HasColimitsOfSize` 的定义

English:
class HasColimitsOfSize
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - has_colimits_of_shape : forall (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C  [default: by infer_instance]

中文:
类 HasColimitsOfSize
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - has_colimits_of_shape : 对任意 (J : 类型u₁) [Category.{v₁} J], HasColimitsOfShape J C  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All `F : J ⥤ C` have colimits for all small `J` -/
  has_colimits_of_shape : forall (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C := by
    infer_instance

/-- `C` has all (small) limits if it has limits of every shape that is as big as its hom-sets. -/
@[to_dual
/-- `C` has all (small) colimits if it has colimits of every shape that is as big as its hom-sets.
-/]
/--
Definition of `HasLimits` / `HasLimits` 的定义

English:
abbreviation HasLimits
  signature: (C : Type u) [Category.{v} C]
  body: HasLimitsOfSize.{v, v} C

@[to_dual]

中文:
缩写 HasLimits
  签名: (C : 类型u) [Category.{v} C]
  定义体: HasLimitsOfSize.{v, v} C

@[to_dual]

Depends on / 依赖: HasLimitsOfSize
-/
abbrev HasLimits (C : Type u) [Category.{v} C] : Prop :=
  HasLimitsOfSize.{v, v} C

@[to_dual]
/--
theorem `HasLimits.has_limits_of_shape` / 定理 `HasLimits.has_limits_of_shape`

English:
theorem HasLimits.has_limits_of_shape
  statement: {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
  proof: HasLimitsOfSize.has_limits_of_shape J

中文:
定理 HasLimits.has_limits_of_shape
  结论: {C : 类型u} [Category.{v} C] [HasLimits C] (J : 类型v)
  证明: HasLimitsOfSize.has_limits_of_shape J

Depends on / 依赖: HasLimitsOfSize, HasLimitsOfSize.has_limits_of_shape, has_limits_of_shape
-/
theorem HasLimits.has_limits_of_shape {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
    [Category.{v} J] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

variable {J C}

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfShape J C] (F : J ⥤ C) : HasLimit F :=
  HasLimitsOfShape.has_limit F

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

-- Interface to the `HasLimit` class.
/-- An arbitrary choice of limit cone for a functor. -/
@[to_dual colimit.cocone /-- An arbitrary choice of colimit cocone of a functor. -/]
/--
Definition of `limit.cone` / `limit.cone` 的定义

English:
definition limit.cone
  signature: (F : J ⥤ C) [HasLimit F]
  body: (getLimitCone F).cone

中文:
定义 limit.cone
  签名: (F : J ⥤ C) [HasLimit F]
  定义体: (getLimitCone F).cone

Depends on / 依赖: getLimitCone
-/
def limit.cone (F : J ⥤ C) [HasLimit F] : Cone F :=
  (getLimitCone F).cone

/-- An arbitrary choice of limit object of a functor. -/
@[to_dual (attr := implicit_reducible) /-- An arbitrary choice of colimit object of a functor. -/]
/--
Definition of `limit` / `limit` 的定义

English:
definition limit
  signature: (F : J ⥤ C) [HasLimit F]
  body: (limit.cone F).pt

中文:
定义 limit
  签名: (F : J ⥤ C) [HasLimit F]
  定义体: (limit.cone F).pt

Depends on / 依赖: limit.cone
-/
def limit (F : J ⥤ C) [HasLimit F] :=
  (limit.cone F).pt

/-- The projection from the limit object to a value of the functor. -/
@[to_dual (attr := implicit_reducible) ι
/-- The coprojection from a value of the functor to the colimit object. -/]
/--
Definition of `limit.π` / `limit.π` 的定义

English:
definition limit.π
  signature: (F : J ⥤ C) [HasLimit F] (j : J)
  body: (limit.cone F).π.app j

中文:
定义 limit.π
  签名: (F : J ⥤ C) [HasLimit F] (j : J)
  定义体: (limit.cone F).π.app j

Depends on / 依赖: limit.cone
-/
def limit.π (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  (limit.cone F).π.app j

/--
theorem `limit.π_comp_eqToHom` / 定理 `limit.π_comp_eqToHom`

English:
theorem limit.π_comp_eqToHom
  given: (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j')
  proof: by
  subst hj
  simp

@[to_dual existing (attr := reassoc) π_comp_eqToHom]

中文:
定理 limit.π_comp_eqToHom
  条件: (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j')
  证明: by
  subst hj
  simp

@[to_dual existing (attr := reassoc) π_comp_eqToHom]
-/
theorem limit.π_comp_eqToHom (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j') :
    limit.π F j ≫ eqToHom (by subst hj; rfl) = limit.π F j' := by
  subst hj
  simp

@[to_dual existing (attr := reassoc) π_comp_eqToHom]
/--
theorem `colimit.eqToHom_comp_ι` / 定理 `colimit.eqToHom_comp_ι`

English:
theorem colimit.eqToHom_comp_ι
  given: (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j')
  proof: by
  subst hj
  simp

@[to_dual (attr := simp)]

中文:
定理 colimit.eqToHom_comp_ι
  条件: (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j')
  证明: by
  subst hj
  simp

@[to_dual (attr := simp)]
-/
theorem colimit.eqToHom_comp_ι (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j') :
    eqToHom (by subst hj; rfl) ≫ colimit.ι F j = colimit.ι F j' := by
  subst hj
  simp

@[to_dual (attr := simp)]
/--
theorem `limit.cone_x` / 定理 `limit.cone_x`

English:
theorem limit.cone_x
  given: {F : J ⥤ C} [HasLimit F]
  statement: (limit.cone F).pt = limit F
  proof: rfl

@[to_dual (attr := simp) cocone_ι]

中文:
定理 limit.cone_x
  条件: {F : J ⥤ C} [HasLimit F]
  结论: (limit.cone F).pt = limit F
  证明: rfl

@[to_dual (attr := simp) cocone_ι]
-/
theorem limit.cone_x {F : J ⥤ C} [HasLimit F] : (limit.cone F).pt = limit F :=
  rfl

@[to_dual (attr := simp) cocone_ι]
/--
theorem `limit.cone_π` / 定理 `limit.cone_π`

English:
theorem limit.cone_π
  given: {F : J ⥤ C} [HasLimit F]
  statement: (limit.cone F).π.app = limit.π _
  proof: rfl

@[to_dual (attr := reassoc (attr := simp))]

中文:
定理 limit.cone_π
  条件: {F : J ⥤ C} [HasLimit F]
  结论: (limit.cone F).π.app = limit.π _
  证明: rfl

@[to_dual (attr := reassoc (attr := simp))]
-/
theorem limit.cone_π {F : J ⥤ C} [HasLimit F] : (limit.cone F).π.app = limit.π _ :=
  rfl

@[to_dual (attr := reassoc (attr := simp))]
/--
theorem `limit.w` / 定理 `limit.w`

English:
theorem limit.w
  given: (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j')
  proof: (limit.cone F).w f

中文:
定理 limit.w
  条件: (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j')
  证明: (limit.cone F).w f

Depends on / 依赖: limit.cone
-/
theorem limit.w (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' :=
  (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `limit.cone F` is a limit cone. -/
@[to_dual
/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/]
/--
Definition of `limit.isLimit` / `limit.isLimit` 的定义

English:
definition limit.isLimit
  signature: (F : J ⥤ C) [HasLimit F]
  body: (getLimitCone F).isLimit

中文:
定义 limit.isLimit
  签名: (F : J ⥤ C) [HasLimit F]
  定义体: (getLimitCone F).isLimit

Depends on / 依赖: getLimitCone, isLimit
-/
def limit.isLimit (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  (getLimitCone F).isLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
@[to_dual
/-- The morphism from the colimit object to the cone point of any other cocone. -/]
/--
Definition of `limit.lift` / `limit.lift` 的定义

English:
definition limit.lift
  signature: (F : J ⥤ C) [HasLimit F] (c : Cone F)
  body: (limit.isLimit F).lift c

@[to_dual (attr := simp)]

中文:
定义 limit.lift
  签名: (F : J ⥤ C) [HasLimit F] (c : Cone F)
  定义体: (limit.isLimit F).lift c

@[to_dual (attr := simp)]

Depends on / 依赖: isLimit, limit.isLimit
-/
def limit.lift (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  (limit.isLimit F).lift c

@[to_dual (attr := simp)]
/--
theorem `limit.isLimit_lift` / 定理 `limit.isLimit_lift`

English:
theorem limit.isLimit_lift
  given: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  proof: rfl

@[to_dual (attr := reassoc (attr := simp)) ι_desc]

中文:
定理 limit.isLimit_lift
  条件: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  证明: rfl

@[to_dual (attr := reassoc (attr := simp)) ι_desc]
-/
theorem limit.isLimit_lift {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.isLimit F).lift c = limit.lift F c :=
  rfl

@[to_dual (attr := reassoc (attr := simp)) ι_desc]
/--
theorem `limit.lift_π` / 定理 `limit.lift_π`

English:
theorem limit.lift_π
  given: {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J)
  proof: IsLimit.fac _ c j

中文:
定理 limit.lift_π
  条件: {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J)
  证明: IsLimit.fac _ c j

Depends on / 依赖: IsLimit, IsLimit.fac
-/
theorem limit.lift_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  IsLimit.fac _ c j

/-- Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
@[to_dual
/-- Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/]
/--
Definition of `limMap` / `limMap` 的定义

English:
definition limMap
  signature: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G)
  body: IsLimit.map _ (limit.isLimit G) α

@[to_dual (attr := reassoc (attr := simp)) ι_colimMap]

中文:
定义 limMap
  签名: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G)
  定义体: IsLimit.map _ (limit.isLimit G) α

@[to_dual (attr := reassoc (attr := simp)) ι_colimMap]

Depends on / 依赖: IsLimit, IsLimit.map, isLimit, limit.isLimit
-/
def limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  IsLimit.map _ (limit.isLimit G) α

@[to_dual (attr := reassoc (attr := simp)) ι_colimMap]
/--
theorem `limMap_π` / 定理 `limMap_π`

English:
theorem limMap_π
  given: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
  proof: limit.lift_π _ j

中文:
定理 limMap_π
  条件: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
  证明: limit.lift_π _ j

Depends on / 依赖: limit.lift_
-/
theorem limMap_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
@[to_dual /-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/]
/--
Definition of `limit.coneMorphism` / `limit.coneMorphism` 的定义

English:
definition limit.coneMorphism
  signature: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  body: (limit.isLimit F).liftConeMorphism c

@[to_dual (attr := simp)]

中文:
定义 limit.coneMorphism
  签名: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  定义体: (limit.isLimit F).liftConeMorphism c

@[to_dual (attr := simp)]

Depends on / 依赖: isLimit, liftConeMorphism, limit.isLimit
-/
def limit.coneMorphism {F : J ⥤ C} [HasLimit F] (c : Cone F) : c ⟶ limit.cone F :=
  (limit.isLimit F).liftConeMorphism c

@[to_dual (attr := simp)]
/--
theorem `limit.coneMorphism_hom` / 定理 `limit.coneMorphism_hom`

English:
theorem limit.coneMorphism_hom
  given: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  proof: rfl

@[to_dual ι_coconeMorphism]

中文:
定理 limit.coneMorphism_hom
  条件: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  证明: rfl

@[to_dual ι_coconeMorphism]
-/
theorem limit.coneMorphism_hom {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.coneMorphism c).hom = limit.lift F c :=
  rfl

@[to_dual ι_coconeMorphism]
/--
theorem `limit.coneMorphism_π` / 定理 `limit.coneMorphism_π`

English:
theorem limit.coneMorphism_π
  given: {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J)
  proof: by simp

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]

中文:
定理 limit.coneMorphism_π
  条件: {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J)
  证明: by simp

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]
-/
theorem limit.coneMorphism_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    (limit.coneMorphism c).hom ≫ limit.π F j = c.π.app j := by simp

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]
/--
theorem `limit.conePointUniqueUpToIso_hom_comp` / 定理 `limit.conePointUniqueUpToIso_hom_comp`

English:
theorem limit.conePointUniqueUpToIso_hom_comp
  statement: {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
  proof: IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]

中文:
定理 limit.conePointUniqueUpToIso_hom_comp
  结论: {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
  证明: IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, conePointUniqueUpToIso_hom_comp
-/
theorem limit.conePointUniqueUpToIso_hom_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso hc (limit.isLimit _)).hom ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]
/--
theorem `limit.conePointUniqueUpToIso_inv_comp` / 定理 `limit.conePointUniqueUpToIso_inv_comp`

English:
theorem limit.conePointUniqueUpToIso_inv_comp
  statement: {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[to_dual]

中文:
定理 limit.conePointUniqueUpToIso_inv_comp
  结论: {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[to_dual]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
theorem limit.conePointUniqueUpToIso_inv_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc).inv ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[to_dual]
/--
theorem `limit.existsUnique` / 定理 `limit.existsUnique`

English:
theorem limit.existsUnique
  given: {F : J ⥤ C} [HasLimit F] (t : Cone F)
  proof: (limit.isLimit F).existsUnique _

中文:
定理 limit.existsUnique
  条件: {F : J ⥤ C} [HasLimit F] (t : Cone F)
  证明: (limit.isLimit F).existsUnique _

Depends on / 依赖: existsUnique, inverseImage_eq, isLimit, limit.isLimit
-/
theorem limit.existsUnique {F : J ⥤ C} [HasLimit F] (t : Cone F) :
    exists! l : t.pt ⟶ limit F, forall j, l ≫ limit.π F j = t.π.app j :=
  (limit.isLimit F).existsUnique _

/-- Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point. -/
@[to_dual
/-- Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone
point. -/]
/--
Definition of `limit.isoLimitCone` / `limit.isoLimitCone` 的定义

English:
definition limit.isoLimitCone
  signature: {F : J ⥤ C} [HasLimit F] (t : LimitCone F)
  body: IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_inv]

中文:
定义 limit.isoLimitCone
  签名: {F : J ⥤ C} [HasLimit F] (t : LimitCone F)
  定义体: IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_inv]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit, t.isLimit
-/
def limit.isoLimitCone {F : J ⥤ C} [HasLimit F] (t : LimitCone F) : limit F ≅ t.cone.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_inv]
/--
theorem `limit.isoLimitCone_hom_π` / 定理 `limit.isoLimitCone_hom_π`

English:
theorem limit.isoLimitCone_hom_π
  given: {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J)
  proof: by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_hom]

中文:
定理 limit.isoLimitCone_hom_π
  条件: {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J)
  证明: by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_hom]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isoLimitCone, limit.isoLimitCone
-/
theorem limit.isoLimitCone_hom_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).hom ≫ t.cone.π.app j = limit.π F j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_hom]
/--
theorem `limit.isoLimitCone_inv_π` / 定理 `limit.isoLimitCone_inv_π`

English:
theorem limit.isoLimitCone_inv_π
  given: {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J)
  proof: by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := ext)]

中文:
定理 limit.isoLimitCone_inv_π
  条件: {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J)
  证明: by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := ext)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isoLimitCone, limit.isoLimitCone
-/
theorem limit.isoLimitCone_inv_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := ext)]
/--
theorem `limit.hom_ext` / 定理 `limit.hom_ext`

English:
theorem limit.hom_ext
  statement: {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
  proof: (limit.isLimit F).hom_ext w

@[to_dual]

中文:
定理 limit.hom_ext
  结论: {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
  证明: (limit.isLimit F).hom_ext w

@[to_dual]

Depends on / 依赖: hom_ext, isLimit, limit.isLimit
-/
theorem limit.hom_ext {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : forall j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.isLimit F).hom_ext w

@[to_dual]
/--
Instance `isIso_limMap` / 实例 `isIso_limMap`

English:
instance isIso_limMap
  signature: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [IsIso α]
  body: ⟨limMap (inv α), by cat_disch , by cat_disch⟩

@[to_dual (attr := reassoc (attr := simp)) map_desc]

中文:
实例 isIso_limMap
  签名: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [IsIso α]
  定义体: ⟨limMap (inv α), by cat_disch , by cat_disch⟩

@[to_dual (attr := reassoc (attr := simp)) map_desc]

Depends on / 依赖: cat_disch, limMap
-/
instance isIso_limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [IsIso α] :
    IsIso (limMap α) :=
  ⟨limMap (inv α), by cat_disch , by cat_disch⟩

@[to_dual (attr := reassoc (attr := simp)) map_desc]
/--
theorem `limit.lift_map` / 定理 `limit.lift_map`

English:
theorem limit.lift_map
  given: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G)
  proof: by
  ext
  rw [assoc]; rw [limMap_π]; rw [limit.lift_π_assoc]; rw [limit.lift_π]
  rfl

@[to_dual (attr := simp)]

中文:
定理 limit.lift_map
  条件: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G)
  证明: by
  ext
  rw [assoc]; rw [limMap_π]; rw [limit.lift_π_assoc]; rw [limit.lift_π]
  rfl

@[to_dual (attr := simp)]

Depends on / 依赖: limit.lift_
-/
theorem limit.lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cone.postcompose α).obj c) := by
  ext
  rw [assoc]; rw [limMap_π]; rw [limit.lift_π_assoc]; rw [limit.lift_π]
  rfl

@[to_dual (attr := simp)]
/--
theorem `limit.lift_cone` / 定理 `limit.lift_cone`

English:
theorem limit.lift_cone
  given: {F : J ⥤ C} [HasLimit F]
  statement: limit.lift F (limit.cone F) = 𝟙 (limit F)
  proof: (limit.isLimit _).lift_self

中文:
定理 limit.lift_cone
  条件: {F : J ⥤ C} [HasLimit F]
  结论: limit.lift F (limit.cone F) = 𝟙 (limit F)
  证明: (limit.isLimit _).lift_self

Depends on / 依赖: isLimit, lift_self, limit.isLimit
-/
theorem limit.lift_cone {F : J ⥤ C} [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  (limit.isLimit _).lift_self

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
/--
Definition of `limit.homIso` / `limit.homIso` 的定义

English:
definition limit.homIso
  signature: (F : J ⥤ C) [HasLimit F] (W : C)
  body: (limit.isLimit F).homIso W

@[simp]

中文:
定义 limit.homIso
  签名: (F : J ⥤ C) [HasLimit F] (W : C)
  定义体: (limit.isLimit F).homIso W

@[simp]

Depends on / 依赖: homIso, isLimit, limit.isLimit
-/
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W

@[simp]
/--
theorem `limit.homIso_hom` / 定理 `limit.homIso_hom`

English:
theorem limit.homIso_hom
  given: (F : J ⥤ C) [HasLimit F] {W : C}
  proof: (limit.isLimit F).homIso_hom

中文:
定理 limit.homIso_hom
  条件: (F : J ⥤ C) [HasLimit F] {W : C}
  证明: (limit.isLimit F).homIso_hom

Depends on / 依赖: homIso_hom, isLimit, limit.isLimit
-/
theorem limit.homIso_hom (F : J ⥤ C) [HasLimit F] {W : C} :
    (limit.homIso F W).hom = ↾fun f => (const J).map f.down ≫ (limit.cone F).π :=
  (limit.isLimit F).homIso_hom

/--
Definition of `limit.homIso'` / `limit.homIso'` 的定义

English:
definition limit.homIso'
  signature: (F : J ⥤ C) [HasLimit F] (W : C)
  body: (limit.isLimit F).homIso' W

@[to_dual]

中文:
定义 limit.homIso'
  签名: (F : J ⥤ C) [HasLimit F] (W : C)
  定义体: (limit.isLimit F).homIso' W

@[to_dual]

Depends on / 依赖: homIso, isLimit, limit.isLimit
-/
def limit.homIso' (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅
      { p : forall j, W ⟶ F.obj j // forall {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  (limit.isLimit F).homIso' W

@[to_dual]
/--
theorem `limit.lift_extend` / 定理 `limit.lift_extend`

English:
theorem limit.lift_extend
  given: {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt)
  proof: by cat_disch

中文:
定理 limit.lift_extend
  条件: {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem limit.lift_extend {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    limit.lift F (c.extend f) = f ≫ limit.lift F c := by cat_disch

/-- If a functor `F` has a limit, so does any naturally isomorphic functor. -/
@[to_dual none]
/--
theorem `hasLimit_of_iso` / 定理 `hasLimit_of_iso`

English:
theorem hasLimit_of_iso
  given: {F G : J ⥤ C} [HasLimit F] (α : F ≅ G)
  statement: HasLimit G
  proof: HasLimit.mk
    { cone := (Cone.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }

@[to_dual]

中文:
定理 hasLimit_of_iso
  条件: {F G : J ⥤ C} [HasLimit F] (α : F ≅ G)
  结论: HasLimit G
  证明: HasLimit.mk
    { cone := (Cone.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }

@[to_dual]

Depends on / 依赖: Cone.postcompose, HasLimit, HasLimit.mk, IsLimit, IsLimit.postcomposeHomEquiv, isLimit, limit.cone, limit.isLimit, postcompose, postcomposeHomEquiv
-/
theorem hasLimit_of_iso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G :=
  HasLimit.mk
    { cone := (Cone.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }

@[to_dual]
/--
theorem `hasLimit_iff_of_iso` / 定理 `hasLimit_iff_of_iso`

English:
theorem hasLimit_iff_of_iso
  given: {F G : J ⥤ C} (α : F ≅ G)
  statement: HasLimit F ↔ HasLimit G
  proof: ⟨fun _ => hasLimit_of_iso α, fun _ => hasLimit_of_iso α.symm⟩

中文:
定理 hasLimit_iff_of_iso
  条件: {F G : J ⥤ C} (α : F ≅ G)
  结论: HasLimit F ↔ HasLimit G
  证明: ⟨fun _ => hasLimit_of_iso α, fun _ => hasLimit_of_iso α.symm⟩

Depends on / 依赖: hasLimit_of_iso
-/
theorem hasLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G :=
  ⟨fun _ => hasLimit_of_iso α, fun _ => hasLimit_of_iso α.symm⟩

-- See the construction of limits from products and equalizers
-- for an example usage.
/--
theorem `HasLimit.ofConesIso` / 定理 `HasLimit.ofConesIso`

English:
theorem HasLimit.ofConesIso
  statement: {J K : Type u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
  proof: HasLimit.mk ⟨_, IsLimit.ofRepresentableBy ((limit.isLimit F).representableBy.ofIso h)⟩

中文:
定理 HasLimit.ofConesIso
  结论: {J K : 类型u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
  证明: HasLimit.mk ⟨_, IsLimit.ofRepresentableBy ((limit.isLimit F).representableBy.ofIso h)⟩

Depends on / 依赖: HasLimit, HasLimit.mk, IsLimit, IsLimit.ofRepresentableBy, isLimit, limit.isLimit, ofRepresentableBy, representableBy, representableBy.ofIso
-/
theorem HasLimit.ofConesIso {J K : Type u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
    (G : K ⥤ C) (h : F.cones ≅ G.cones) [HasLimit F] : HasLimit G :=
  HasLimit.mk ⟨_, IsLimit.ofRepresentableBy ((limit.isLimit F).representableBy.ofIso h)⟩

/-- The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
@[to_dual
/-- The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/]
/--
Definition of `HasLimit.isoOfNatIso` / `HasLimit.isoOfNatIso` 的定义

English:
definition HasLimit.isoOfNatIso
  signature: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G)
  body: IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w

@[reassoc (attr := simp)]

中文:
定义 HasLimit.isoOfNatIso
  签名: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G)
  定义体: IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointsIsoOfNatIso, conePointsIsoOfNatIso, isLimit, limit.isLimit
-/
def HasLimit.isoOfNatIso {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w

@[reassoc (attr := simp)]
/--
theorem `HasLimit.isoOfNatIso_hom_π` / 定理 `HasLimit.isoOfNatIso_hom_π`

English:
theorem HasLimit.isoOfNatIso_hom_π
  given: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J)
  proof: IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _

@[reassoc (attr := simp)]

中文:
定理 HasLimit.isoOfNatIso_hom_π
  条件: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J)
  证明: IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointsIsoOfNatIso_hom_comp, conePointsIsoOfNatIso_hom_comp
-/
theorem HasLimit.isoOfNatIso_hom_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _

@[reassoc (attr := simp)]
/--
theorem `HasLimit.isoOfNatIso_inv_π` / 定理 `HasLimit.isoOfNatIso_inv_π`

English:
theorem HasLimit.isoOfNatIso_inv_π
  given: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J)
  proof: IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _

@[reassoc (attr := simp)]

中文:
定理 HasLimit.isoOfNatIso_inv_π
  条件: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J)
  证明: IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointsIsoOfNatIso_inv_comp, conePointsIsoOfNatIso_inv_comp
-/
theorem HasLimit.isoOfNatIso_inv_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).inv ≫ limit.π F j = limit.π G j ≫ w.inv.app j :=
  IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _

@[reassoc (attr := simp)]
/--
theorem `HasLimit.lift_isoOfNatIso_hom` / 定理 `HasLimit.lift_isoOfNatIso_hom`

English:
theorem HasLimit.lift_isoOfNatIso_hom
  statement: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
  proof: IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _

@[reassoc (attr := simp)]

中文:
定理 HasLimit.lift_isoOfNatIso_hom
  结论: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
  证明: IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.lift_comp_conePointsIsoOfNatIso_hom, lift_comp_conePointsIsoOfNatIso_hom
-/
theorem HasLimit.lift_isoOfNatIso_hom {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
    (w : F ≅ G) :
    limit.lift F t ≫ (HasLimit.isoOfNatIso w).hom =
      limit.lift G ((Cone.postcompose w.hom).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _

@[reassoc (attr := simp)]
/--
theorem `HasLimit.lift_isoOfNatIso_inv` / 定理 `HasLimit.lift_isoOfNatIso_inv`

English:
theorem HasLimit.lift_isoOfNatIso_inv
  statement: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
  proof: IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _

中文:
定理 HasLimit.lift_isoOfNatIso_inv
  结论: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
  证明: IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _

Depends on / 依赖: IsLimit, IsLimit.lift_comp_conePointsIsoOfNatIso_inv, lift_comp_conePointsIsoOfNatIso_inv
-/
theorem HasLimit.lift_isoOfNatIso_inv {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
    (w : F ≅ G) :
    limit.lift G t ≫ (HasLimit.isoOfNatIso w).inv =
      limit.lift F ((Cone.postcompose w.inv).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _

/--
Definition of `HasLimit.isoOfEquivalence` / `HasLimit.isoOfEquivalence` 的定义

English:
definition HasLimit.isoOfEquivalence
  signature: {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
  body: IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w

中文:
定义 HasLimit.isoOfEquivalence
  签名: {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
  定义体: IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w

Depends on / 依赖: CatCommSq, Discrete, E.functor, Functor, Functor.associator, Functor.pi, Functor.rightUnitor, IsLimit, IsLimit.conePointsIsoOfEquivalence, Iso.refl, associator, conePointsIsoOfEquivalence, counitIso, counitIso.symm, functor, isLimit, isoWhiskerLeft, isoWhiskerRight, limit.isLimit, piEquivalenceFunctorDiscrete
-/
def HasLimit.isoOfEquivalence {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `HasLimit.isoOfEquivalence_hom_π` / 定理 `HasLimit.isoOfEquivalence_hom_π`

English:
theorem HasLimit.isoOfEquivalence_hom_π
  statement: {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
  proof: by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  simp

中文:
定理 HasLimit.isoOfEquivalence_hom_π
  结论: {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
  证明: by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  simp

Depends on / 依赖: HasLimit, HasLimit.isoOfEquivalence, IsLimit, IsLimit.conePointsIsoOfEquivalence_hom, conePointsIsoOfEquivalence_hom, isoOfEquivalence
-/
theorem HasLimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    (HasLimit.isoOfEquivalence e w).hom ≫ limit.π G k =
      limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `HasLimit.isoOfEquivalence_inv_π` / 定理 `HasLimit.isoOfEquivalence_inv_π`

English:
theorem HasLimit.isoOfEquivalence_inv_π
  statement: {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
  proof: by
  simp only [HasLimit.isoOfEquivalence]
  simp

中文:
定理 HasLimit.isoOfEquivalence_inv_π
  结论: {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
  证明: by
  simp only [HasLimit.isoOfEquivalence]
  simp

Depends on / 依赖: HasLimit, HasLimit.isoOfEquivalence, isoOfEquivalence
-/
theorem HasLimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    (HasLimit.isoOfEquivalence e w).inv ≫ limit.π F j =
    limit.π G (e.functor.obj j) ≫ w.hom.app j := by
  simp only [HasLimit.isoOfEquivalence]
  simp

section Pre

variable (F)
variable [HasLimit F] (E : K ⥤ J) [HasLimit (E ⋙ F)]

/--
Definition of `limit.pre` / `limit.pre` 的定义

English:
definition limit.pre
  signature: : limit F ⟶ limit (E ⋙ F)
  body: limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[reassoc (attr := simp)]

中文:
定义 limit.pre
  签名: : limit F ⟶ limit (E ⋙ F)
  定义体: limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[reassoc (attr := simp)]

Depends on / 依赖: limit.cone, limit.lift, whisker
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[reassoc (attr := simp)]
/--
theorem `limit.pre_π` / 定理 `limit.pre_π`

English:
theorem limit.pre_π
  given: (k : K)
  statement: limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k)
  proof: by
  simp [limit.pre]

@[simp]

中文:
定理 limit.pre_π
  条件: (k : K)
  结论: limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k)
  证明: by
  simp [limit.pre]

@[simp]

Depends on / 依赖: limit.pre
-/
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) := by
  simp [limit.pre]

@[simp]
/--
theorem `limit.lift_pre` / 定理 `limit.lift_pre`

English:
theorem limit.lift_pre
  given: (c : Cone F)
  proof: by ext; simp

中文:
定理 limit.lift_pre
  条件: (c : Cone F)
  证明: by ext; simp
-/
theorem limit.lift_pre (c : Cone F) :
    limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) := by ext; simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[simp]
/--
theorem `limit.pre_pre` / 定理 `limit.pre_pre`

English:
theorem limit.pre_pre
  given: [h : HasLimit (D ⋙ E ⋙ F)]
  statement: haveI : HasLimit ((D ⋙ E) ⋙ F)
  proof: h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  have : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl

中文:
定理 limit.pre_pre
  条件: [h : HasLimit (D ⋙ E ⋙ F)]
  结论: haveI : HasLimit ((D ⋙ E) ⋙ F)
  证明: h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  have : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl
-/
theorem limit.pre_pre [h : HasLimit (D ⋙ E ⋙ F)] : haveI : HasLimit ((D ⋙ E) ⋙ F) := h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  have : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl

variable {E F}

/--
theorem `limit.pre_eq` / 定理 `limit.pre_eq`

English:
theorem limit.pre_eq
  given: (s : LimitCone (E ⋙ F)) (t : LimitCone F)
  proof: by cat_disch

中文:
定理 limit.pre_eq
  条件: (s : LimitCone (E ⋙ F)) (t : LimitCone F)
  证明: by cat_disch

Depends on / 依赖: Construction, Functor, Functor.assoc, Functor.comp_id, IsEquivalence, IsEquivalence.mk, Localization, Localization.Construction.fac, Localization.Construction.uniq, Q_inverts, W.Q_inverts, cat_disch, comp_id, eqToIso, inverts, isEquivalence
-/
theorem limit.pre_eq (s : LimitCone (E ⋙ F)) (t : LimitCone F) :
    limit.pre F E = (limit.isoLimitCone t).hom ≫ s.isLimit.lift (t.cone.whisker E) ≫
      (limit.isoLimitCone s).inv := by cat_disch

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]
variable (F : J ⥤ C) [HasLimit F] (G : C ⥤ D) [HasLimit (F ⋙ G)]

/--
Definition of `limit.post` / `limit.post` 的定义

English:
definition limit.post
  signature: : G.obj (limit F) ⟶ limit (F ⋙ G)
  body: limit.lift (F ⋙ G) (G.mapCone (limit.cone F))

@[reassoc (attr := simp)]

中文:
定义 limit.post
  签名: : G.obj (limit F) ⟶ limit (F ⋙ G)
  定义体: limit.lift (F ⋙ G) (G.mapCone (limit.cone F))

@[reassoc (attr := simp)]

Depends on / 依赖: G.mapCone, limit.cone, limit.lift, mapCone
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (G.mapCone (limit.cone F))

@[reassoc (attr := simp)]
/--
theorem `limit.post_π` / 定理 `limit.post_π`

English:
theorem limit.post_π
  given: (j : J)
  statement: limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j)
  proof: by
  simp [limit.post]

@[simp]

中文:
定理 limit.post_π
  条件: (j : J)
  结论: limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j)
  证明: by
  simp [limit.post]

@[simp]

Depends on / 依赖: limit.post
-/
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  simp [limit.post]

@[simp]
/--
theorem `limit.lift_post` / 定理 `limit.lift_post`

English:
theorem limit.lift_post
  given: (c : Cone F)
  proof: by
  ext
  rw [assoc]; rw [limit.post_π]; rw [← G.map_comp]; rw [limit.lift_π]; rw [limit.lift_π]
  rfl

@[simp]

中文:
定理 limit.lift_post
  条件: (c : Cone F)
  证明: by
  ext
  rw [assoc]; rw [limit.post_π]; rw [← G.map_comp]; rw [limit.lift_π]; rw [limit.lift_π]
  rfl

@[simp]

Depends on / 依赖: G.map_comp, limit.lift_, limit.post_, map_comp
-/
theorem limit.lift_post (c : Cone F) :
    G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.mapCone c) := by
  ext
  rw [assoc]; rw [limit.post_π]; rw [← G.map_comp]; rw [limit.lift_π]; rw [limit.lift_π]
  rfl

@[simp]
/--
theorem `limit.post_post` / 定理 `limit.post_post`

English:
theorem limit.post_post
  given: {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)]
  proof: h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  have : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl

中文:
定理 limit.post_post
  条件: {E : 类型u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)]
  证明: h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  have : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl
-/
theorem limit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)] :
    -- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals
    -- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H))
    haveI : HasLimit (F ⋙ G ⋙ H) := h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  have : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl

end Post

/--
theorem `limit.pre_post` / 定理 `limit.pre_post`

English:
theorem limit.pre_post
  statement: {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  proof: h
    G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := by
  have : HasLimit (E ⋙ F ⋙ G) := h
  ext; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]

中文:
定理 limit.pre_post
  结论: {D : 类型u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  证明: h
    G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := by
  have : HasLimit (E ⋙ F ⋙ G) := h
  ext; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]
-/
theorem limit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasLimit F] [HasLimit (E ⋙ F)] [HasLimit (F ⋙ G)]
    [h : HasLimit ((E ⋙ F) ⋙ G)] : -- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs
            -- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or
    haveI : HasLimit (E ⋙ F ⋙ G) := h
    G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := by
  have : HasLimit (E ⋙ F ⋙ G) := h
  ext; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]

open CategoryTheory.Equivalence

/--
Instance `hasLimit_equivalence_comp` / 实例 `hasLimit_equivalence_comp`

English:
instance hasLimit_equivalence_comp
  signature: (e : K ≌ J) [HasLimit F]
  body: HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }

中文:
实例 hasLimit_equivalence_comp
  签名: (e : K ≌ J) [HasLimit F]
  定义体: HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }

Depends on / 依赖: Cone.whisker, HasLimit, HasLimit.mk, IsLimit, IsLimit.whiskerEquivalence, e.functor, functor, isLimit, limit.cone, limit.isLimit, whisker, whiskerEquivalence
-/
instance hasLimit_equivalence_comp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙ F) :=
  HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }

-- not entirely sure why this is needed
/--
theorem `hasLimit_of_equivalence_comp` / 定理 `hasLimit_of_equivalence_comp`

English:
theorem hasLimit_of_equivalence_comp
  given: (e : K ≌ J) [HasLimit (e.functor ⋙ F)]
  statement: HasLimit F
  proof: by
  have : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimit_equivalence_comp e.symm
  apply hasLimit_of_iso (e.invFunIdAssoc F)

中文:
定理 hasLimit_of_equivalence_comp
  条件: (e : K ≌ J) [HasLimit (e.functor ⋙ F)]
  结论: HasLimit F
  证明: by
  have : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimit_equivalence_comp e.symm
  apply hasLimit_of_iso (e.invFunIdAssoc F)

Depends on / 依赖: HasLimit, Limits, Limits.hasLimit_equivalence_comp, e.functor, e.invFunIdAssoc, e.inverse, e.symm, functor, hasLimit_equivalence_comp, hasLimit_of_iso, invFunIdAssoc, inverse
-/
theorem hasLimit_of_equivalence_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F := by
  have : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimit_equivalence_comp e.symm
  apply hasLimit_of_iso (e.invFunIdAssoc F)

/--
lemma `hasLimit_equivalence_comp_iff` / 引理 `hasLimit_equivalence_comp_iff`

English:
lemma hasLimit_equivalence_comp_iff
  given: (e : K ≌ J)
  statement: HasLimit (e.functor ⋙ F) ↔ HasLimit F
  proof: ⟨fun _ => hasLimit_of_equivalence_comp e, fun _ => inferInstance⟩

中文:
引理 hasLimit_equivalence_comp_iff
  条件: (e : K ≌ J)
  结论: HasLimit (e.functor ⋙ F) ↔ HasLimit F
  证明: ⟨fun _ => hasLimit_of_equivalence_comp e, fun _ => inferInstance⟩

Depends on / 依赖: hasLimit_of_equivalence_comp
-/
lemma hasLimit_equivalence_comp_iff (e : K ≌ J) : HasLimit (e.functor ⋙ F) ↔ HasLimit F :=
  ⟨fun _ => hasLimit_of_equivalence_comp e, fun _ => inferInstance⟩

/--
lemma `hasLimit_inverse_equivalence_comp_iff` / 引理 `hasLimit_inverse_equivalence_comp_iff`

English:
lemma hasLimit_inverse_equivalence_comp_iff
  given: (e : J ≌ K)
  statement: HasLimit (e.inverse ⋙ F) ↔ HasLimit F
  proof: hasLimit_equivalence_comp_iff e.symm

中文:
引理 hasLimit_inverse_equivalence_comp_iff
  条件: (e : J ≌ K)
  结论: HasLimit (e.inverse ⋙ F) ↔ HasLimit F
  证明: hasLimit_equivalence_comp_iff e.symm

Depends on / 依赖: e.symm, hasLimit_equivalence_comp_iff
-/
lemma hasLimit_inverse_equivalence_comp_iff (e : J ≌ K) : HasLimit (e.inverse ⋙ F) ↔ HasLimit F :=
  hasLimit_equivalence_comp_iff e.symm

-- `hasLimitCompEquivalence` and `hasLimitOfCompEquivalence`
-- are proved in `Mathlib/CategoryTheory/Adjunction/Limits.lean`.
section LimFunctor

variable [HasLimitsOfShape J C]

section

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[simps, implicit_reducible]
/--
Definition of `lim` / `lim` 的定义

English:
definition lim
  signature: : (J ⥤ C) ⥤ C where
  body: limit F
  map α := limMap α
  map_id F := by
    apply Limits.limit.hom_ext; intro j
    simp
  map_comp α β := by
    apply Limits.limit.hom_ext; intro j
    simp [assoc]

中文:
定义 lim
  签名: : (J ⥤ C) ⥤ C where
  定义体: limit F
  map α := limMap α
  map_id F := by
    apply Limits.limit.hom_ext; intro j
    simp
  map_comp α β := by
    apply Limits.limit.hom_ext; intro j
    simp [assoc]
-/
def lim : (J ⥤ C) ⥤ C where
  obj F := limit F
  map α := limMap α
  map_id F := by
    apply Limits.limit.hom_ext; intro j
    simp
  map_comp α β := by
    apply Limits.limit.hom_ext; intro j
    simp [assoc]

/-- The natural transformation induced by `limit.π`. -/
@[simps]
/--
Definition of `lim.π` / `lim.π` 的定义

English:
definition lim.π
  signature: (j : J)
  body: limit.π F j

中文:
定义 lim.π
  签名: (j : J)
  定义体: limit.π F j
-/
def lim.π (j : J) : lim ⟶ (evaluation J C).obj j where
  app F := limit.π F j

end

variable {G : J ⥤ C} (α : F ⟶ G)

/--
theorem `limMap_eq` / 定理 `limMap_eq`

English:
theorem limMap_eq
  statement: limMap α = lim.map α
  proof: rfl

中文:
定理 limMap_eq
  结论: limMap α = lim.map α
  证明: rfl
-/
theorem limMap_eq : limMap α = lim.map α := rfl

/--
theorem `limit.map_pre` / 定理 `limit.map_pre`

English:
theorem limit.map_pre
  given: [HasLimitsOfShape K C] (E : K ⥤ J)
  proof: by
  ext
  simp

中文:
定理 limit.map_pre
  条件: [HasLimitsOfShape K C] (E : K ⥤ J)
  证明: by
  ext
  simp
-/
theorem limit.map_pre [HasLimitsOfShape K C] (E : K ⥤ J) :
    lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whiskerLeft E α) := by
  ext
  simp

/--
theorem `limit.map_pre'` / 定理 `limit.map_pre'`

English:
theorem limit.map_pre'
  given: [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂)
  proof: by
  ext1; simp

中文:
定理 limit.map_pre'
  条件: [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂)
  证明: by
  ext1; simp
-/
theorem limit.map_pre' [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whiskerRight α F) := by
  ext1; simp

/--
theorem `limit.id_pre` / 定理 `limit.id_pre`

English:
theorem limit.id_pre
  given: (F : J ⥤ C)
  statement: limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv
  proof: by
  cat_disch

中文:
定理 limit.id_pre
  条件: (F : J ⥤ C)
  结论: limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem limit.id_pre (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv := by
  cat_disch

/--
theorem `limit.map_post` / 定理 `limit.map_post`

English:
theorem limit.map_post
  given: {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D)
  proof: by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]

中文:
定理 limit.map_post
  条件: {D : 类型u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D)
  证明: by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]

Depends on / 依赖: H.map_comp, limit.post_, map_comp, whiskerRight_app
-/
theorem limit.map_post {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D) :
    /- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
     H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
    H.map (limMap α) ≫ limit.post G H = limit.post F H ≫ limMap (whiskerRight α H) := by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `limYoneda` / `limYoneda` 的定义

English:
definition limYoneda
  signature: :
  body: NatIso.ofComponents fun F => NatIso.ofComponents fun W => limit.homIso F (unop W)

中文:
定义 limYoneda
  签名: :
  定义体: NatIso.ofComponents fun F => NatIso.ofComponents fun W => limit.homIso F (unop W)

Depends on / 依赖: NatIso, NatIso.ofComponents, homIso, limit.homIso, ofComponents
-/
def limYoneda :
    lim ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅ CategoryTheory.cones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => limit.homIso F (unop W)

/--
Definition of `constLimAdj` / `constLimAdj` 的定义

English:
definition constLimAdj
  signature: : (const J : C ⥤ J ⥤ C) ⊣ lim
  body: Adjunction.mk' {
  homEquiv := fun c g =>
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun _ => f ≫ limit.π _ _ }
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g =

中文:
定义 constLimAdj
  签名: : (const J : C ⥤ J ⥤ C) ⊣ lim
  定义体: Adjunction.mk' {
  homEquiv := fun c g =>
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun _ => f ≫ limit.π _ _ }
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g =

Depends on / 依赖: Adjunction, Adjunction.mk
-/
def constLimAdj : (const J : C ⥤ J ⥤ C) ⊣ lim := Adjunction.mk' {
  homEquiv := fun c g =>
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun _ => f ≫ limit.π _ _ }
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g => { app := limit.π _ } } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRightAdjoint (lim : (J ⥤ C) ⥤ C)
  body: ⟨_, ⟨constLimAdj⟩⟩

中文:
实例 :
  签名: IsRightAdjoint (lim : (J ⥤ C) ⥤ C)
  定义体: ⟨_, ⟨constLimAdj⟩⟩

Depends on / 依赖: constLimAdj
-/
instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨constLimAdj⟩⟩

end LimFunctor

/--
Instance `limMap_mono'` / 实例 `limMap_mono'`

English:
instance limMap_mono'
  signature: {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α]
  body: (lim : (J ⥤ C) ⥤ C).map_mono α

中文:
实例 limMap_mono'
  签名: {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α]
  定义体: (lim : (J ⥤ C) ⥤ C).map_mono α

Depends on / 依赖: map_mono
-/
instance limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α

/--
Instance `limMap_mono` / 实例 `limMap_mono`

English:
instance limMap_mono
  signature: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [forall j, Mono (α.app j)]
  body: ⟨fun {Z} u v h =>
limit.hom_ext fun j => (cancel_mono (α.app j)).1 by simpa using h =≫ limit.π _ j⟩

中文:
实例 limMap_mono
  签名: {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [对任意 j, Mono (α.app j)]
  定义体: ⟨fun {Z} u v h =>
limit.hom_ext fun j => (cancel_mono (α.app j)).1 by simpa using h =≫ limit.π _ j⟩

Depends on / 依赖: cancel_mono, hom_ext, limit.hom_ext
-/
instance limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [forall j, Mono (α.app j)] :
    Mono (limMap α) :=
  ⟨fun {Z} u v h =>
limit.hom_ext fun j => (cancel_mono (α.app j)).1 by simpa using h =≫ limit.π _ j⟩

section Adjunction

variable {L : (J ⥤ C) ⥤ C} (adj : Functor.const _ ⊣ L)

/- The fact that the existence of limits of shape `J` is equivalent to the existence
of a right adjoint to the constant functor `C ⥤ (J ⥤ C)` is obtained in
the file `Mathlib/CategoryTheory/Limits/ConeCategory.lean`: see the lemma
`hasLimitsOfShape_iff_isLeftAdjoint_const`. In the definitions below, given an
adjunction `adj : Functor.const _ ⊣ (L : (J ⥤ C) ⥤ C)`, we directly construct
a limit cone for any `F : J ⥤ C`. -/

/-- The limit cone obtained from a right adjoint of the constant functor. -/
@[simps]
/--
Definition of `coneOfAdj` / `coneOfAdj` 的定义

English:
definition coneOfAdj
  signature: (F : J ⥤ C)
  body: L.obj F
  π := adj.counit.app F

中文:
定义 coneOfAdj
  签名: (F : J ⥤ C)
  定义体: L.obj F
  π := adj.counit.app F

Depends on / 依赖: L.obj
-/
noncomputable def coneOfAdj (F : J ⥤ C) : Cone F where
  pt := L.obj F
  π := adj.counit.app F

set_option backward.defeqAttrib.useBackward true in
/-- The cones defined by `coneOfAdj` are limit cones. -/
@[simps]
/--
Definition of `isLimitConeOfAdj` / `isLimitConeOfAdj` 的定义

English:
definition isLimitConeOfAdj
  signature: (F : J ⥤ C)
  body: adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (adj.left_triangle_components s.pt) j
    dsimp at eq eq' ⊢
    rw [adj.homEquiv_unit]; rw [assoc]; rw [eq]; rw [reassoc_of% eq']
  uniq s m hm := (adj.homEquiv _ _

中文:
定义 isLimitConeOfAdj
  签名: (F : J ⥤ C)
  定义体: adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (adj.left_triangle_components s.pt) j
    dsimp at eq eq' ⊢
    rw [adj.homEquiv_unit]; rw [assoc]; rw [eq]; rw [reassoc_of% eq']
  uniq s m hm := (adj.homEquiv _ _

Depends on / 依赖: adj.homEquiv, homEquiv
-/
def isLimitConeOfAdj (F : J ⥤ C) :
    IsLimit (coneOfAdj adj F) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (adj.left_triangle_components s.pt) j
    dsimp at eq eq' ⊢
    rw [adj.homEquiv_unit]; rw [assoc]; rw [eq]; rw [reassoc_of% eq']
  uniq s m hm := (adj.homEquiv _ _).symm.injective (by ext j; simpa using! hm j)

end Adjunction

/--
theorem `hasLimitsOfShape_of_equivalence` / 定理 `hasLimitsOfShape_of_equivalence`

English:
theorem hasLimitsOfShape_of_equivalence
  statement: {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
  proof: by
  constructor
  intro F
  apply hasLimit_of_equivalence_comp e

中文:
定理 hasLimitsOfShape_of_equivalence
  结论: {J' : 类型u₂} [Category.{v₂} J'] (e : J ≌ J')
  证明: by
  constructor
  intro F
  apply hasLimit_of_equivalence_comp e

Depends on / 依赖: hasLimit_of_equivalence_comp
-/
theorem hasLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasLimitsOfShape J C] : HasLimitsOfShape J' C := by
  constructor
  intro F
  apply hasLimit_of_equivalence_comp e

variable (C)

/--
lemma `HasLimitsOfShape.of_small` / 引理 `HasLimitsOfShape.of_small`

English:
lemma HasLimitsOfShape.of_small
  proof: by
  have := HasLimitsOfSize.has_limits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

中文:
引理 HasLimitsOfShape.of_small
  证明: by
  have := HasLimitsOfSize.has_limits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

Depends on / 依赖: HasLimitsOfSize, HasLimitsOfSize.has_limits_of_shape, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, equivalence, hasLimitsOfShape_of_equivalence, has_limits_of_shape, symm.trans
-/
lemma HasLimitsOfShape.of_small
    [HasLimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [Small.{u₁} J] [LocallySmall.{v₁} J] :
    HasLimitsOfShape J C := by
  have := HasLimitsOfSize.has_limits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

/--
lemma `HasLimitsOfShape.of_essentiallySmall` / 引理 `HasLimitsOfShape.of_essentiallySmall`

English:
lemma HasLimitsOfShape.of_essentiallySmall
  proof: by
  have := HasLimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasLimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

中文:
引理 HasLimitsOfShape.of_essentiallySmall
  证明: by
  have := HasLimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasLimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

Depends on / 依赖: HasLimitsOfShape, HasLimitsOfShape.of_small, SmallModel, equivSmallModel, hasLimitsOfShape_of_equivalence, of_small
-/
lemma HasLimitsOfShape.of_essentiallySmall
    [HasLimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [EssentiallySmall.{u₁} J] [LocallySmall.{v₁} J] :
    HasLimitsOfShape J C := by
  have := HasLimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasLimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

/--
theorem `hasLimitsOfSizeOfUnivLE` / 定理 `hasLimitsOfSizeOfUnivLE`

English:
theorem hasLimitsOfSizeOfUnivLE
  statement: [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
  proof: hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

中文:
定理 hasLimitsOfSizeOfUnivLE
  结论: [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
  证明: hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

Depends on / 依赖: hasLimitsOfShape_of_equivalence
-/
theorem hasLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSize.{v₂, u₂} C where
  has_limits_of_shape J {_} := hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

/--
theorem `hasLimitsOfSizeShrink` / 定理 `hasLimitsOfSizeShrink`

English:
theorem hasLimitsOfSizeShrink
  given: [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C]
  proof: hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

中文:
定理 hasLimitsOfSizeShrink
  条件: [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C]
  证明: hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

Depends on / 依赖: hasLimitsOfSizeOfUnivLE
-/
theorem hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasLimitsOfSize.{v₁, u₁} C := hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

instance (priority := 100) hasSmallestLimitsOfHasLimits [HasLimits C] : HasLimitsOfSize.{0, 0} C :=
  hasLimitsOfSizeShrink.{0, 0} C

end Limit

section Colimit

/--
Definition of `colimit.homIso` / `colimit.homIso` 的定义

English:
definition colimit.homIso
  signature: (F : J ⥤ C) [HasColimit F] (W : C)
  body: (colimit.isColimit F).homIso W

@[simp]

中文:
定义 colimit.homIso
  签名: (F : J ⥤ C) [HasColimit F] (W : C)
  定义体: (colimit.isColimit F).homIso W

@[simp]

Depends on / 依赖: colimit, colimit.isColimit, homIso, isColimit
-/
def colimit.homIso (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅ F.cocones.obj W :=
  (colimit.isColimit F).homIso W

@[simp]
/--
theorem `colimit.homIso_hom` / 定理 `colimit.homIso_hom`

English:
theorem colimit.homIso_hom
  given: (F : J ⥤ C) [HasColimit F] {W : C}
  proof: (colimit.isColimit F).homIso_hom

中文:
定理 colimit.homIso_hom
  条件: (F : J ⥤ C) [HasColimit F] {W : C}
  证明: (colimit.isColimit F).homIso_hom

Depends on / 依赖: colimit, colimit.isColimit, homIso_hom, isColimit
-/
theorem colimit.homIso_hom (F : J ⥤ C) [HasColimit F] {W : C} :
    (colimit.homIso F W).hom =
      ↾fun f => (colimit.cocone F).ι ≫ (const J).map f.down :=
  (colimit.isColimit F).homIso_hom

/--
Definition of `colimit.homIso'` / `colimit.homIso'` 的定义

English:
definition colimit.homIso'
  signature: (F : J ⥤ C) [HasColimit F] (W : C)
  body: (colimit.isColimit F).homIso' W

中文:
定义 colimit.homIso'
  签名: (F : J ⥤ C) [HasColimit F] (W : C)
  定义体: (colimit.isColimit F).homIso' W

Depends on / 依赖: colimit, colimit.isColimit, homIso, isColimit
-/
def colimit.homIso' (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅
      { p : forall j, F.obj j ⟶ W // forall {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  (colimit.isColimit F).homIso' W

-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
/-- If `F` has a colimit, so does any naturally isomorphic functor. -/
@[to_dual none]
/--
theorem `hasColimit_of_iso` / 定理 `hasColimit_of_iso`

English:
theorem hasColimit_of_iso
  given: {F G : J ⥤ C} [HasColimit F] (α : G ≅ F)
  statement: HasColimit G
  proof: HasColimit.mk
    { cocone := (Cocone.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }

中文:
定理 hasColimit_of_iso
  条件: {F G : J ⥤ C} [HasColimit F] (α : G ≅ F)
  结论: HasColimit G
  证明: HasColimit.mk
    { cocone := (Cocone.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }

Depends on / 依赖: Cocone, Cocone.precompose, HasColimit, HasColimit.mk, IsColimit, IsColimit.precomposeHomEquiv, cocone, colimit, colimit.cocone, colimit.isColimit, isColimit, precompose, precomposeHomEquiv
-/
theorem hasColimit_of_iso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G :=
  HasColimit.mk
    { cocone := (Cocone.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }

/--
theorem `HasColimit.ofCoconesIso` / 定理 `HasColimit.ofCoconesIso`

English:
theorem HasColimit.ofCoconesIso
  statement: {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
  proof: HasColimit.mk ⟨_, IsColimit.ofCorepresentableBy ((colimit.isColimit F).corepresentableBy.ofIso h)⟩

@[reassoc (attr := simp)]

中文:
定理 HasColimit.ofCoconesIso
  结论: {K : 类型u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
  证明: HasColimit.mk ⟨_, IsColimit.ofCorepresentableBy ((colimit.isColimit F).corepresentableBy.ofIso h)⟩

@[reassoc (attr := simp)]

Depends on / 依赖: HasColimit, HasColimit.mk, IsColimit, IsColimit.ofCorepresentableBy, colimit, colimit.isColimit, corepresentableBy, corepresentableBy.ofIso, isColimit, ofCorepresentableBy
-/
theorem HasColimit.ofCoconesIso {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
    (h : F.cocones ≅ G.cocones) [HasColimit F] : HasColimit G :=
  HasColimit.mk ⟨_, IsColimit.ofCorepresentableBy ((colimit.isColimit F).corepresentableBy.ofIso h)⟩

@[reassoc (attr := simp)]
/--
theorem `HasColimit.isoOfNatIso_ι_hom` / 定理 `HasColimit.isoOfNatIso_ι_hom`

English:
theorem HasColimit.isoOfNatIso_ι_hom
  statement: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
  proof: IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _

@[reassoc (attr := simp)]

中文:
定理 HasColimit.isoOfNatIso_ι_hom
  结论: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
  证明: IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointsIsoOfNatIso_hom, comp_coconePointsIsoOfNatIso_hom
-/
theorem HasColimit.isoOfNatIso_ι_hom {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι F j ≫ (HasColimit.isoOfNatIso w).hom = w.hom.app j ≫ colimit.ι G j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _

@[reassoc (attr := simp)]
/--
theorem `HasColimit.isoOfNatIso_ι_inv` / 定理 `HasColimit.isoOfNatIso_ι_inv`

English:
theorem HasColimit.isoOfNatIso_ι_inv
  statement: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
  proof: IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _

@[reassoc (attr := simp)]

中文:
定理 HasColimit.isoOfNatIso_ι_inv
  结论: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
  证明: IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointsIsoOfNatIso_inv, comp_coconePointsIsoOfNatIso_inv
-/
theorem HasColimit.isoOfNatIso_ι_inv {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι G j ≫ (HasColimit.isoOfNatIso w).inv = w.inv.app j ≫ colimit.ι F j :=
  IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _

@[reassoc (attr := simp)]
/--
theorem `HasColimit.isoOfNatIso_hom_desc` / 定理 `HasColimit.isoOfNatIso_hom_desc`

English:
theorem HasColimit.isoOfNatIso_hom_desc
  statement: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
  proof: IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 HasColimit.isoOfNatIso_hom_desc
  结论: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
  证明: IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointsIsoOfNatIso_hom_desc, coconePointsIsoOfNatIso_hom_desc
-/
theorem HasColimit.isoOfNatIso_hom_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).hom ≫ colimit.desc G t =
      colimit.desc F ((Cocone.precompose w.hom).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _

@[reassoc (attr := simp)]
/--
theorem `HasColimit.isoOfNatIso_inv_desc` / 定理 `HasColimit.isoOfNatIso_inv_desc`

English:
theorem HasColimit.isoOfNatIso_inv_desc
  statement: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
  proof: IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _

中文:
定理 HasColimit.isoOfNatIso_inv_desc
  结论: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
  证明: IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _

Depends on / 依赖: IsColimit, IsColimit.coconePointsIsoOfNatIso_inv_desc, coconePointsIsoOfNatIso_inv_desc
-/
theorem HasColimit.isoOfNatIso_inv_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).inv ≫ colimit.desc F t =
      colimit.desc G ((Cocone.precompose w.inv).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _

/--
Definition of `HasColimit.isoOfEquivalence` / `HasColimit.isoOfEquivalence` 的定义

English:
definition HasColimit.isoOfEquivalence
  signature: {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
  body: IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w

中文:
定义 HasColimit.isoOfEquivalence
  签名: {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
  定义体: IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w

Depends on / 依赖: IsColimit, IsColimit.coconePointsIsoOfEquivalence, coconePointsIsoOfEquivalence, colimit, colimit.isColimit, isColimit
-/
def HasColimit.isoOfEquivalence {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `HasColimit.ι_isoOfEquivalence_hom` / 定理 `HasColimit.ι_isoOfEquivalence_hom`

English:
theorem HasColimit.ι_isoOfEquivalence_hom
  statement: {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
  proof: by
  simp [HasColimit.isoOfEquivalence]

中文:
定理 HasColimit.ι_isoOfEquivalence_hom
  结论: {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
  证明: by
  simp [HasColimit.isoOfEquivalence]

Depends on / 依赖: HasColimit, HasColimit.isoOfEquivalence, isoOfEquivalence
-/
theorem HasColimit.ι_isoOfEquivalence_hom {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    colimit.ι F j ≫ (HasColimit.isoOfEquivalence e w).hom =
      F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ := by
  simp [HasColimit.isoOfEquivalence]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `HasColimit.ι_isoOfEquivalence_inv` / 定理 `HasColimit.ι_isoOfEquivalence_inv`

English:
theorem HasColimit.ι_isoOfEquivalence_inv
  statement: {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
  proof: by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_hom_π := HasColimit.ι_isoOfEquivalence_hom

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_inv_π := HasColimit.ι_isoOf

中文:
定理 HasColimit.ι_isoOfEquivalence_inv
  结论: {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
  证明: by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_hom_π := HasColimit.ι_isoOfEquivalence_hom

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_inv_π := HasColimit.ι_isoOf

Depends on / 依赖: HasColimit, HasColimit.isoOfEquivalence, IsColimit, IsColimit.coconePointsIsoOfEquivalence_inv, coconePointsIsoOfEquivalence_inv, isoOfEquivalence
-/
theorem HasColimit.ι_isoOfEquivalence_inv {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    colimit.ι G k ≫ (HasColimit.isoOfEquivalence e w).inv =
      G.map (e.counitInv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_hom_π := HasColimit.ι_isoOfEquivalence_hom

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_inv_π := HasColimit.ι_isoOfEquivalence_inv

section Pre

variable (F)
variable [HasColimit F] (E : K ⥤ J) [HasColimit (E ⋙ F)]

/--
Definition of `colimit.pre` / `colimit.pre` 的定义

English:
definition colimit.pre
  signature: : colimit (E ⋙ F) ⟶ colimit F
  body: colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[reassoc (attr := simp)]

中文:
定义 colimit.pre
  签名: : colimit (E ⋙ F) ⟶ colimit F
  定义体: colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[reassoc (attr := simp)]

Depends on / 依赖: cocone, colimit, colimit.cocone, colimit.desc, whisker
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[reassoc (attr := simp)]
/--
theorem `colimit.ι_pre` / 定理 `colimit.ι_pre`

English:
theorem colimit.ι_pre
  given: (k : K)
  statement: colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k)
  proof: by
  simp [colimit.pre]

@[reassoc (attr := simp)]

中文:
定理 colimit.ι_pre
  条件: (k : K)
  结论: colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k)
  证明: by
  simp [colimit.pre]

@[reassoc (attr := simp)]

Depends on / 依赖: F.asEquivalence, Iso.refl, asEquivalence, colimit, colimit.pre, of_equivalence_target
-/
theorem colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) := by
  simp [colimit.pre]

@[reassoc (attr := simp)]
/--
theorem `colimit.ι_inv_pre` / 定理 `colimit.ι_inv_pre`

English:
theorem colimit.ι_inv_pre
  given: [IsIso (pre F E)] (k : K)
  proof: by
  simp [IsIso.comp_inv_eq]

@[reassoc (attr := simp)]

中文:
定理 colimit.ι_inv_pre
  条件: [IsIso (pre F E)] (k : K)
  证明: by
  simp [IsIso.comp_inv_eq]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.comp_inv_eq, comp_inv_eq
-/
theorem colimit.ι_inv_pre [IsIso (pre F E)] (k : K) :
    colimit.ι F (E.obj k) ≫ inv (colimit.pre F E) = colimit.ι (E ⋙ F) k := by
  simp [IsIso.comp_inv_eq]

@[reassoc (attr := simp)]
/--
theorem `colimit.pre_desc` / 定理 `colimit.pre_desc`

English:
theorem colimit.pre_desc
  given: (c : Cocone F)
  proof: by
  ext
  simp

中文:
定理 colimit.pre_desc
  条件: (c : Cocone F)
  证明: by
  ext
  simp
-/
theorem colimit.pre_desc (c : Cocone F) :
    colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) := by
  ext
  simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[simp]
/--
theorem `colimit.pre_pre` / 定理 `colimit.pre_pre`

English:
theorem colimit.pre_pre
  given: [h : HasColimit (D ⋙ E ⋙ F)]
  proof: h
    colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc]; rw [colimit.ι_pre]; rw [colimit.ι_pre]
  have : HasColimit ((D ⋙ E) ⋙ F) := h
  exact (colimit.ι_pre F (D ⋙ E) j).symm

中文:
定理 colimit.pre_pre
  条件: [h : HasColimit (D ⋙ E ⋙ F)]
  证明: h
    colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc]; rw [colimit.ι_pre]; rw [colimit.ι_pre]
  have : HasColimit ((D ⋙ E) ⋙ F) := h
  exact (colimit.ι_pre F (D ⋙ E) j).symm
-/
theorem colimit.pre_pre [h : HasColimit (D ⋙ E ⋙ F)] :
    haveI : HasColimit ((D ⋙ E) ⋙ F) := h
    colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc]; rw [colimit.ι_pre]; rw [colimit.ι_pre]
  have : HasColimit ((D ⋙ E) ⋙ F) := h
  exact (colimit.ι_pre F (D ⋙ E) j).symm

variable {E F}

/--
theorem `colimit.pre_eq` / 定理 `colimit.pre_eq`

English:
theorem colimit.pre_eq
  given: (s : ColimitCocone (E ⋙ F)) (t : ColimitCocone F)
  proof: by
  cat_disch

中文:
定理 colimit.pre_eq
  条件: (s : ColimitCocone (E ⋙ F)) (t : ColimitCocone F)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem colimit.pre_eq (s : ColimitCocone (E ⋙ F)) (t : ColimitCocone F) :
    colimit.pre F E =
      (colimit.isoColimitCocone s).hom ≫
        s.isColimit.desc (t.cocone.whisker E) ≫ (colimit.isoColimitCocone t).inv := by
  cat_disch

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]
variable (F)
variable [HasColimit F] (G : C ⥤ D) [HasColimit (F ⋙ G)]

/--
Definition of `colimit.post` / `colimit.post` 的定义

English:
definition colimit.post
  signature: : colimit (F ⋙ G) ⟶ G.obj (colimit F)
  body: colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))

@[reassoc (attr := simp)]

中文:
定义 colimit.post
  签名: : colimit (F ⋙ G) ⟶ G.obj (colimit F)
  定义体: colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))

@[reassoc (attr := simp)]

Depends on / 依赖: G.mapCocone, cocone, colimit, colimit.cocone, colimit.desc, mapCocone
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
  colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))

@[reassoc (attr := simp)]
/--
theorem `colimit.ι_post` / 定理 `colimit.ι_post`

English:
theorem colimit.ι_post
  given: (j : J)
  proof: by
  simp [colimit.post]

@[simp]

中文:
定理 colimit.ι_post
  条件: (j : J)
  证明: by
  simp [colimit.post]

@[simp]

Depends on / 依赖: colimit, colimit.post
-/
theorem colimit.ι_post (j : J) :
    colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) := by
  simp [colimit.post]

@[simp]
/--
theorem `colimit.post_desc` / 定理 `colimit.post_desc`

English:
theorem colimit.post_desc
  given: (c : Cocone F)
  proof: by
  ext
  rw [← assoc]; rw [colimit.ι_post]; rw [← G.map_comp]; rw [colimit.ι_desc]; rw [colimit.ι_desc]
  rfl

@[simp]

中文:
定理 colimit.post_desc
  条件: (c : Cocone F)
  证明: by
  ext
  rw [← assoc]; rw [colimit.ι_post]; rw [← G.map_comp]; rw [colimit.ι_desc]; rw [colimit.ι_desc]
  rfl

@[simp]

Depends on / 依赖: G.map_comp, colimit, map_comp
-/
theorem colimit.post_desc (c : Cocone F) :
    colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.mapCocone c) := by
  ext
  rw [← assoc]; rw [colimit.ι_post]; rw [← G.map_comp]; rw [colimit.ι_desc]; rw [colimit.ι_desc]
  rfl

@[simp]
/--
theorem `colimit.post_post` / 定理 `colimit.post_post`

English:
theorem colimit.post_post
  statement: {E : Type u''} [Category.{v''} E] (H : D ⥤ E)
  proof: h
    colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc]; rw [colimit.ι_post]; rw [← H.map_comp]; rw [colimit.ι_post]
  have : HasColimit (F ⋙ G ⋙ H) := h
  exact (colimit.ι_post F (G ⋙ H) j).symm

中文:
定理 colimit.post_post
  结论: {E : 类型u''} [Category.{v''} E] (H : D ⥤ E)
  证明: h
    colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc]; rw [colimit.ι_post]; rw [← H.map_comp]; rw [colimit.ι_post]
  have : HasColimit (F ⋙ G ⋙ H) := h
  exact (colimit.ι_post F (G ⋙ H) j).symm
-/
theorem colimit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E)
    -- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals
    -- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H))
    [h : HasColimit ((F ⋙ G) ⋙ H)] : haveI : HasColimit (F ⋙ G ⋙ H) := h
    colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc]; rw [colimit.ι_post]; rw [← H.map_comp]; rw [colimit.ι_post]
  have : HasColimit (F ⋙ G ⋙ H) := h
  exact (colimit.ι_post F (G ⋙ H) j).symm

end Post

/--
theorem `colimit.pre_post` / 定理 `colimit.pre_post`

English:
theorem colimit.pre_post
  statement: {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  proof: h
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
      colimit.pre (F ⋙ G) E ≫ colimit.post F G := by
  ext j
  rw [← assoc]; rw [colimit.ι_post]; rw [← G.map_comp]; rw [colimit.ι_pre]; rw [← assoc]
  have : HasColimit (E ⋙ F ⋙ G) := h
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]

中文:
定理 colimit.pre_post
  结论: {D : 类型u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  证明: h
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
      colimit.pre (F ⋙ G) E ≫ colimit.post F G := by
  ext j
  rw [← assoc]; rw [colimit.ι_post]; rw [← G.map_comp]; rw [colimit.ι_pre]; rw [← assoc]
  have : HasColimit (E ⋙ F ⋙ G) := h
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
-/
theorem colimit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasColimit F] [HasColimit (E ⋙ F)] [HasColimit (F ⋙ G)] [h : HasColimit ((E ⋙ F) ⋙ G)] :
    -- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs
    -- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or
    haveI : HasColimit (E ⋙ F ⋙ G) := h
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
      colimit.pre (F ⋙ G) E ≫ colimit.post F G := by
  ext j
  rw [← assoc]; rw [colimit.ι_post]; rw [← G.map_comp]; rw [colimit.ι_pre]; rw [← assoc]
  have : HasColimit (E ⋙ F ⋙ G) := h
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]

open CategoryTheory.Equivalence

/--
Instance `hasColimit_equivalence_comp` / 实例 `hasColimit_equivalence_comp`

English:
instance hasColimit_equivalence_comp
  signature: (e : K ≌ J) [HasColimit F]
  body: HasColimit.mk
    { cocone := Cocone.whisker e.functor (colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }

中文:
实例 hasColimit_equivalence_comp
  签名: (e : K ≌ J) [HasColimit F]
  定义体: HasColimit.mk
    { cocone := Cocone.whisker e.functor (colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }

Depends on / 依赖: Cocone, Cocone.whisker, HasColimit, HasColimit.mk, IsColimit, IsColimit.whiskerEquivalence, cocone, colimit, colimit.cocone, colimit.isColimit, e.functor, functor, isColimit, whisker, whiskerEquivalence
-/
instance hasColimit_equivalence_comp (e : K ≌ J) [HasColimit F] : HasColimit (e.functor ⋙ F) :=
  HasColimit.mk
    { cocone := Cocone.whisker e.functor (colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }

/--
theorem `hasColimit_of_equivalence_comp` / 定理 `hasColimit_of_equivalence_comp`

English:
theorem hasColimit_of_equivalence_comp
  given: (e : K ≌ J) [HasColimit (e.functor ⋙ F)]
  statement: HasColimit F
  proof: by
  have : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimit_equivalence_comp e.symm
  apply hasColimit_of_iso (e.invFunIdAssoc F).symm

中文:
定理 hasColimit_of_equivalence_comp
  条件: (e : K ≌ J) [HasColimit (e.functor ⋙ F)]
  结论: HasColimit F
  证明: by
  have : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimit_equivalence_comp e.symm
  apply hasColimit_of_iso (e.invFunIdAssoc F).symm

Depends on / 依赖: HasColimit, Limits, Limits.hasColimit_equivalence_comp, e.functor, e.invFunIdAssoc, e.inverse, e.symm, functor, hasColimit_equivalence_comp, hasColimit_of_iso, invFunIdAssoc, inverse
-/
theorem hasColimit_of_equivalence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F := by
  have : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimit_equivalence_comp e.symm
  apply hasColimit_of_iso (e.invFunIdAssoc F).symm

/--
lemma `hasColimit_equivalence_comp_iff` / 引理 `hasColimit_equivalence_comp_iff`

English:
lemma hasColimit_equivalence_comp_iff
  given: (e : K ≌ J)
  statement: HasColimit (e.functor ⋙ F) ↔ HasColimit F
  proof: ⟨fun _ => hasColimit_of_equivalence_comp e, fun _ => inferInstance⟩

中文:
引理 hasColimit_equivalence_comp_iff
  条件: (e : K ≌ J)
  结论: HasColimit (e.functor ⋙ F) ↔ HasColimit F
  证明: ⟨fun _ => hasColimit_of_equivalence_comp e, fun _ => inferInstance⟩

Depends on / 依赖: hasColimit_of_equivalence_comp
-/
lemma hasColimit_equivalence_comp_iff (e : K ≌ J) : HasColimit (e.functor ⋙ F) ↔ HasColimit F :=
  ⟨fun _ => hasColimit_of_equivalence_comp e, fun _ => inferInstance⟩

/--
lemma `hasColimit_inverse_equivalence_comp_iff` / 引理 `hasColimit_inverse_equivalence_comp_iff`

English:
lemma hasColimit_inverse_equivalence_comp_iff
  given: (e : J ≌ K)
  proof: hasColimit_equivalence_comp_iff e.symm

中文:
引理 hasColimit_inverse_equivalence_comp_iff
  条件: (e : J ≌ K)
  证明: hasColimit_equivalence_comp_iff e.symm

Depends on / 依赖: e.symm, hasColimit_equivalence_comp_iff
-/
lemma hasColimit_inverse_equivalence_comp_iff (e : J ≌ K) :
    HasColimit (e.inverse ⋙ F) ↔ HasColimit F :=
  hasColimit_equivalence_comp_iff e.symm

section ColimFunctor

variable [HasColimitsOfShape J C]

section

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps, implicit_reducible]
/--
Definition of `colim` / `colim` 的定义

English:
definition colim
  signature: : (J ⥤ C) ⥤ C where
  body: colimit F
  map α := colimMap α

中文:
定义 colim
  签名: : (J ⥤ C) ⥤ C where
  定义体: colimit F
  map α := colimMap α

Depends on / 依赖: colimit
-/
def colim : (J ⥤ C) ⥤ C where
  obj F := colimit F
  map α := colimMap α

/-- The natural transformation induced by `colimit.ι`. -/
@[simps]
/--
Definition of `colim.ι` / `colim.ι` 的定义

English:
definition colim.ι
  signature: (j : J)
  body: colimit.ι F j

中文:
定义 colim.ι
  签名: (j : J)
  定义体: colimit.ι F j

Depends on / 依赖: colimit
-/
def colim.ι (j : J) : (evaluation J C).obj j ⟶ colim where
  app F := colimit.ι F j

end

variable {G : J ⥤ C} (α : F ⟶ G)

/--
theorem `colimMap_eq` / 定理 `colimMap_eq`

English:
theorem colimMap_eq
  statement: colimMap α = colim.map α
  proof: rfl

@[reassoc]

中文:
定理 colimMap_eq
  结论: colimMap α = colim.map α
  证明: rfl

@[reassoc]
-/
theorem colimMap_eq : colimMap α = colim.map α := rfl

@[reassoc]
/--
theorem `colimit.ι_map` / 定理 `colimit.ι_map`

English:
theorem colimit.ι_map
  given: (j : J)
  statement: colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j
  proof: by simp

中文:
定理 colimit.ι_map
  条件: (j : J)
  结论: colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j
  证明: by simp
-/
theorem colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j := by simp

/--
theorem `colimit.pre_map` / 定理 `colimit.pre_map`

English:
theorem colimit.pre_map
  given: [HasColimitsOfShape K C] (E : K ⥤ J)
  proof: by
  ext
  rw [← assoc]; rw [colimit.ι_pre]; rw [colimit.ι_map]; rw [← assoc]; rw [colimit.ι_map]; rw [assoc]; rw [colimit.ι_pre]
  rfl

中文:
定理 colimit.pre_map
  条件: [HasColimitsOfShape K C] (E : K ⥤ J)
  证明: by
  ext
  rw [← assoc]; rw [colimit.ι_pre]; rw [colimit.ι_map]; rw [← assoc]; rw [colimit.ι_map]; rw [assoc]; rw [colimit.ι_pre]
  rfl

Depends on / 依赖: colimit
-/
theorem colimit.pre_map [HasColimitsOfShape K C] (E : K ⥤ J) :
    colimit.pre F E ≫ colim.map α = colim.map (whiskerLeft E α) ≫ colimit.pre G E := by
  ext
  rw [← assoc]; rw [colimit.ι_pre]; rw [colimit.ι_map]; rw [← assoc]; rw [colimit.ι_map]; rw [assoc]; rw [colimit.ι_pre]
  rfl

/--
theorem `colimit.pre_map'` / 定理 `colimit.pre_map'`

English:
theorem colimit.pre_map'
  given: [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂)
  proof: by
  ext1
  simp

中文:
定理 colimit.pre_map'
  条件: [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂)
  证明: by
  ext1
  simp
-/
theorem colimit.pre_map' [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    colimit.pre F E₁ = colim.map (whiskerRight α F) ≫ colimit.pre F E₂ := by
  ext1
  simp

/--
theorem `colimit.pre_id` / 定理 `colimit.pre_id`

English:
theorem colimit.pre_id
  given: (F : J ⥤ C)
  proof: by cat_disch

中文:
定理 colimit.pre_id
  条件: (F : J ⥤ C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem colimit.pre_id (F : J ⥤ C) :
    colimit.pre F (𝟭 _) = colim.map (Functor.leftUnitor F).hom := by cat_disch

/--
theorem `colimit.map_post` / 定理 `colimit.map_post`

English:
theorem colimit.map_post
  statement: {D : Type u'} [Category.{v'} D] [HasColimitsOfShape J D]
  proof: by
  ext
  rw [← assoc]; rw [colimit.ι_post]; rw [← H.map_comp]; rw [colimit.ι_map]; rw [H.map_comp]
  rw [← assoc]; rw [colimit.ι_map]; rw [assoc]; rw [colimit.ι_post]
  rfl

中文:
定理 colimit.map_post
  结论: {D : 类型u'} [Category.{v'} D] [HasColimitsOfShape J D]
  证明: by
  ext
  rw [← assoc]; rw [colimit.ι_post]; rw [← H.map_comp]; rw [colimit.ι_map]; rw [H.map_comp]
  rw [← assoc]; rw [colimit.ι_map]; rw [assoc]; rw [colimit.ι_post]
  rfl

Depends on / 依赖: H.map_comp, colimit, map_comp
-/
theorem colimit.map_post {D : Type u'} [Category.{v'} D] [HasColimitsOfShape J D]
    (H : C ⥤ D) :
    /- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
      H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
    colimit.post F H ≫ H.map (colim.map α) =
      colim.map (whiskerRight α H) ≫ colimit.post G H := by
  ext
  rw [← assoc]; rw [colimit.ι_post]; rw [← H.map_comp]; rw [colimit.ι_map]; rw [H.map_comp]
  rw [← assoc]; rw [colimit.ι_map]; rw [assoc]; rw [colimit.ι_post]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `colimCoyoneda` / `colimCoyoneda` 的定义

English:
definition colimCoyoneda
  signature: : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
  body: NatIso.ofComponents fun F => NatIso.ofComponents fun W => colimit.homIso (unop F) W

中文:
定义 colimCoyoneda
  签名: : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
  定义体: NatIso.ofComponents fun F => NatIso.ofComponents fun W => colimit.homIso (unop F) W

Depends on / 依赖: NatIso, NatIso.ofComponents, colimit, colimit.homIso, homIso, ofComponents
-/
def colimCoyoneda : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
    ≅ CategoryTheory.cocones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => colimit.homIso (unop F) W

/--
Definition of `colimConstAdj` / `colimConstAdj` 的定义

English:
definition colimConstAdj
  signature: : (colim : (J ⥤ C) ⥤ C) ⊣ const J
  body: Adjunction.mk' {
  homEquiv := fun f c =>
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fu

中文:
定义 colimConstAdj
  签名: : (colim : (J ⥤ C) ⥤ C) ⊣ const J
  定义体: Adjunction.mk' {
  homEquiv := fun f c =>
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fu

Depends on / 依赖: Adjunction, Adjunction.mk
-/
def colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ const J := Adjunction.mk' {
  homEquiv := fun f c =>
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fun _ => colimit.desc _ ⟨_, 𝟙 _⟩ } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLeftAdjoint (colim : (J ⥤ C) ⥤ C)
  body: ⟨_, ⟨colimConstAdj⟩⟩

中文:
实例 :
  签名: IsLeftAdjoint (colim : (J ⥤ C) ⥤ C)
  定义体: ⟨_, ⟨colimConstAdj⟩⟩

Depends on / 依赖: colimConstAdj
-/
instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨colimConstAdj⟩⟩

end ColimFunctor

/--
Instance `colimMap_epi'` / 实例 `colimMap_epi'`

English:
instance colimMap_epi'
  signature: {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α]
  body: (colim : (J ⥤ C) ⥤ C).map_epi α

中文:
实例 colimMap_epi'
  签名: {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α]
  定义体: (colim : (J ⥤ C) ⥤ C).map_epi α

Depends on / 依赖: map_epi
-/
instance colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α

/--
Instance `colimMap_epi` / 实例 `colimMap_epi`

English:
instance colimMap_epi
  signature: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [forall j, Epi (α.app j)]
  body: ⟨fun {Z} u v h =>
colimit.hom_ext fun j => (cancel_epi (α.app j)).1 by simpa using colimit.ι _ j ≫= h⟩

中文:
实例 colimMap_epi
  签名: {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [对任意 j, Epi (α.app j)]
  定义体: ⟨fun {Z} u v h =>
colimit.hom_ext fun j => (cancel_epi (α.app j)).1 by simpa using colimit.ι _ j ≫= h⟩

Depends on / 依赖: cancel_epi, colimit, colimit.hom_ext, hom_ext
-/
instance colimMap_epi {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [forall j, Epi (α.app j)] :
    Epi (colimMap α) :=
  ⟨fun {Z} u v h =>
colimit.hom_ext fun j => (cancel_epi (α.app j)).1 by simpa using colimit.ι _ j ≫= h⟩

/--
theorem `hasColimitsOfShape_of_equivalence` / 定理 `hasColimitsOfShape_of_equivalence`

English:
theorem hasColimitsOfShape_of_equivalence
  statement: {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
  proof: by
  constructor
  intro F
  apply hasColimit_of_equivalence_comp e

中文:
定理 hasColimitsOfShape_of_equivalence
  结论: {J' : 类型u₂} [Category.{v₂} J'] (e : J ≌ J')
  证明: by
  constructor
  intro F
  apply hasColimit_of_equivalence_comp e

Depends on / 依赖: hasColimit_of_equivalence_comp
-/
theorem hasColimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasColimitsOfShape J C] : HasColimitsOfShape J' C := by
  constructor
  intro F
  apply hasColimit_of_equivalence_comp e

variable (C)

/--
lemma `HasColimitsOfShape.of_small` / 引理 `HasColimitsOfShape.of_small`

English:
lemma HasColimitsOfShape.of_small
  proof: by
  have := HasColimitsOfSize.has_colimits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

中文:
引理 HasColimitsOfShape.of_small
  证明: by
  have := HasColimitsOfSize.has_colimits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

Depends on / 依赖: HasColimitsOfSize, HasColimitsOfSize.has_colimits_of_shape, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, equivalence, hasColimitsOfShape_of_equivalence, has_colimits_of_shape, symm.trans
-/
lemma HasColimitsOfShape.of_small
    [HasColimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [Small.{u₁} J] [LocallySmall.{v₁} J] :
    HasColimitsOfShape J C := by
  have := HasColimitsOfSize.has_colimits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

/--
lemma `HasColimitsOfShape.of_essentiallySmall` / 引理 `HasColimitsOfShape.of_essentiallySmall`

English:
lemma HasColimitsOfShape.of_essentiallySmall
  proof: by
  have := HasColimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasColimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

中文:
引理 HasColimitsOfShape.of_essentiallySmall
  证明: by
  have := HasColimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasColimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

Depends on / 依赖: HasColimitsOfShape, HasColimitsOfShape.of_small, SmallModel, equivSmallModel, hasColimitsOfShape_of_equivalence, of_small
-/
lemma HasColimitsOfShape.of_essentiallySmall
    [HasColimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [EssentiallySmall.{u₁} J] [LocallySmall.{v₁} J] :
    HasColimitsOfShape J C := by
  have := HasColimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasColimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

/--
theorem `hasColimitsOfSizeOfUnivLE` / 定理 `hasColimitsOfSizeOfUnivLE`

English:
theorem hasColimitsOfSizeOfUnivLE
  statement: [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
  proof: hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

中文:
定理 hasColimitsOfSizeOfUnivLE
  结论: [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
  证明: hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

Depends on / 依赖: hasColimitsOfShape_of_equivalence
-/
theorem hasColimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfSize.{v₂, u₂} C where
  has_colimits_of_shape J {_} := hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

/--
theorem `hasColimitsOfSizeShrink` / 定理 `hasColimitsOfSizeShrink`

English:
theorem hasColimitsOfSizeShrink
  given: [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C]
  proof: hasColimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

中文:
定理 hasColimitsOfSizeShrink
  条件: [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C]
  证明: hasColimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

Depends on / 依赖: hasColimitsOfSizeOfUnivLE
-/
theorem hasColimitsOfSizeShrink [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasColimitsOfSize.{v₁, u₁} C := hasColimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

instance (priority := 100) hasSmallestColimitsOfHasColimits [HasColimits C] :
    HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink.{0, 0} C

end Colimit

section Opposite

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsLimit.op` / `IsLimit.op` 的定义

English:
definition IsLimit.op
  signature: {t : Cone F} (P : IsLimit t)
  body: (P.lift s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

中文:
定义 IsLimit.op
  签名: {t : Cone F} (P : IsLimit t)
  定义体: (P.lift s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

Depends on / 依赖: P.lift, s.unop
-/
def IsLimit.op {t : Cone F} (P : IsLimit t) : IsColimit t.op where
  desc s := (P.lift s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsColimit.op` / `IsColimit.op` 的定义

English:
definition IsColimit.op
  signature: {t : Cocone F} (P : IsColimit t)
  body: (P.desc s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

中文:
定义 IsColimit.op
  签名: {t : Cocone F} (P : IsColimit t)
  定义体: (P.desc s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

Depends on / 依赖: P.desc, s.unop
-/
def IsColimit.op {t : Cocone F} (P : IsColimit t) : IsLimit t.op where
  lift s := (P.desc s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsLimit.unop` / `IsLimit.unop` 的定义

English:
definition IsLimit.unop
  signature: {t : Cone F.op} (P : IsLimit t)
  body: (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

中文:
定义 IsLimit.unop
  签名: {t : Cone F.op} (P : IsLimit t)
  定义体: (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

Depends on / 依赖: P.lift, s.op
-/
def IsLimit.unop {t : Cone F.op} (P : IsLimit t) : IsColimit t.unop where
  desc s := (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsColimit.unop` / `IsColimit.unop` 的定义

English:
definition IsColimit.unop
  signature: {t : Cocone F.op} (P : IsColimit t)
  body: (P.desc s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

中文:
定义 IsColimit.unop
  签名: {t : Cocone F.op} (P : IsColimit t)
  定义体: (P.desc s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

Depends on / 依赖: P.desc, s.op
-/
def IsColimit.unop {t : Cocone F.op} (P : IsColimit t) : IsLimit t.unop where
  lift s := (P.desc s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

/--
Definition of `isLimitOfOp` / `isLimitOfOp` 的定义

English:
definition isLimitOfOp
  signature: {t : Cone F} (P : IsColimit t.op)
  body: P.unop

中文:
定义 isLimitOfOp
  签名: {t : Cone F} (P : IsColimit t.op)
  定义体: P.unop

Depends on / 依赖: P.unop
-/
def isLimitOfOp {t : Cone F} (P : IsColimit t.op) : IsLimit t :=
  P.unop

/--
Definition of `isColimitOfOp` / `isColimitOfOp` 的定义

English:
definition isColimitOfOp
  signature: {t : Cocone F} (P : IsLimit t.op)
  body: P.unop

中文:
定义 isColimitOfOp
  签名: {t : Cocone F} (P : IsLimit t.op)
  定义体: P.unop

Depends on / 依赖: P.unop
-/
def isColimitOfOp {t : Cocone F} (P : IsLimit t.op) : IsColimit t :=
  P.unop

/--
Definition of `isLimitOfUnop` / `isLimitOfUnop` 的定义

English:
definition isLimitOfUnop
  signature: {t : Cone F.op} (P : IsColimit t.unop)
  body: P.op

中文:
定义 isLimitOfUnop
  签名: {t : Cone F.op} (P : IsColimit t.unop)
  定义体: P.op

Depends on / 依赖: P.op
-/
def isLimitOfUnop {t : Cone F.op} (P : IsColimit t.unop) : IsLimit t :=
  P.op

/--
Definition of `isColimitOfUnop` / `isColimitOfUnop` 的定义

English:
definition isColimitOfUnop
  signature: {t : Cocone F.op} (P : IsLimit t.unop)
  body: P.op

中文:
定义 isColimitOfUnop
  签名: {t : Cocone F.op} (P : IsLimit t.unop)
  定义体: P.op

Depends on / 依赖: P.op
-/
def isColimitOfUnop {t : Cocone F.op} (P : IsLimit t.unop) : IsColimit t :=
  P.op

/--
Definition of `isLimitEquivIsColimitOp` / `isLimitEquivIsColimitOp` 的定义

English:
definition isLimitEquivIsColimitOp
  signature: {t : Cone F}
  body: equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

中文:
定义 isLimitEquivIsColimitOp
  签名: {t : Cone F}
  定义体: equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

Depends on / 依赖: IsLimit, IsLimit.op, equivOfSubsingletonOfSubsingleton, isLimitOfOp
-/
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

/--
Definition of `isColimitEquivIsLimitOp` / `isColimitEquivIsLimitOp` 的定义

English:
definition isColimitEquivIsLimitOp
  signature: {t : Cocone F}
  body: equivOfSubsingletonOfSubsingleton IsColimit.op isColimitOfOp

中文:
定义 isColimitEquivIsLimitOp
  签名: {t : Cocone F}
  定义体: equivOfSubsingletonOfSubsingleton IsColimit.op isColimitOfOp

Depends on / 依赖: IsColimit, IsColimit.op, equivOfSubsingletonOfSubsingleton, isColimitOfOp
-/
def isColimitEquivIsLimitOp {t : Cocone F} : IsColimit t ≃ IsLimit t.op :=
  equivOfSubsingletonOfSubsingleton IsColimit.op isColimitOfOp

end Opposite

end Limits

end CategoryTheory
