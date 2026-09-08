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

/-- `LimitCone F` contains a cone over `F` together with the information that it is a limit. -/
/-
**CategoryTheory.Limits.LimitCone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} → [inst_1 : CategoryTheory.Category.{v, u} C] → CategoryTheory.Functor J 
C → Type (max (max u u₁) v)
参数：max (max u u₁) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LimitCone F` contains a cone over `F` together with the information that it is 
a limit.
-/
structure LimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isLimit : IsLimit cone

/-- `ColimitCocone F` contains a cocone over `F` together with the information that it is a
colimit. -/
@[to_dual]
/-
**CategoryTheory.Limits.ColimitCocone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} → [inst_1 : CategoryTheory.Category.{v, u} C] → CategoryTheory.Functor J 
C → Type (max (max u u₁) v)
参数：max (max u u₁) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ColimitCocone F` contains a cocone over `F` together with the information that 
it is a
colimit.
-/
structure ColimitCocone (F : J ⥤ C) where
  /-- The cocone itself -/
  cocone : Cocone F
  /-- The proof that it is the colimit cocone -/
  isColimit : IsColimit cocone

/-- `HasLimit F` represents the mere existence of a limit for `F`. -/
/-
**CategoryTheory.Limits.HasLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} → [inst_1 : CategoryTheory.Category.{v, u} C] → CategoryTheory.Functor J 
C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasLimit F` represents the mere existence of a limit for `F`.
-/
class HasLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (LimitCone F)

/-- `HasColimit F` represents the mere existence of a colimit for `F`. -/
@[to_dual]
/-
**CategoryTheory.Limits.HasColimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} → [inst_1 : CategoryTheory.Category.{v, u} C] → CategoryTheory.Functor J 
C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasColimit F` represents the mere existence of a colimit for `F`.
-/
class HasColimit (F : J ⥤ C) : Prop where mk' ::
  /-- There exists a colimit for `F` -/
  exists_colimit : Nonempty (ColimitCocone F)

@[to_dual]
/-
**CategoryTheory.Limits.HasLimit.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits.HasLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} (d
 : CategoryTheory.Limits.LimitCone F), CategoryTheory.Limits.HasLimit F
参数：d : CategoryTheory.Limits.LimitCone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `LimitCone F` from `HasLimit F`. -/
@[no_expose, to_dual
/-- Use the axiom of choice to extract explicit `ColimitCocone F` from `HasColimit F`. -/]
/-
**CategoryTheory.Limits.getLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F
参数：F : J ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.exists_limit`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} {C : Type u} {inst_1 : CategoryTheory.Category.
{v, u} C}   {F : CategoryTheory.F…
-/
def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
  Classical.choice <| HasLimit.exists_limit

variable (J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
/-
**CategoryTheory.Limits.HasLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：HasLimitsOfShape : Prop where /-- All functors `F : J ⥤ C` from `J` have l
imits -/ has_limit : forall F : J ⥤ C, HasLimit F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C
`.
-/
class HasLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_limit : ∀ F : J ⥤ C, HasLimit F := by infer_instance

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
@[to_dual]
/-
**CategoryTheory.Limits.HasColimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：HasColimitsOfShape : Prop where /-- All `F : J ⥤ C` have colimits for a fi
xed `J` -/ has_colimit : forall F : J ⥤ C, HasColimit F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has colimits of shape `J` if there exists a colimit for every functor `F : J
 ⥤ C`.
-/
class HasColimitsOfShape : Prop where
  /-- All `F : J ⥤ C` have colimits for a fixed `J` -/
  has_colimit : ∀ F : J ⥤ C, HasColimit F := by infer_instance

/-- `C` has all limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.HasLimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where /-- All functor
s `F : J ⥤ C` from all small `J` have limits -/ has_limits_of_shape : forall (J 
: Type u₁) [Category.{v₁} J], HasLimitsOfShape J C
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have limits -/
  has_limits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C := by
    infer_instance

/-- `C` has all colimits of size `v₁ u₁` (`HasColimitsOfSize.{v₁ u₁} C`)
if it has colimits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[to_dual, univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.HasColimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where /-- All `F : 
J ⥤ C` have colimits for all small `J` -/ has_colimits_of_shape : forall (J : Ty
pe u₁) [Category.{v₁} J], HasColimitsOfShape J C
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All `F : J ⥤ C` have colimits for all small `J` -/
  has_colimits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C := by
    infer_instance

/-- `C` has all (small) limits if it has limits of every shape that is as big as its hom-sets. -/
@[to_dual
/-- `C` has all (small) colimits if it has colimits of every shape that is as big as its hom-sets.
-/]
/-
**CategoryTheory.Limits.HasLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：HasLimits (C : Type u) [Category.{v} C] : Prop
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev HasLimits (C : Type u) [Category.{v} C] : Prop :=
  HasLimitsOfSize.{v, v} C

@[to_dual]
/-
**CategoryTheory.Limits.HasLimits.has_limits_of_shape** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.HasLimits`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasLimits C] (J : Type v)   [inst_2 : CategoryTheory.Category.{v, v} J], C
ategoryTheory.Limits.HasLimitsOfShape J C
参数：J : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimitsOfSize.has_limits_of_shape`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasLim
itsOfSize.{v₁, u₁, v, u} C]   (J : Type u₁) [in…
-/
theorem HasLimits.has_limits_of_shape {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
    [Category.{v} J] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

variable {J C}

-- see Note [lower instance priority]
@[to_dual]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfShape J C] (F : J ⥤ C) : HasLimit F :=
  HasLimitsOfShape.has_limit F

-- see Note [lower instance priority]
@[to_dual]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

-- Interface to the `HasLimit` class.
/-- An arbitrary choice of limit cone for a functor. -/
@[to_dual colimit.cocone /-- An arbitrary choice of colimit cocone of a functor. -/]
/-
**CategoryTheory.Limits.limit.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) → [CategoryTheory.Limits.HasLimit F] → CategoryTheory.Limi
ts.Cone F
参数：F : CategoryTheory.Functor J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of limit cone for a functor.
-/
def limit.cone (F : J ⥤ C) [HasLimit F] : Cone F :=
  (getLimitCone F).cone

/-- An arbitrary choice of limit object of a functor. -/
@[to_dual (attr := implicit_reducible) /-- An arbitrary choice of colimit object of a functor. -/]
/-
**CategoryTheory.Limits.limit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：limit (F : J ⥤ C) [HasLimit F]
参数：F : J ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of limit object of a functor.
-/
def limit (F : J ⥤ C) [HasLimit F] :=
  (limit.cone F).pt

/-- The projection from the limit object to a value of the functor. -/
@[to_dual (attr := implicit_reducible) ι
/-- The coprojection from a value of the functor to the colimit object. -/]
/-
**CategoryTheory.Limits.limit.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def limit.π (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  (limit.cone F).π.app j
/-
**CategoryTheory.Limits.limit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.π_comp_eqToHom (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j') :
    limit.π F j ≫ eqToHom (by subst hj; rfl) = limit.π F j' := by
  subst hj
  simp

@[to_dual existing (attr := reassoc) π_comp_eqToHom]
/-
**CategoryTheory.Limits.colimit.eqToHom_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.eqToHom_comp_ι (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j') :
    eqToHom (by subst hj; rfl) ≫ colimit.ι F j = colimit.ι F j' := by
  subst hj
  simp

@[to_dual (attr := simp)]
/-
**CategoryTheory.Limits.limit.cone_x** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F],   (CategoryTheory.Limits.limit.cone F
).pt = CategoryTheory.Limits.limit F
参数：CategoryTheory.Limits.limit.cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.cone_x {F : J ⥤ C} [HasLimit F] : (limit.cone F).pt = limit F :=
  rfl

@[to_dual (attr := simp) cocone_ι]
/-
**CategoryTheory.Limits.limit.cone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.cone_π {F : J ⥤ C} [HasLimit F] : (limit.cone F).π.app = limit.π _ :=
  rfl

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Limits.limit.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor J C) [i
nst_2 : CategoryTheory.Limits.HasLimit F] {j j' : J} (f : j ⟶ j'),   CategoryThe
ory.CategoryStruct.comp (CategoryTheory.Limits.limit.π F j) (F.map f) = Category
Theory.Limits.limit.π F j'
参数：F : CategoryTheory.Functor J C；f : j ⟶ j'；CategoryTheory.Limits.limit.π F j；F
.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
-/
theorem limit.w (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' :=
  (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `limit.cone F` is a limit cone. -/
@[to_dual
/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/]
/-
**CategoryTheory.Limits.limit.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasLimit F] → 
            CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.limit.cone F)
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.limit.cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def limit.isLimit (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  (getLimitCone F).isLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
@[to_dual
/-- The morphism from the colimit object to the cone point of any other cocone. -/]
/-
**CategoryTheory.Limits.limit.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasLimit F] → 
            (c : CategoryTheory.Limits.Cone F) → c.pt ⟶ CategoryTheory.Limits.li
mit F
参数：F : CategoryTheory.Functor J C；c : CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def limit.lift (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  (limit.isLimit F).lift c

@[to_dual (attr := simp)]
/-
**CategoryTheory.Limits.limit.isLimit_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] (c : CategoryTheory.Limits.Cone F),   
(CategoryTheory.Limits.limit.isLimit F).lift c = CategoryTheory.Limits.limit.lif
t F c
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.Limits.limit.isLimit F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.isLimit_lift {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.isLimit F).lift c = limit.lift F c :=
  rfl

@[to_dual (attr := reassoc (attr := simp)) ι_desc]
/-
**CategoryTheory.Limits.limit.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Limits.limMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ lim
it G
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  IsLimit.map _ (limit.isLimit G) α

@[to_dual (attr := reassoc (attr := simp)) ι_colimMap]
/-
**CategoryTheory.Limits.limMap_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limMap_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
@[to_dual /-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/]
/-
**CategoryTheory.Limits.limit.coneMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           [inst_2 : CategoryTheory.Limits.HasLimit F] → 
            (c : CategoryTheory.Limits.Cone F) → c ⟶ CategoryTheory.Limits.limit
.cone F
参数：c : CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone morphism from any cone to the arbitrary choice of limit cone.
-/
def limit.coneMorphism {F : J ⥤ C} [HasLimit F] (c : Cone F) : c ⟶ limit.cone F :=
  (limit.isLimit F).liftConeMorphism c

@[to_dual (attr := simp)]
/-
**CategoryTheory.Limits.limit.coneMorphism_hom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] (c : CategoryTheory.Limits.Cone F),   
(CategoryTheory.Limits.limit.coneMorphism c).hom = CategoryTheory.Limits.limit.l
ift F c
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.Limits.limit.coneMorphism c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.coneMorphism_hom {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.coneMorphism c).hom = limit.lift F c :=
  rfl

@[to_dual ι_coconeMorphism]
/-
**CategoryTheory.Limits.limit.coneMorphism_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.coneMorphism_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    (limit.coneMorphism c).hom ≫ limit.π F j = c.π.app j := by simp

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]
/-
**CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] {c : CategoryTheory.Limits.Cone F}   (
hc : CategoryTheory.Limits.IsLimit c) (j : J),   CategoryTheory.CategoryStruct.c
omp (hc.conePointUniqueUpToIso (CategoryTheory.Limits.limit.isLimit F)).hom     
  (CategoryTheory.Limits.limit.π F j) =     c.π.app j
参数：hc : CategoryTheory.Limits.IsLimit c；j : J；hc.conePointUniqueUpToIso (Categor
yTheory.Limits.limit.isLimit F)；CategoryTheory.Limits.limit.π F j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem limit.conePointUniqueUpToIso_hom_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso hc (limit.isLimit _)).hom ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]
/-
**CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] {c : CategoryTheory.Limits.Cone F}   (
hc : CategoryTheory.Limits.IsLimit c) (j : J),   CategoryTheory.CategoryStruct.c
omp ((CategoryTheory.Limits.limit.isLimit F).conePointUniqueUpToIso hc).inv     
  (CategoryTheory.Limits.limit.π F j) =     c.π.app j
参数：hc : CategoryTheory.Limits.IsLimit c；j : J；(CategoryTheory.Limits.limit.isLim
it F).conePointUniqueUpToIso hc；CategoryTheory.Limits.limit.π F j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem limit.conePointUniqueUpToIso_inv_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc).inv ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[to_dual]
/-
**CategoryTheory.Limits.limit.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] (t : CategoryTheory.Limits.Cone F),   
∃! l, ∀ (j : J), CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.lim
it.π F j) = t.π.app j
参数：t : CategoryTheory.Limits.Cone F；j : J；CategoryTheory.Limits.limit.π F j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.existsUnique`：existsUnique {t : Cone F} (h
 : IsLimit t) (s : Cone F) : exists! l : s.pt ⟶ t.pt, forall j, l ≫ t.π.app j = 
s.π.app j
-/
theorem limit.existsUnique {F : J ⥤ C} [HasLimit F] (t : Cone F) :
    ∃! l : t.pt ⟶ limit F, ∀ j, l ≫ limit.π F j = t.π.app j :=
  (limit.isLimit F).existsUnique _

/-- Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point. -/
@[to_dual
/-- Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone
point. -/]
/-
**CategoryTheory.Limits.limit.isoLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           [inst_2 : CategoryTheory.Limits.HasLimit F] → 
            (t : CategoryTheory.Limits.LimitCone F) → CategoryTheory.Limits.limi
t F ≅ t.cone.pt
参数：t : CategoryTheory.Limits.LimitCone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def limit.isoLimitCone {F : J ⥤ C} [HasLimit F] (t : LimitCone F) : limit F ≅ t.cone.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_inv]
/-
**CategoryTheory.Limits.limit.isoLimitCone_hom_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.isoLimitCone_hom_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).hom ≫ t.cone.π.app j = limit.π F j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_hom]
/-
**CategoryTheory.Limits.limit.isoLimitCone_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.isoLimitCone_inv_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := ext)]
/-
**CategoryTheory.Limits.limit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] {X : C}   {f f' : X ⟶ CategoryTheory.L
imits.limit F},   (∀ (j : J),       CategoryTheory.CategoryStruct.comp f (Catego
ryTheory.Limits.limit.π F j) =         CategoryTheory.CategoryStruct.comp f' (Ca
tegoryTheory.Limits.limit.π F j)) →     f = f'
参数：∀ (j : J),       CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.
limit.π F j) =         CategoryTheory.CategoryStruct.comp f' (CategoryTheory.Lim
its.limit.π F j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
theorem limit.hom_ext {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.isLimit F).hom_ext w

@[to_dual]
/-
**CategoryTheory.Limits.isIso_limMap** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：isIso_limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [IsIso α]
 : IsIso (limMap α)
参数：α : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.limMap_π_assoc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
instance isIso_limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [IsIso α] :
    IsIso (limMap α) :=
  ⟨limMap (inv α), by cat_disch , by cat_disch⟩

@[to_dual (attr := reassoc (attr := simp)) map_desc]
/-
**CategoryTheory.Limits.limit.lift_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
[inst_2 : CategoryTheory.Limits.HasLimit F]   [inst_3 : CategoryTheory.Limits.Ha
sLimit G] (c : CategoryTheory.Limits.Cone F) (α : F ⟶ G),   CategoryTheory.Categ
oryStruct.comp (CategoryTheory.Limits.limit.lift F c) (CategoryTheory.Limits.lim
Map α) =     CategoryTheory.Limits.limit.lift G ((CategoryTheory.Limits.Cone.pos
tcompose α).obj c)
参数：c : CategoryTheory.Limits.Cone F；α : F ⟶ G；CategoryTheory.Limits.limit.lift F
 c；CategoryTheory.Limits.limMap α；(CategoryTheory.Limits.Cone.postcompose α).obj
 c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem limit.lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cone.postcompose α).obj c) := by
  ext
  rw [assoc, limMap_π, limit.lift_π_assoc, limit.lift_π]
  rfl

@[to_dual (attr := simp)]
/-
**CategoryTheory.Limits.limit.lift_cone** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F],   CategoryTheory.Limits.limit.lift F 
(CategoryTheory.Limits.limit.cone F) =     CategoryTheory.CategoryStruct.id (Cat
egoryTheory.Limits.limit F)
参数：CategoryTheory.Limits.limit.cone F；CategoryTheory.Limits.limit F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.lift_self`：lift_self {c : Cone F} (t : IsL
imit c) : t.lift c = 𝟙 c.pt
-/
theorem limit.lift_cone {F : J ⥤ C} [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  (limit.isLimit _).lift_self

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
/-
**CategoryTheory.Limits.limit.homIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasLimit F] → 
            (W : C) → ULift.{u₁, v} (W ⟶ CategoryTheory.Limits.limit F) ≅ F.cone
s.obj (Opposite.op W)
参数：F : CategoryTheory.Functor J C；W : C；W ⟶ CategoryTheory.Limits.limit F；Opposi
te.op W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W

@[simp]
/-
**CategoryTheory.Limits.limit.homIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor J C) [i
nst_2 : CategoryTheory.Limits.HasLimit F] {W : C},   (CategoryTheory.Limits.limi
t.homIso F W).hom =     TypeCat.ofHom fun f =>       CategoryTheory.CategoryStru
ct.comp ((CategoryTheory.Functor.const J).map f.down)         (CategoryTheory.Li
mits.limit.cone F).π
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.limit.homIso F W；(Catego
ryTheory.Functor.const J).map f.down；CategoryTheory.Limits.limit.cone F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.homIso_hom`：homIso_hom (h : IsLimit t) {W 
: C} : (IsLimit.homIso h W).hom = ↾fun f => (t.extend f.down).π
-/
theorem limit.homIso_hom (F : J ⥤ C) [HasLimit F] {W : C} :
    (limit.homIso F W).hom = ↾fun f ↦ (const J).map f.down ≫ (limit.cone F).π :=
  (limit.isLimit F).homIso_hom

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
/-
**CategoryTheory.Limits.limit.homIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasLimit F] → 
            (W : C) →               ULift.{u₁, v} (W ⟶ CategoryTheory.Limits.lim
it F) ≅                 { p // ∀ {j j' : J} (f : j ⟶ j'), CategoryTheory.Categor
yStruct.comp (p j) (F.map f) = p j' }
参数：F : CategoryTheory.Functor J C；W : C；W ⟶ CategoryTheory.Limits.limit F；f : j 
⟶ j'；p j；F.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.homIso' (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅
      { p : ∀ j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  (limit.isLimit F).homIso' W

@[to_dual]
/-
**CategoryTheory.Limits.limit.lift_extend** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimit F] (c : CategoryTheory.Limits.Cone F)   {
X : C} (f : X ⟶ c.pt),   CategoryTheory.Limits.limit.lift F (c.extend f) =     C
ategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.limit.lift F c)
参数：c : CategoryTheory.Limits.Cone F；f : X ⟶ c.pt；c.extend f；CategoryTheory.Limit
s.limit.lift F c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit.lift_extend {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    limit.lift F (c.extend f) = f ≫ limit.lift F c := by cat_disch

/-- If a functor `F` has a limit, so does any naturally isomorphic functor. -/
@[to_dual none]
/-
**CategoryTheory.Limits.hasLimit_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：hasLimit_of_iso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G
参数：α : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
theorem hasLimit_of_iso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G :=
  HasLimit.mk
    { cone := (Cone.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }

@[to_dual]
/-
**CategoryTheory.Limits.hasLimit_iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：hasLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
参数：α : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
-/
theorem hasLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G :=
  ⟨fun _ ↦ hasLimit_of_iso α, fun _ ↦ hasLimit_of_iso α.symm⟩

-- See the construction of limits from products and equalizers
-- for an example usage.
/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
/-
**CategoryTheory.Limits.HasLimit.ofConesIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.HasLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J K : Type u₁} [
inst_1 : CategoryTheory.Category.{v₁, u₁} J]   [inst_2 : CategoryTheory.Category
.{v₂, u₁} K] (F : CategoryTheory.Functor J C) (G : CategoryTheory.Functor K C)  
 (h : F.cones ≅ G.cones) [CategoryTheory.Limits.HasLimit F], CategoryTheory.Limi
ts.HasLimit G
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor K C；h : F.cones ≅ G
.cones。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit.
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
/-
**CategoryTheory.Limits.HasLimit.isoOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.HasLimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F G : Cate
goryTheory.Functor J C} →           [inst_2 : CategoryTheory.Limits.HasLimit F] 
→             [inst_3 : CategoryTheory.Limits.HasLimit G] →               (F ≅ G
) → (CategoryTheory.Limits.limit F ≅ CategoryTheory.Limits.limit G)
参数：F ≅ G；CategoryTheory.Limits.limit F ≅ CategoryTheory.Limits.limit G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasLimit.isoOfNatIso {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasLimit.isoOfNatIso_hom_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasLimit.isoOfNatIso_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasLimit.isoOfNatIso_inv_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).inv ≫ limit.π F j = limit.π G j ≫ w.inv.app j :=
  IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasLimit.lift_isoOfNatIso_hom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.HasLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
[inst_2 : CategoryTheory.Limits.HasLimit F]   [inst_3 : CategoryTheory.Limits.Ha
sLimit G] (t : CategoryTheory.Limits.Cone F) (w : F ≅ G),   CategoryTheory.Categ
oryStruct.comp (CategoryTheory.Limits.limit.lift F t)       (CategoryTheory.Limi
ts.HasLimit.isoOfNatIso w).hom =     CategoryTheory.Limits.limit.lift G ((Catego
ryTheory.Limits.Cone.postcompose w.hom).obj t)
参数：t : CategoryTheory.Limits.Cone F；w : F ≅ G；CategoryTheory.Limits.limit.lift F
 t；CategoryTheory.Limits.HasLimit.isoOfNatIso w；(CategoryTheory.Limits.Cone.post
compose w.hom).obj t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.lift_comp_conePointsIsoOfNatIso_hom`：lift_
comp_conePointsIsoOfNatIso_hom {F G : J ⥤ C} {r s : Cone F} {t : Cone G} (P : Is
Limit s) (Q : IsLimit t) (w : F ≅ G) : P.lift r ≫ (cone…
-/
theorem HasLimit.lift_isoOfNatIso_hom {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
    (w : F ≅ G) :
    limit.lift F t ≫ (HasLimit.isoOfNatIso w).hom =
      limit.lift G ((Cone.postcompose w.hom).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasLimit.lift_isoOfNatIso_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.HasLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
[inst_2 : CategoryTheory.Limits.HasLimit F]   [inst_3 : CategoryTheory.Limits.Ha
sLimit G] (t : CategoryTheory.Limits.Cone G) (w : F ≅ G),   CategoryTheory.Categ
oryStruct.comp (CategoryTheory.Limits.limit.lift G t)       (CategoryTheory.Limi
ts.HasLimit.isoOfNatIso w).inv =     CategoryTheory.Limits.limit.lift F ((Catego
ryTheory.Limits.Cone.postcompose w.inv).obj t)
参数：t : CategoryTheory.Limits.Cone G；w : F ≅ G；CategoryTheory.Limits.limit.lift G
 t；CategoryTheory.Limits.HasLimit.isoOfNatIso w；(CategoryTheory.Limits.Cone.post
compose w.inv).obj t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.lift_comp_conePointsIsoOfNatIso_inv`：lift_
comp_conePointsIsoOfNatIso_inv {F G : J ⥤ C} {r s : Cone G} {t : Cone F} (P : Is
Limit t) (Q : IsLimit s) (w : F ≅ G) : Q.lift r ≫ (cone…
-/
theorem HasLimit.lift_isoOfNatIso_inv {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
    (w : F ≅ G) :
    limit.lift G t ≫ (HasLimit.isoOfNatIso w).inv =
      limit.lift F ((Cone.postcompose w.inv).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _

/-- The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
/-
**CategoryTheory.Limits.HasLimit.isoOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.HasLimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u} →           [inst_2 : CategoryTheory.Category.{v, u} C] →             {F : 
CategoryTheory.Functor J C} →               [inst_3 : CategoryTheory.Limits.HasL
imit F] →                 {G : CategoryTheory.Functor K C} →                   [
inst_4 : CategoryTheory.Limits.HasLimit G] →                     (e : J ≌ K) →  
                     (e.functor.comp G ≅ F) → (CategoryTheory.Limits.limit F ≅ C
ategoryTheory.Limits.limit G)
参数：e : J ≌ K；e.functor.comp G ≅ F；CategoryTheory.Limits.limit F ≅ CategoryTheory
.Limits.limit G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural
 isomorphism.
-/
def HasLimit.isoOfEquivalence {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasLimit.isoOfEquivalence_hom_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasLimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    (HasLimit.isoOfEquivalence e w).hom ≫ limit.π G k =
      limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasLimit.isoOfEquivalence_inv_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
/-
**CategoryTheory.Limits.limit.pre** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u} →           [inst_2 : CategoryTheory.Category.{v, u} C] →             (F : 
CategoryTheory.Functor J C) →               [inst_3 : CategoryTheory.Limits.HasL
imit F] →                 (E : CategoryTheory.Functor K J) →                   [
inst_4 : CategoryTheory.Limits.HasLimit (E.comp F)] →                     Catego
ryTheory.Limits.limit F ⟶ CategoryTheory.Limits.limit (E.comp F)
参数：F : CategoryTheory.Functor J C；E : CategoryTheory.Functor K J；E.comp F；E.comp
 F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limit.pre_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) := by
  simp [limit.pre]

@[simp]
/-
**CategoryTheory.Limits.limit.lift_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] (F : CategoryTheory.Functor J C)   [inst_3 : CategoryTh
eory.Limits.HasLimit F] (E : CategoryTheory.Functor K J)   [inst_4 : CategoryThe
ory.Limits.HasLimit (E.comp F)] (c : CategoryTheory.Limits.Cone F),   CategoryTh
eory.CategoryStruct.comp (CategoryTheory.Limits.limit.lift F c) (CategoryTheory.
Limits.limit.pre F E) =     CategoryTheory.Limits.limit.lift (E.comp F) (Categor
yTheory.Limits.Cone.whisker E c)
参数：F : CategoryTheory.Functor J C；E : CategoryTheory.Functor K J；E.comp F；c : Ca
tegoryTheory.Limits.Cone F；CategoryTheory.Limits.limit.lift F c；CategoryTheory.L
imits.limit.pre F E；E.comp F；CategoryTheory.Limits.Cone.whisker E c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit.lift_pre (c : Cone F) :
    limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) := by ext; simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[simp]
/-
**CategoryTheory.Limits.limit.pre_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] (F : CategoryTheory.Functor J C)   [inst_3 : CategoryTh
eory.Limits.HasLimit F] (E : CategoryTheory.Functor K J)   [inst_4 : CategoryThe
ory.Limits.HasLimit (E.comp F)] {L : Type u₃} [inst_5 : CategoryTheory.Category.
{v₃, u₃} L]   (D : CategoryTheory.Functor L K) [h : CategoryTheory.Limits.HasLim
it (D.comp (E.comp F))],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Li
mits.limit.pre F E)       (CategoryTheory.Limits.limit.pre (E.comp F) D) =     C
ategoryTheory.Limits.limit.pre F (D.comp E)
参数：F : CategoryTheory.Functor J C；E : CategoryTheory.Functor K J；E.comp F；D : Ca
tegoryTheory.Functor L K；D.comp (E.comp F)；CategoryTheory.Limits.limit.pre F E；C
ategoryTheory.Limits.limit.pre (E.comp F) D；D.comp E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
-/
theorem limit.pre_pre [h : HasLimit (D ⋙ E ⋙ F)] : haveI : HasLimit ((D ⋙ E) ⋙ F) := h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  have : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl

variable {E F}

/--
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
/-
**CategoryTheory.Limits.limit.pre_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] {F : CategoryTheory.Functor J C}   [inst_3 : CategoryTh
eory.Limits.HasLimit F] {E : CategoryTheory.Functor K J}   [inst_4 : CategoryThe
ory.Limits.HasLimit (E.comp F)] (s : CategoryTheory.Limits.LimitCone (E.comp F))
   (t : CategoryTheory.Limits.LimitCone F),   CategoryTheory.Limits.limit.pre F 
E =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.limit.isoLimit
Cone t).hom       (CategoryTheory.CategoryStruct.comp (s.isLimit.lift (CategoryT
heory.Limits.Cone.whisker E t.cone))         (CategoryTheory.Limits.limit.isoLim
itCone s).inv)
参数：E.comp F；s : CategoryTheory.Limits.LimitCone (E.comp F)；t : CategoryTheory.Li
mits.LimitCone F；CategoryTheory.Limits.limit.isoLimitCone t；CategoryTheory.Categ
oryStruct.comp (s.isLimit.lift (CategoryTheory.Limits.Cone.whisker E t.cone))   
      (CategoryTheory.Limits.limit.isoLimitCone s).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
theorem limit.pre_eq (s : LimitCone (E ⋙ F)) (t : LimitCone F) :
    limit.pre F E = (limit.isoLimitCone t).hom ≫ s.isLimit.lift (t.cone.whisker E) ≫
      (limit.isoLimitCone s).inv := by cat_disch

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]
variable (F : J ⥤ C) [HasLimit F] (G : C ⥤ D) [HasLimit (F ⋙ G)]

/-- The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
/-
**CategoryTheory.Limits.limit.post** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.limit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {D : Type u
'} →           [inst_2 : CategoryTheory.Category.{v', u'} D] →             (F : 
CategoryTheory.Functor J C) →               [inst_3 : CategoryTheory.Limits.HasL
imit F] →                 (G : CategoryTheory.Functor C D) →                   [
inst_4 : CategoryTheory.Limits.HasLimit (F.comp G)] →                     G.obj 
(CategoryTheory.Limits.limit F) ⟶ CategoryTheory.Limits.limit (F.comp G)
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor C D；F.comp G；Catego
ryTheory.Limits.limit F；F.comp G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙
 G`.
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (G.mapCone (limit.cone F))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limit.post_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  simp [limit.post]

@[simp]
/-
**CategoryTheory.Limits.limit.lift_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u'} [inst_2 : CategoryThe
ory.Category.{v', u'} D] (F : CategoryTheory.Functor J C)   [inst_3 : CategoryTh
eory.Limits.HasLimit F] (G : CategoryTheory.Functor C D)   [inst_4 : CategoryThe
ory.Limits.HasLimit (F.comp G)] (c : CategoryTheory.Limits.Cone F),   CategoryTh
eory.CategoryStruct.comp (G.map (CategoryTheory.Limits.limit.lift F c))       (C
ategoryTheory.Limits.limit.post F G) =     CategoryTheory.Limits.limit.lift (F.c
omp G) (G.mapCone c)
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor C D；F.comp G；c : Ca
tegoryTheory.Limits.Cone F；G.map (CategoryTheory.Limits.limit.lift F c)；Category
Theory.Limits.limit.post F G；F.comp G；G.mapCone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.post_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {D : Type u'} [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem limit.lift_post (c : Cone F) :
    G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.mapCone c) := by
  ext
  rw [assoc, limit.post_π, ← G.map_comp, limit.lift_π, limit.lift_π]
  rfl

@[simp]
/-
**CategoryTheory.Limits.limit.post_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u'} [inst_2 : CategoryThe
ory.Category.{v', u'} D] (F : CategoryTheory.Functor J C)   [inst_3 : CategoryTh
eory.Limits.HasLimit F] (G : CategoryTheory.Functor C D)   [inst_4 : CategoryThe
ory.Limits.HasLimit (F.comp G)] {E : Type u''} [inst_5 : CategoryTheory.Category
.{v'', u''} E]   (H : CategoryTheory.Functor D E) [h : CategoryTheory.Limits.Has
Limit ((F.comp G).comp H)],   CategoryTheory.CategoryStruct.comp (H.map (Categor
yTheory.Limits.limit.post F G))       (CategoryTheory.Limits.limit.post (F.comp 
G) H) =     CategoryTheory.Limits.limit.post F (G.comp H)
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor C D；F.comp G；H : Ca
tegoryTheory.Functor D E；(F.comp G).comp H；H.map (CategoryTheory.Limits.limit.po
st F G)；CategoryTheory.Limits.limit.post (F.comp G) H；G.comp H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.post_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {D : Type u'} [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem limit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)] :
    -- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals
    -- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H))
    haveI : HasLimit (F ⋙ G ⋙ H) := h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  have : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl

end Post

/-
**CategoryTheory.Limits.limit.pre_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] {D : Type u'} [inst_3 : CategoryTheory.Category.{v', u'
} D]   (E : CategoryTheory.Functor K J) (F : CategoryTheory.Functor J C) (G : Ca
tegoryTheory.Functor C D)   [inst_4 : CategoryTheory.Limits.HasLimit F] [inst_5 
: CategoryTheory.Limits.HasLimit (E.comp F)]   [inst_6 : CategoryTheory.Limits.H
asLimit (F.comp G)] [h : CategoryTheory.Limits.HasLimit ((E.comp F).comp G)],   
CategoryTheory.CategoryStruct.comp (G.map (CategoryTheory.Limits.limit.pre F E))
       (CategoryTheory.Limits.limit.post (E.comp F) G) =     CategoryTheory.Cate
goryStruct.comp (CategoryTheory.Limits.limit.post F G)       (CategoryTheory.Lim
its.limit.pre (F.comp G) E)
参数：E : CategoryTheory.Functor K J；F : CategoryTheory.Functor J C；G : CategoryThe
ory.Functor C D；E.comp F；F.comp G；(E.comp F).comp G；G.map (CategoryTheory.Limits
.limit.pre F E)；CategoryTheory.Limits.limit.post (E.comp F) G；CategoryTheory.Lim
its.limit.post F G；CategoryTheory.Limits.limit.pre (F.comp G) E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.post_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {D : Type u'} [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
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
/-
**CategoryTheory.Limits.hasLimit_equivalence_comp** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasLimit_equivalence_comp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙
 F)
参数：e : K ≌ J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_equivalence_comp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙ F) :=
  HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }

-- not entirely sure why this is needed
/-- If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
/-
**CategoryTheory.Limits.hasLimit_of_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasLimit_of_equivalence_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasL
imit F
参数：e : K ≌ J；e.functor ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G

--- 原说明 ---
If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of
 `F`.
-/
theorem hasLimit_of_equivalence_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F := by
  have : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimit_equivalence_comp e.symm
  apply hasLimit_of_iso (e.invFunIdAssoc F)
/-
**CategoryTheory.Limits.hasLimit_equivalence_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_equivalence_comp_iff (e : K ≌ J) : HasLimit (e.functor ⋙ F) ↔ Has
Limit F
参数：e : K ≌ J。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_equivalence_comp`：hasLimit_of_equivale
nce_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F
-/
lemma hasLimit_equivalence_comp_iff (e : K ≌ J) : HasLimit (e.functor ⋙ F) ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_equivalence_comp e, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasLimit_inverse_equivalence_comp_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimit_inverse_equivalence_comp_iff (e : J ≌ K) : HasLimit (e.inverse ⋙ 
F) ↔ HasLimit F
参数：e : J ≌ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasLimit_equivalence_comp_iff`：hasLimit_equivalenc
e_comp_iff (e : K ≌ J) : HasLimit (e.functor ⋙ F) ↔ HasLimit F
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
/-
**CategoryTheory.Limits.lim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：lim : (J ⥤ C) ⥤ C where obj F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
`limit F` is functorial in `F`, when `C` has all limits of shape `J`.
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
/-
**CategoryTheory.Limits.lim.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation induced by `limit.π`.
-/
def lim.π (j : J) : lim ⟶ (evaluation J C).obj j where
  app F := limit.π F j

end

variable {G : J ⥤ C} (α : F ⟶ G)

/-
**CategoryTheory.Limits.limMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：limMap_eq : limMap α = lim.map α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem limMap_eq : limMap α = lim.map α := rfl
/-
**CategoryTheory.Limits.limit.map_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] {F : CategoryTheory.Functor J C}   [inst_3 : CategoryTh
eory.Limits.HasLimitsOfShape J C] {G : CategoryTheory.Functor J C} (α : F ⟶ G)  
 [inst_4 : CategoryTheory.Limits.HasLimitsOfShape K C] (E : CategoryTheory.Funct
or K J),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.lim.map α) 
(CategoryTheory.Limits.limit.pre G E) =     CategoryTheory.CategoryStruct.comp (
CategoryTheory.Limits.limit.pre F E)       (CategoryTheory.Limits.lim.map (E.whi
skerLeft α))
参数：α : F ⟶ G；E : CategoryTheory.Functor K J；CategoryTheory.Limits.lim.map α；Cate
goryTheory.Limits.limit.pre G E；CategoryTheory.Limits.limit.pre F E；CategoryTheo
ry.Limits.lim.map (E.whiskerLeft α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Limits.limit.pre_π_assoc`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} K]   {C : Type u} [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit.map_pre [HasLimitsOfShape K C] (E : K ⥤ J) :
    lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whiskerLeft E α) := by
  ext
  simp
/-
**CategoryTheory.Limits.limit.map_pre'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] [inst_3 : CategoryTheory.Limits.HasLimitsOfShape J C]  
 [inst_4 : CategoryTheory.Limits.HasLimitsOfShape K C] (F : CategoryTheory.Funct
or J C)   {E₁ E₂ : CategoryTheory.Functor K J} (α : E₁ ⟶ E₂),   CategoryTheory.L
imits.limit.pre F E₂ =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Li
mits.limit.pre F E₁)       (CategoryTheory.Limits.lim.map (CategoryTheory.Functo
r.whiskerRight α F))
参数：F : CategoryTheory.Functor J C；α : E₁ ⟶ E₂；CategoryTheory.Limits.limit.pre F 
E₁；CategoryTheory.Limits.lim.map (CategoryTheory.Functor.whiskerRight α F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Limits.limit.pre_π_assoc`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit.map_pre' [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whiskerRight α F) := by
  ext1; simp
/-
**CategoryTheory.Limits.limit.id_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryTheory.Limits.Has
LimitsOfShape J C] (F : CategoryTheory.Functor J C),   CategoryTheory.Limits.lim
it.pre F (CategoryTheory.Functor.id J) = CategoryTheory.Limits.lim.map F.leftUni
tor.inv
参数：F : CategoryTheory.Functor J C；CategoryTheory.Functor.id J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.pre_π`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit.id_pre (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv := by
  cat_disch
/-
**CategoryTheory.Limits.limit.map_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.limit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasLimitsOfShape J C]   {G : CategoryTheory.Functo
r J C} (α : F ⟶ G) {D : Type u'} [inst_3 : CategoryTheory.Category.{v', u'} D]  
 [inst_4 : CategoryTheory.Limits.HasLimitsOfShape J D] (H : CategoryTheory.Funct
or C D),   CategoryTheory.CategoryStruct.comp (H.map (CategoryTheory.Limits.limM
ap α)) (CategoryTheory.Limits.limit.post G H) =     CategoryTheory.CategoryStruc
t.comp (CategoryTheory.Limits.limit.post F H)       (CategoryTheory.Limits.limMa
p (CategoryTheory.Functor.whiskerRight α H))
参数：α : F ⟶ G；H : CategoryTheory.Functor C D；H.map (CategoryTheory.Limits.limMap 
α)；CategoryTheory.Limits.limit.post G H；CategoryTheory.Limits.limit.post F H；Cat
egoryTheory.Limits.limMap (CategoryTheory.Functor.whiskerRight α H)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.post_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {D : Type u'} [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Limits.limit.post_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {D : Type u'} [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit.map_post {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D) :
    /- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
     H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
    H.map (limMap α) ≫ limit.post G H = limit.post F H ≫ limMap (whiskerRight α H) := by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
/-
**CategoryTheory.Limits.limYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：limYoneda : lim ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅
 CategoryTheory.cones J C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def limYoneda :
    lim ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅ CategoryTheory.cones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => limit.homIso F (unop W)

/-- The constant functor and limit functor are adjoint to each other -/
/-
**CategoryTheory.Limits.constLimAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：constLimAdj : (const J : C ⥤ J ⥤ C) ⊣ lim
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The constant functor and limit functor are adjoint to each other
-/
def constLimAdj : (const J : C ⥤ J ⥤ C) ⊣ lim := Adjunction.mk' {
  homEquiv := fun c g ↦
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun _ => f ≫ limit.π _ _ }
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g => { app := limit.π _ } } }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨constLimAdj⟩⟩

end LimFunctor

/-
**CategoryTheory.Limits.limMap_mono'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : M
ono (limMap α)
参数：α : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instIsRightAdjointFunctorLim`：∀ {J : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   [inst_2 : CategoryThe…
-/
instance limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α
/-
**CategoryTheory.Limits.limMap_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [forall j,
 Mono (α.app j)] : Mono (limMap α)
参数：α : F ⟶ G；α.app j。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
instance limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [∀ j, Mono (α.app j)] :
    Mono (limMap α) :=
  ⟨fun {Z} u v h =>
    limit.hom_ext fun j => (cancel_mono (α.app j)).1 <| by simpa using h =≫ limit.π _ j⟩

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
/-
**CategoryTheory.Limits.coneOfAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：coneOfAdj (F : J ⥤ C) : Cone F where pt
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone obtained from a right adjoint of the constant functor.
-/
noncomputable def coneOfAdj (F : J ⥤ C) : Cone F where
  pt := L.obj F
  π := adj.counit.app F

set_option backward.defeqAttrib.useBackward true in
/-- The cones defined by `coneOfAdj` are limit cones. -/
@[simps]
/-
**CategoryTheory.Limits.isLimitConeOfAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isLimitConeOfAdj (F : J ⥤ C) : IsLimit (coneOfAdj adj F) where lift s
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cones defined by `coneOfAdj` are limit cones.
-/
def isLimitConeOfAdj (F : J ⥤ C) :
    IsLimit (coneOfAdj adj F) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (adj.left_triangle_components s.pt) j
    dsimp at eq eq' ⊢
    rw [adj.homEquiv_unit, assoc, eq, reassoc_of% eq']
  uniq s m hm := (adj.homEquiv _ _).symm.injective (by ext j; simpa using! hm j)

end Adjunction

/-- We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
/-
**CategoryTheory.Limits.hasLimitsOfShape_of_equivalence** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌
 J') [HasLimitsOfShape J C] : HasLimitsOfShape J' C
参数：e : J ≌ J'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_equivalence_comp`：hasLimit_of_equivale
nce_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasLimitsOfShape J C] : HasLimitsOfShape J' C := by
  constructor
  intro F
  apply hasLimit_of_equivalence_comp e

variable (C)
/-
**CategoryTheory.Limits.HasLimitsOfShape.of_small** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.HasLimitsOfShape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasLimitsOfSize.{v₁, u₁, v, u} C]   (J : Type u₂) [inst_2 : CategoryTheory
.Category.{v₂, u₂} J] [Small.{u₁, u₂} J]   [CategoryTheory.LocallySmall.{v₁, v₂,
 u₂} J], CategoryTheory.Limits.HasLimitsOfShape J C
参数：C : Type u；J : Type u₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Shrink.instLocallySmallShrink`：∀ (C : Type u) [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : Small.{w', u} C]   [CategoryTheory.Loca
llySmall.{w, v, u} C], CategoryThe…
· 使用定理 `CategoryTheory.Limits.HasLimitsOfSize.has_limits_of_shape`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasLim
itsOfSize.{v₁, u₁, v, u} C]   (J : Type u₁) [in…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
lemma HasLimitsOfShape.of_small
    [HasLimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [Small.{u₁} J] [LocallySmall.{v₁} J] :
    HasLimitsOfShape J C := by
  have := HasLimitsOfSize.has_limits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)
/-
**CategoryTheory.Limits.HasLimitsOfShape.of_essentiallySmall** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.HasLimitsOfShape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasLimitsOfSize.{v₁, u₁, v, u} C]   (J : Type u₂) [inst_2 : CategoryTheory
.Category.{v₂, u₂} J] [CategoryTheory.EssentiallySmall.{u₁, v₂, u₂} J]   [Catego
ryTheory.LocallySmall.{v₁, v₂, u₂} J], CategoryTheory.Limits.HasLimitsOfShape J 
C
参数：C : Type u；J : Type u₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimitsOfShape.of_small`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimitsOfSize.{v₁, u₁
, v, u} C]   (J : Type u₂) [inst_2 : …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instLocallySmallSmallModel`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.EssentiallySmall.{w, v, u} 
C]   [CategoryTheory.LocallySma…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
lemma HasLimitsOfShape.of_essentiallySmall
    [HasLimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [EssentiallySmall.{u₁} J] [LocallySmall.{v₁} J] :
    HasLimitsOfShape J C := by
  have := HasLimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasLimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

/-- A category that has larger limits also has smaller limits. -/
/-
**CategoryTheory.Limits.hasLimitsOfSizeOfUnivLE** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}] [HasLimitsOfSi
ze.{v₁, u₁} C] : HasLimitsOfSize.{v₂, u₂} C where has_limits_of_shape J {_}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A category that has larger limits also has smaller limits.
-/
theorem hasLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSize.{v₂, u₂} C where
  has_limits_of_shape J {_} := hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

/-- `hasLimitsOfSizeShrink.{v u} C` tries to obtain `HasLimitsOfSize.{v u} C`
from some other `HasLimitsOfSize C`.
-/
/-
**CategoryTheory.Limits.hasLimitsOfSizeShrink** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] : HasLimi
tsOfSize.{v₁, u₁} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfSizeOfUnivLE`：hasLimitsOfSizeOfUnivLE [
UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}] [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSiz
e.{v₂, u₂} C where has_limits_of_sh…

--- 原说明 ---
`hasLimitsOfSizeShrink.{v u} C` tries to obtain `HasLimitsOfSize.{v u} C`
from some other `HasLimitsOfSize C`.
-/
theorem hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasLimitsOfSize.{v₁, u₁} C := hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasSmallestLimitsOfHasLimits [HasLimits C] : HasLimitsOfSize.{0, 0} C :=
  hasLimitsOfSizeShrink.{0, 0} C

end Limit

section Colimit

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
/-
**CategoryTheory.Limits.colimit.homIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.colimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasColimit F] 
→             (W : C) → ULift.{u₁, v} (CategoryTheory.Limits.colimit F ⟶ W) ≅ F.
cocones.obj W
参数：F : CategoryTheory.Functor J C；W : C；CategoryTheory.Limits.colimit F ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.homIso (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅ F.cocones.obj W :=
  (colimit.isColimit F).homIso W

@[simp]
/-
**CategoryTheory.Limits.colimit.homIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor J C) [i
nst_2 : CategoryTheory.Limits.HasColimit F] {W : C},   (CategoryTheory.Limits.co
limit.homIso F W).hom =     TypeCat.ofHom fun f =>       CategoryTheory.Category
Struct.comp (CategoryTheory.Limits.colimit.cocone F).ι         ((CategoryTheory.
Functor.const J).map f.down)
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.colimit.homIso F W；Categ
oryTheory.Limits.colimit.cocone F；(CategoryTheory.Functor.const J).map f.down。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.homIso_hom`：homIso_hom (h : IsColimit t)
 {W : C} : (IsColimit.homIso h W).hom = ↾fun f => (t.extend f.down).ι
-/
theorem colimit.homIso_hom (F : J ⥤ C) [HasColimit F] {W : C} :
    (colimit.homIso F W).hom =
      ↾fun f ↦ (colimit.cocone F).ι ≫ (const J).map f.down :=
  (colimit.isColimit F).homIso_hom

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
/-
**CategoryTheory.Limits.colimit.homIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.colimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasColimit F] 
→             (W : C) →               ULift.{u₁, v} (CategoryTheory.Limits.colim
it F ⟶ W) ≅                 { p // ∀ {j j' : J} (f : j ⟶ j'), CategoryTheory.Cat
egoryStruct.comp (F.map f) (p j') = p j }
参数：F : CategoryTheory.Functor J C；W : C；CategoryTheory.Limits.colimit F ⟶ W；f : 
j ⟶ j'；F.map f；p j'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.homIso' (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅
      { p : ∀ j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  (colimit.isColimit F).homIso' W

-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
/-- If `F` has a colimit, so does any naturally isomorphic functor. -/
@[to_dual none]
/-
**CategoryTheory.Limits.hasColimit_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：hasColimit_of_iso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G
参数：α : G ≅ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` has a colimit, so does any naturally isomorphic functor.
-/
theorem hasColimit_of_iso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G :=
  HasColimit.mk
    { cocone := (Cocone.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
/-
**CategoryTheory.Limits.HasColimit.ofCoconesIso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.HasColimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {K : Type u₁} [inst_2 : CategoryThe
ory.Category.{v₂, u₁} K] (F : CategoryTheory.Functor J C)   (G : CategoryTheory.
Functor K C) (h : F.cocones ≅ G.cocones) [CategoryTheory.Limits.HasColimit F],  
 CategoryTheory.Limits.HasColimit G
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor K C；h : F.cocones ≅
 G.cocones。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit.
-/
theorem HasColimit.ofCoconesIso {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
    (h : F.cocones ≅ G.cocones) [HasColimit F] : HasColimit G :=
  HasColimit.mk ⟨_, IsColimit.ofCorepresentableBy ((colimit.isColimit F).corepresentableBy.ofIso h)⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasColimit.isoOfNatIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasColimit.isoOfNatIso_ι_hom {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι F j ≫ (HasColimit.isoOfNatIso w).hom = w.hom.app j ≫ colimit.ι G j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasColimit.isoOfNatIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasColimit.isoOfNatIso_ι_inv {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι G j ≫ (HasColimit.isoOfNatIso w).inv = w.inv.app j ≫ colimit.ι F j :=
  IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.HasColimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
[inst_2 : CategoryTheory.Limits.HasColimit F]   [inst_3 : CategoryTheory.Limits.
HasColimit G] (t : CategoryTheory.Limits.Cocone G) (w : F ≅ G),   CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.HasColimit.isoOfNatIso w).hom       
(CategoryTheory.Limits.colimit.desc G t) =     CategoryTheory.Limits.colimit.des
c F ((CategoryTheory.Limits.Cocone.precompose w.hom).obj t)
参数：t : CategoryTheory.Limits.Cocone G；w : F ≅ G；CategoryTheory.Limits.HasColimit
.isoOfNatIso w；CategoryTheory.Limits.colimit.desc G t；(CategoryTheory.Limits.Coc
one.precompose w.hom).obj t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointsIsoOfNatIso_hom_desc`：∀ {J :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : Ca
tegoryTheory.Category.{v₃, u₃} C]   {F G : CategoryThe…
-/
theorem HasColimit.isoOfNatIso_hom_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).hom ≫ colimit.desc G t =
      colimit.desc F ((Cocone.precompose w.hom).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasColimit.isoOfNatIso_inv_desc** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.HasColimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
[inst_2 : CategoryTheory.Limits.HasColimit F]   [inst_3 : CategoryTheory.Limits.
HasColimit G] (t : CategoryTheory.Limits.Cocone F) (w : F ≅ G),   CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.HasColimit.isoOfNatIso w).inv       
(CategoryTheory.Limits.colimit.desc F t) =     CategoryTheory.Limits.colimit.des
c G ((CategoryTheory.Limits.Cocone.precompose w.inv).obj t)
参数：t : CategoryTheory.Limits.Cocone F；w : F ≅ G；CategoryTheory.Limits.HasColimit
.isoOfNatIso w；CategoryTheory.Limits.colimit.desc F t；(CategoryTheory.Limits.Coc
one.precompose w.inv).obj t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointsIsoOfNatIso_inv_desc`：∀ {J :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : Ca
tegoryTheory.Category.{v₃, u₃} C]   {F G : CategoryThe…
-/
theorem HasColimit.isoOfNatIso_inv_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).inv ≫ colimit.desc F t =
      colimit.desc G ((Cocone.precompose w.inv).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _

/-- The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
/-
**CategoryTheory.Limits.HasColimit.isoOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.HasColimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u} →           [inst_2 : CategoryTheory.Category.{v, u} C] →             {F : 
CategoryTheory.Functor J C} →               [inst_3 : CategoryTheory.Limits.HasC
olimit F] →                 {G : CategoryTheory.Functor K C} →                  
 [inst_4 : CategoryTheory.Limits.HasColimit G] →                     (e : J ≌ K)
 →                       (e.functor.comp G ≅ F) → (CategoryTheory.Limits.colimit
 F ≅ CategoryTheory.Limits.colimit G)
参数：e : J ≌ K；e.functor.comp G ≅ F；CategoryTheory.Limits.colimit F ≅ CategoryTheo
ry.Limits.colimit G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural
 isomorphism.
-/
def HasColimit.isoOfEquivalence {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasColimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasColimit.ι_isoOfEquivalence_hom {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    colimit.ι F j ≫ (HasColimit.isoOfEquivalence e w).hom =
      F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ := by
  simp [HasColimit.isoOfEquivalence]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.HasColimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
/-
**CategoryTheory.Limits.colimit.pre** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.colimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {K : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} K] →         {C : Typ
e u} →           [inst_2 : CategoryTheory.Category.{v, u} C] →             (F : 
CategoryTheory.Functor J C) →               [inst_3 : CategoryTheory.Limits.HasC
olimit F] →                 (E : CategoryTheory.Functor K J) →                  
 [inst_4 : CategoryTheory.Limits.HasColimit (E.comp F)] →                     Ca
tegoryTheory.Limits.colimit (E.comp F) ⟶ CategoryTheory.Limits.colimit F
参数：F : CategoryTheory.Functor J C；E : CategoryTheory.Functor K J；E.comp F；E.comp
 F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) := by
  simp [colimit.pre]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.ι_inv_pre [IsIso (pre F E)] (k : K) :
    colimit.ι F (E.obj k) ≫ inv (colimit.pre F E) = colimit.ι (E ⋙ F) k := by
  simp [IsIso.comp_inv_eq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit.pre_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] (F : CategoryTheory.Functor J C)   [inst_3 : CategoryTh
eory.Limits.HasColimit F] (E : CategoryTheory.Functor K J)   [inst_4 : CategoryT
heory.Limits.HasColimit (E.comp F)] (c : CategoryTheory.Limits.Cocone F),   Cate
goryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.pre F E) (Category
Theory.Limits.colimit.desc F c) =     CategoryTheory.Limits.colimit.desc (E.comp
 F) (CategoryTheory.Limits.Cocone.whisker E c)
参数：F : CategoryTheory.Functor J C；E : CategoryTheory.Functor K J；E.comp F；c : Ca
tegoryTheory.Limits.Cocone F；CategoryTheory.Limits.colimit.pre F E；CategoryTheor
y.Limits.colimit.desc F c；E.comp F；CategoryTheory.Limits.Cocone.whisker E c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimit.pre_desc (c : Cocone F) :
    colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) := by
  ext
  simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[simp]
/-
**CategoryTheory.Limits.colimit.pre_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] (F : CategoryTheory.Functor J C)   [inst_3 : CategoryTh
eory.Limits.HasColimit F] (E : CategoryTheory.Functor K J)   [inst_4 : CategoryT
heory.Limits.HasColimit (E.comp F)] {L : Type u₃} [inst_5 : CategoryTheory.Categ
ory.{v₃, u₃} L]   (D : CategoryTheory.Functor L K) [h : CategoryTheory.Limits.Ha
sColimit (D.comp (E.comp F))],   CategoryTheory.CategoryStruct.comp (CategoryThe
ory.Limits.colimit.pre (E.comp F) D)       (CategoryTheory.Limits.colimit.pre F 
E) =     CategoryTheory.Limits.colimit.pre F (D.comp E)
参数：F : CategoryTheory.Functor J C；E : CategoryTheory.Functor K J；E.comp F；D : Ca
tegoryTheory.Functor L K；D.comp (E.comp F)；CategoryTheory.Limits.colimit.pre (E.
comp F) D；CategoryTheory.Limits.colimit.pre F E；D.comp E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
-/
theorem colimit.pre_pre [h : HasColimit (D ⋙ E ⋙ F)] :
    haveI : HasColimit ((D ⋙ E) ⋙ F) := h
    colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc, colimit.ι_pre, colimit.ι_pre]
  have : HasColimit ((D ⋙ E) ⋙ F) := h
  exact (colimit.ι_pre F (D ⋙ E) j).symm

variable {E F}

/--
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
/-
**CategoryTheory.Limits.colimit.pre_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] {F : CategoryTheory.Functor J C}   [inst_3 : CategoryTh
eory.Limits.HasColimit F] {E : CategoryTheory.Functor K J}   [inst_4 : CategoryT
heory.Limits.HasColimit (E.comp F)] (s : CategoryTheory.Limits.ColimitCocone (E.
comp F))   (t : CategoryTheory.Limits.ColimitCocone F),   CategoryTheory.Limits.
colimit.pre F E =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.
colimit.isoColimitCocone s).hom       (CategoryTheory.CategoryStruct.comp (s.isC
olimit.desc (CategoryTheory.Limits.Cocone.whisker E t.cocone))         (Category
Theory.Limits.colimit.isoColimitCocone t).inv)
参数：E.comp F；s : CategoryTheory.Limits.ColimitCocone (E.comp F)；t : CategoryTheor
y.Limits.ColimitCocone F；CategoryTheory.Limits.colimit.isoColimitCocone s；Catego
ryTheory.CategoryStruct.comp (s.isColimit.desc (CategoryTheory.Limits.Cocone.whi
sker E t.cocone))         (CategoryTheory.Limits.colimit.isoColimitCocone t).inv
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom_assoc`：∀ {J : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryT
heory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
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

/-- The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
/-
**CategoryTheory.Limits.colimit.post** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.colimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           {D : Type u'} →             [inst_2 : Category
Theory.Category.{v', u'} D] →               [inst_3 : CategoryTheory.Limits.HasC
olimit F] →                 (G : CategoryTheory.Functor C D) →                  
 [inst_4 : CategoryTheory.Limits.HasColimit (F.comp G)] →                     Ca
tegoryTheory.Limits.colimit (F.comp G) ⟶ G.obj (CategoryTheory.Limits.colimit F)
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor C D；F.comp G；F.comp
 G；CategoryTheory.Limits.colimit F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
  colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.ι_post (j : J) :
    colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) := by
  simp [colimit.post]

@[simp]
/-
**CategoryTheory.Limits.colimit.post_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor J C) {D
 : Type u'} [inst_2 : CategoryTheory.Category.{v', u'} D]   [inst_3 : CategoryTh
eory.Limits.HasColimit F] (G : CategoryTheory.Functor C D)   [inst_4 : CategoryT
heory.Limits.HasColimit (F.comp G)] (c : CategoryTheory.Limits.Cocone F),   Cate
goryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F G)       (G
.map (CategoryTheory.Limits.colimit.desc F c)) =     CategoryTheory.Limits.colim
it.desc (F.comp G) (G.mapCocone c)
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor C D；F.comp G；c : Ca
tegoryTheory.Limits.Cocone F；CategoryTheory.Limits.colimit.post F G；G.map (Categ
oryTheory.Limits.colimit.desc F c)；F.comp G；G.mapCocone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_post`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem colimit.post_desc (c : Cocone F) :
    colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.mapCocone c) := by
  ext
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_desc, colimit.ι_desc]
  rfl

@[simp]
/-
**CategoryTheory.Limits.colimit.post_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor J C) {D
 : Type u'} [inst_2 : CategoryTheory.Category.{v', u'} D]   [inst_3 : CategoryTh
eory.Limits.HasColimit F] (G : CategoryTheory.Functor C D)   [inst_4 : CategoryT
heory.Limits.HasColimit (F.comp G)] {E : Type u''} [inst_5 : CategoryTheory.Cate
gory.{v'', u''} E]   (H : CategoryTheory.Functor D E) [h : CategoryTheory.Limits
.HasColimit ((F.comp G).comp H)],   CategoryTheory.CategoryStruct.comp (Category
Theory.Limits.colimit.post (F.comp G) H)       (H.map (CategoryTheory.Limits.col
imit.post F G)) =     CategoryTheory.Limits.colimit.post F (G.comp H)
参数：F : CategoryTheory.Functor J C；G : CategoryTheory.Functor C D；F.comp G；H : Ca
tegoryTheory.Functor D E；(F.comp G).comp H；CategoryTheory.Limits.colimit.post (F
.comp G) H；H.map (CategoryTheory.Limits.colimit.post F G)；G.comp H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_post`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem colimit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E)
    -- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals
    -- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H))
    [h : HasColimit ((F ⋙ G) ⋙ H)] : haveI : HasColimit (F ⋙ G ⋙ H) := h
    colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_post]
  have : HasColimit (F ⋙ G ⋙ H) := h
  exact (colimit.ι_post F (G ⋙ H) j).symm

end Post

/-
**CategoryTheory.Limits.colimit.pre_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] {D : Type u'} [inst_3 : CategoryTheory.Category.{v', u'
} D]   (E : CategoryTheory.Functor K J) (F : CategoryTheory.Functor J C) (G : Ca
tegoryTheory.Functor C D)   [inst_4 : CategoryTheory.Limits.HasColimit F] [inst_
5 : CategoryTheory.Limits.HasColimit (E.comp F)]   [inst_6 : CategoryTheory.Limi
ts.HasColimit (F.comp G)] [h : CategoryTheory.Limits.HasColimit ((E.comp F).comp
 G)],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post (
E.comp F) G)       (G.map (CategoryTheory.Limits.colimit.pre F E)) =     Categor
yTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.pre (F.comp G) E)    
   (CategoryTheory.Limits.colimit.post F G)
参数：E : CategoryTheory.Functor K J；F : CategoryTheory.Functor J C；G : CategoryThe
ory.Functor C D；E.comp F；F.comp G；(E.comp F).comp G；CategoryTheory.Limits.colimi
t.post (E.comp F) G；G.map (CategoryTheory.Limits.colimit.pre F E)；CategoryTheory
.Limits.colimit.pre (F.comp G) E；CategoryTheory.Limits.colimit.post F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_post`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
-/
theorem colimit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasColimit F] [HasColimit (E ⋙ F)] [HasColimit (F ⋙ G)] [h : HasColimit ((E ⋙ F) ⋙ G)] :
    -- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs
    -- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or
    haveI : HasColimit (E ⋙ F ⋙ G) := h
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
      colimit.pre (F ⋙ G) E ≫ colimit.post F G := by
  ext j
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_pre, ← assoc]
  have : HasColimit (E ⋙ F ⋙ G) := h
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]

open CategoryTheory.Equivalence
/-
**CategoryTheory.Limits.hasColimit_equivalence_comp** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimit_equivalence_comp (e : K ≌ J) [HasColimit F] : HasColimit (e.fun
ctor ⋙ F)
参数：e : K ≌ J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_equivalence_comp (e : K ≌ J) [HasColimit F] : HasColimit (e.functor ⋙ F) :=
  HasColimit.mk
    { cocone := Cocone.whisker e.functor (colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }

/-- If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
/-
**CategoryTheory.Limits.hasColimit_of_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasColimit_of_equivalence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : 
HasColimit F
参数：e : K ≌ J；e.functor ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G

--- 原说明 ---
If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimi
t of `F`.
-/
theorem hasColimit_of_equivalence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F := by
  have : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimit_equivalence_comp e.symm
  apply hasColimit_of_iso (e.invFunIdAssoc F).symm
/-
**CategoryTheory.Limits.hasColimit_equivalence_comp_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_equivalence_comp_iff (e : K ≌ J) : HasColimit (e.functor ⋙ F) ↔
 HasColimit F
参数：e : K ≌ J。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_equivalence_comp`：hasColimit_of_equi
valence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F
-/
lemma hasColimit_equivalence_comp_iff (e : K ≌ J) : HasColimit (e.functor ⋙ F) ↔ HasColimit F :=
  ⟨fun _ ↦ hasColimit_of_equivalence_comp e, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasColimit_inverse_equivalence_comp_iff** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_inverse_equivalence_comp_iff (e : J ≌ K) : HasColimit (e.invers
e ⋙ F) ↔ HasColimit F
参数：e : J ≌ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasColimit_equivalence_comp_iff`：hasColimit_equiva
lence_comp_iff (e : K ≌ J) : HasColimit (e.functor ⋙ F) ↔ HasColimit F
-/
lemma hasColimit_inverse_equivalence_comp_iff (e : J ≌ K) :
    HasColimit (e.inverse ⋙ F) ↔ HasColimit F :=
  hasColimit_equivalence_comp_iff e.symm

section ColimFunctor

variable [HasColimitsOfShape J C]

section

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Limits.colim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colim : (J ⥤ C) ⥤ C where obj F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
`colimit F` is functorial in `F`, when `C` has all colimits of shape `J`.
-/
def colim : (J ⥤ C) ⥤ C where
  obj F := colimit F
  map α := colimMap α

/-- The natural transformation induced by `colimit.ι`. -/
@[simps]
/-
**CategoryTheory.Limits.colim.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation induced by `colimit.ι`.
-/
def colim.ι (j : J) : (evaluation J C).obj j ⟶ colim where
  app F := colimit.ι F j

end

variable {G : J ⥤ C} (α : F ⟶ G)

/-
**CategoryTheory.Limits.colimMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：colimMap_eq : colimMap α = colim.map α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem colimMap_eq : colimMap α = colim.map α := rfl

@[reassoc]
/-
**CategoryTheory.Limits.colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j := by simp
/-
**CategoryTheory.Limits.colimit.pre_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] {F : CategoryTheory.Functor J C}   [inst_3 : CategoryTh
eory.Limits.HasColimitsOfShape J C] {G : CategoryTheory.Functor J C} (α : F ⟶ G)
   [inst_4 : CategoryTheory.Limits.HasColimitsOfShape K C] (E : CategoryTheory.F
unctor K J),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit
.pre F E) (CategoryTheory.Limits.colim.map α) =     CategoryTheory.CategoryStruc
t.comp (CategoryTheory.Limits.colim.map (E.whiskerLeft α))       (CategoryTheory
.Limits.colimit.pre G E)
参数：α : F ⟶ G；E : CategoryTheory.Functor K J；CategoryTheory.Limits.colimit.pre F 
E；CategoryTheory.Limits.colim.map α；CategoryTheory.Limits.colim.map (E.whiskerLe
ft α)；CategoryTheory.Limits.colimit.pre G E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.colimit.ι_map`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem colimit.pre_map [HasColimitsOfShape K C] (E : K ⥤ J) :
    colimit.pre F E ≫ colim.map α = colim.map (whiskerLeft E α) ≫ colimit.pre G E := by
  ext
  rw [← assoc, colimit.ι_pre, colimit.ι_map, ← assoc, colimit.ι_map, assoc, colimit.ι_pre]
  rfl
/-
**CategoryTheory.Limits.colimit.pre_map'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   {C : Type u} [inst_2 : CategoryT
heory.Category.{v, u} C] [inst_3 : CategoryTheory.Limits.HasColimitsOfShape J C]
   [inst_4 : CategoryTheory.Limits.HasColimitsOfShape K C] (F : CategoryTheory.F
unctor J C)   {E₁ E₂ : CategoryTheory.Functor K J} (α : E₁ ⟶ E₂),   CategoryTheo
ry.Limits.colimit.pre F E₁ =     CategoryTheory.CategoryStruct.comp (CategoryThe
ory.Limits.colim.map (CategoryTheory.Functor.whiskerRight α F))       (CategoryT
heory.Limits.colimit.pre F E₂)
参数：F : CategoryTheory.Functor J C；α : E₁ ⟶ E₂；CategoryTheory.Limits.colim.map (C
ategoryTheory.Functor.whiskerRight α F)；CategoryTheory.Limits.colimit.pre F E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimit.pre_map' [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    colimit.pre F E₁ = colim.map (whiskerRight α F) ≫ colimit.pre F E₂ := by
  ext1
  simp
/-
**CategoryTheory.Limits.colimit.pre_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryTheory.Limits.Has
ColimitsOfShape J C] (F : CategoryTheory.Functor J C),   CategoryTheory.Limits.c
olimit.pre F (CategoryTheory.Functor.id J) = CategoryTheory.Limits.colim.map F.l
eftUnitor.hom
参数：F : CategoryTheory.Functor J C；CategoryTheory.Functor.id J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimit.pre_id (F : J ⥤ C) :
    colimit.pre F (𝟭 _) = colim.map (Functor.leftUnitor F).hom := by cat_disch
/-
**CategoryTheory.Limits.colimit.map_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.colimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} [i
nst_2 : CategoryTheory.Limits.HasColimitsOfShape J C]   {G : CategoryTheory.Func
tor J C} (α : F ⟶ G) {D : Type u'} [inst_3 : CategoryTheory.Category.{v', u'} D]
   [inst_4 : CategoryTheory.Limits.HasColimitsOfShape J D] (H : CategoryTheory.F
unctor C D),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit
.post F H)       (H.map (CategoryTheory.Limits.colim.map α)) =     CategoryTheor
y.CategoryStruct.comp (CategoryTheory.Limits.colim.map (CategoryTheory.Functor.w
hiskerRight α H))       (CategoryTheory.Limits.colimit.post G H)
参数：α : F ⟶ G；H : CategoryTheory.Functor C D；CategoryTheory.Limits.colimit.post F
 H；H.map (CategoryTheory.Limits.colim.map α)；CategoryTheory.Limits.colim.map (Ca
tegoryTheory.Functor.whiskerRight α H)；CategoryTheory.Limits.colimit.post G H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_post`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_map`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem colimit.map_post {D : Type u'} [Category.{v'} D] [HasColimitsOfShape J D]
    (H : C ⥤ D) :
    /- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
      H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
    colimit.post F H ≫ H.map (colim.map α) =
      colim.map (whiskerRight α H) ≫ colimit.post G H := by
  ext
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_map, H.map_comp]
  rw [← assoc, colimit.ι_map, assoc, colimit.ι_post]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
/-
**CategoryTheory.Limits.colimCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：colimCoyoneda : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFun
ctor.{u₁} ≅ CategoryTheory.cocones J C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colimCoyoneda : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
    ≅ CategoryTheory.cocones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => colimit.homIso (unop F) W

/-- The colimit functor and constant functor are adjoint to each other
-/
/-
**CategoryTheory.Limits.colimConstAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ const J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The colimit functor and constant functor are adjoint to each other
-/
def colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ const J := Adjunction.mk' {
  homEquiv := fun f c ↦
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fun _ => colimit.desc _ ⟨_, 𝟙 _⟩ } }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨colimConstAdj⟩⟩

end ColimFunctor

/-
**CategoryTheory.Limits.colimMap_epi'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
 Epi (colimMap α)
参数：α : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instIsLeftAdjointFunctorColim`：∀ {J : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.C
ategory.{v, u} C]   [inst_2 : CategoryThe…
-/
instance colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α
/-
**CategoryTheory.Limits.colimMap_epi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：colimMap_epi {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [fora
ll j, Epi (α.app j)] : Epi (colimMap α)
参数：α : F ⟶ G；α.app j。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
-/
instance colimMap_epi {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [∀ j, Epi (α.app j)] :
    Epi (colimMap α) :=
  ⟨fun {Z} u v h =>
    colimit.hom_ext fun j => (cancel_epi (α.app j)).1 <| by simpa using colimit.ι _ j ≫= h⟩

/-- We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_equivalence** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J
 ≌ J') [HasColimitsOfShape J C] : HasColimitsOfShape J' C
参数：e : J ≌ J'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_equivalence_comp`：hasColimit_of_equi
valence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasColimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasColimitsOfShape J C] : HasColimitsOfShape J' C := by
  constructor
  intro F
  apply hasColimit_of_equivalence_comp e

variable (C)
/-
**CategoryTheory.Limits.HasColimitsOfShape.of_small** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.HasColimitsOfShape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasColimitsOfSize.{v₁, u₁, v, u} C]   (J : Type u₂) [inst_2 : CategoryTheo
ry.Category.{v₂, u₂} J] [Small.{u₁, u₂} J]   [CategoryTheory.LocallySmall.{v₁, v
₂, u₂} J], CategoryTheory.Limits.HasColimitsOfShape J C
参数：C : Type u；J : Type u₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Shrink.instLocallySmallShrink`：∀ (C : Type u) [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : Small.{w', u} C]   [CategoryTheory.Loca
llySmall.{w, v, u} C], CategoryThe…
· 使用定理 `CategoryTheory.Limits.HasColimitsOfSize.has_colimits_of_shape`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C}   [self : CategoryTheory.Limits.
HasColimitsOfSize.{v₁, u₁, v, u} C] (J : Type u₁)  …
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
-/
lemma HasColimitsOfShape.of_small
    [HasColimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [Small.{u₁} J] [LocallySmall.{v₁} J] :
    HasColimitsOfShape J C := by
  have := HasColimitsOfSize.has_colimits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)
/-
**CategoryTheory.Limits.HasColimitsOfShape.of_essentiallySmall** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.HasColimitsOfShape`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasColimitsOfSize.{v₁, u₁, v, u} C]   (J : Type u₂) [inst_2 : CategoryTheo
ry.Category.{v₂, u₂} J] [CategoryTheory.EssentiallySmall.{u₁, v₂, u₂} J]   [Cate
goryTheory.LocallySmall.{v₁, v₂, u₂} J], CategoryTheory.Limits.HasColimitsOfShap
e J C
参数：C : Type u；J : Type u₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimitsOfShape.of_small`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimitsOfSize.{v₁
, u₁, v, u} C]   (J : Type u₂) [inst_2 …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instLocallySmallSmallModel`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.EssentiallySmall.{w, v, u} 
C]   [CategoryTheory.LocallySma…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
-/
lemma HasColimitsOfShape.of_essentiallySmall
    [HasColimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [EssentiallySmall.{u₁} J] [LocallySmall.{v₁} J] :
    HasColimitsOfShape J C := by
  have := HasColimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasColimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

/-- A category that has larger colimits also has smaller colimits. -/
/-
**CategoryTheory.Limits.hasColimitsOfSizeOfUnivLE** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasColimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}] [HasColimits
OfSize.{v₁, u₁} C] : HasColimitsOfSize.{v₂, u₂} C where has_colimits_of_shape J 
{_}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A category that has larger colimits also has smaller colimits.
-/
theorem hasColimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfSize.{v₂, u₂} C where
  has_colimits_of_shape J {_} := hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

/-- `hasColimitsOfSizeShrink.{v u} C` tries to obtain `HasColimitsOfSize.{v u} C`
from some other `HasColimitsOfSize C`.
-/
/-
**CategoryTheory.Limits.hasColimitsOfSizeShrink** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasColimitsOfSizeShrink [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] : Has
ColimitsOfSize.{v₁, u₁} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfSizeOfUnivLE`：hasColimitsOfSizeOfUniv
LE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}] [HasColimitsOfSize.{v₁, u₁} C] : HasColim
itsOfSize.{v₂, u₂} C where has_colimi…

--- 原说明 ---
`hasColimitsOfSizeShrink.{v u} C` tries to obtain `HasColimitsOfSize.{v u} C`
from some other `HasColimitsOfSize C`.
-/
theorem hasColimitsOfSizeShrink [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasColimitsOfSize.{v₁, u₁} C := hasColimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasSmallestColimitsOfHasColimits [HasColimits C] :
    HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink.{0, 0} C

end Colimit

section Opposite

set_option backward.defeqAttrib.useBackward true in
/-- If `t : Cone F` is a limit cone, then `t.op : Cocone F.op` is a colimit cocone.
-/
/-
**CategoryTheory.Limits.IsLimit.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.IsLimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           {t : CategoryTheory.Limits.Cone F} → CategoryT
heory.Limits.IsLimit t → CategoryTheory.Limits.IsColimit t.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : Cone F` is a limit cone, then `t.op : Cocone F.op` is a colimit cocone.
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
/-- If `t : Cocone F` is a colimit cocone, then `t.op : Cone F.op` is a limit cone.
-/
/-
**CategoryTheory.Limits.IsColimit.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsColimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           {t : CategoryTheory.Limits.Cocone F} → Categor
yTheory.Limits.IsColimit t → CategoryTheory.Limits.IsLimit t.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : Cocone F` is a colimit cocone, then `t.op : Cone F.op` is a limit cone.
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
/-- If `t : Cone F.op` is a limit cone, then `t.unop : Cocone F` is a colimit cocone.
-/
/-
**CategoryTheory.Limits.IsLimit.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsLimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           {t : CategoryTheory.Limits.Cone F.op} →       
      CategoryTheory.Limits.IsLimit t → CategoryTheory.Limits.IsColimit t.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : Cone F.op` is a limit cone, then `t.unop : Cocone F` is a colimit cocone
.
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
/-- If `t : Cocone F.op` is a colimit cocone, then `t.unop : Cone F` is a limit cone.
-/
/-
**CategoryTheory.Limits.IsColimit.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsColimit`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           {t : CategoryTheory.Limits.Cocone F.op} →     
        CategoryTheory.Limits.IsColimit t → CategoryTheory.Limits.IsLimit t.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t : Cocone F.op` is a colimit cocone, then `t.unop : Cone F` is a limit cone
.
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

/-- If `t.op : Cocone F.op` is a colimit cocone, then `t : Cone F` is a limit cone. -/
/-
**CategoryTheory.Limits.isLimitOfOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：isLimitOfOp {t : Cone F} (P : IsColimit t.op) : IsLimit t
参数：P : IsColimit t.op。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t.op : Cocone F.op` is a colimit cocone, then `t : Cone F` is a limit cone.
-/
def isLimitOfOp {t : Cone F} (P : IsColimit t.op) : IsLimit t :=
  P.unop

/-- If `t.op : Cone F.op` is a limit cone, then `t : Cocone F` is a colimit cocone. -/
/-
**CategoryTheory.Limits.isColimitOfOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：isColimitOfOp {t : Cocone F} (P : IsLimit t.op) : IsColimit t
参数：P : IsLimit t.op。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t.op : Cone F.op` is a limit cone, then `t : Cocone F` is a colimit cocone.
-/
def isColimitOfOp {t : Cocone F} (P : IsLimit t.op) : IsColimit t :=
  P.unop

/-- If `t.unop : Cocone F` is a colimit cocone, then `t : Cone F.op` is a limit cone. -/
/-
**CategoryTheory.Limits.isLimitOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：isLimitOfUnop {t : Cone F.op} (P : IsColimit t.unop) : IsLimit t
参数：P : IsColimit t.unop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t.unop : Cocone F` is a colimit cocone, then `t : Cone F.op` is a limit cone
.
-/
def isLimitOfUnop {t : Cone F.op} (P : IsColimit t.unop) : IsLimit t :=
  P.op

/-- If `t.unop : Cone F` is a limit cone, then `t : Cocone F.op` is a colimit cocone. -/
/-
**CategoryTheory.Limits.isColimitOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：isColimitOfUnop {t : Cocone F.op} (P : IsLimit t.unop) : IsColimit t
参数：P : IsLimit t.unop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t.unop : Cone F` is a limit cone, then `t : Cocone F.op` is a colimit cocone
.
-/
def isColimitOfUnop {t : Cocone F.op} (P : IsLimit t.unop) : IsColimit t :=
  P.op

/-- `t : Cone F` is a limit cone if and only if `t.op : Cocone F.op` is a colimit cocone.
-/
/-
**CategoryTheory.Limits.isLimitEquivIsColimitOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`t : Cone F` is a limit cone if and only if `t.op : Cocone F.op` is a colimit co
cone.
-/
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

/-- `t : Cocone F` is a colimit cocone if and only if `t.op : Cone F.op` is a limit cone.
-/
/-
**CategoryTheory.Limits.isColimitEquivIsLimitOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isColimitEquivIsLimitOp {t : Cocone F} : IsColimit t ≃ IsLimit t.op
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.subsingleton`：∀ {J : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Categor
y.{v₃, u₃} C]   {F : CategoryTheor…

--- 原说明 ---
`t : Cocone F` is a colimit cocone if and only if `t.op : Cone F.op` is a limit 
cone.
-/
def isColimitEquivIsLimitOp {t : Cocone F} : IsColimit t ≃ IsLimit t.op :=
  equivOfSubsingletonOfSubsingleton IsColimit.op isColimitOfOp

end Opposite

end Limits

end CategoryTheory

