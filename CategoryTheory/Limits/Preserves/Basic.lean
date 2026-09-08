/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C ⥤ D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/

@[expose] public section


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category theory universes].
universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- A functor `F` preserves limits of `K` (written as `PreservesLimit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
/-
**CategoryTheory.Limits.PreservesLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] → CategoryTheory.F
unctor J C → CategoryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves limits of `K` (written as `PreservesLimit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cone K} (hc : IsLimit c) : Nonempty (IsLimit (F.mapCone c))

/-- A functor `F` preserves colimits of `K` (written as `PreservesColimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
/-
**CategoryTheory.Limits.PreservesColimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] → CategoryTheory.F
unctor J C → CategoryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves colimits of `K` (written as `PreservesColimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cocone K} (hc : IsColimit c) : Nonempty (IsColimit (F.mapCocone c))

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
`K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
/-
**CategoryTheory.Limits.PreservesLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop w
here preservesLimit : forall {K : J ⥤ C}, PreservesLimit K F
参数：J : Type w；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `F` preserves limits of shape `J` if `F` preserves limits for every 
diagram
`K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones.
-/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by infer_instance

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
`K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
/-
**CategoryTheory.Limits.PreservesColimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop
 where preservesColimit : forall {K : J ⥤ C}, PreservesColimit K F
参数：J : Type w；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `F` preserves colimits of shape `J` if `F` preserves colimits for ev
ery diagram
`K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones.
-/
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `PreservesLimitsOfSize.{v u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[Category.{v} J]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `w, w'` in
-- `PreservesLimitsOfSize`, `PreservesColimitsOfSize`, `ReflectsLimitsOfSize`, and
-- `ReflectsColimitsOfSize` would default to universe output parameters.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.PreservesLimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory.Limits`。
形式化陈述：PreservesLimitsOfSize (F : C ⥤ D) : Prop where preservesLimitsOfShape : fo
rall {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class PreservesLimitsOfSize (F : C ⥤ D) : Prop where
  preservesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F := by
    infer_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
/-
**CategoryTheory.Limits.PreservesLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：PreservesLimits (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones.
-/
abbrev PreservesLimits (F : C ⥤ D) :=
  PreservesLimitsOfSize.{v₂, v₂} F

-- This should be used with explicit universe variables.
/-- `PreservesColimitsOfSize.{v u} F` means that `F` sends all colimit cocones over any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[Category.{v} J]`. -/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.PreservesColimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：PreservesColimitsOfSize (F : C ⥤ D) : Prop where preservesColimitsOfShape 
: forall {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PreservesColimitsOfSize.{v u} F` means that `F` sends all colimit cocones over 
any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[Category.{v} J]`.
-/
class PreservesColimitsOfSize (F : C ⥤ D) : Prop where
  preservesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F := by
    infer_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
/-
**CategoryTheory.Limits.PreservesColimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：PreservesColimits (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones.
-/
abbrev PreservesColimits (F : C ⥤ D) :=
  PreservesColimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance 100]
  PreservesLimitsOfShape.preservesLimit PreservesLimitsOfSize.preservesLimitsOfShape
  PreservesColimitsOfShape.preservesColimit
  PreservesColimitsOfSize.preservesColimitsOfShape

-- see Note [lower instance priority]
/-- A convenience function for `PreservesLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
/-
**CategoryTheory.Limits.isLimitOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimi
t K F] : IsLimit (F.mapCone c)
参数：F : C ⥤ D；t : IsLimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimit.preserves`：∀ {C : Type u₁} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A convenience function for `PreservesLimit`, which takes the functor as an expli
cit argument to
guide typeclass resolution.
-/
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] :
    IsLimit (F.mapCone c) :=
  (PreservesLimit.preserves t).some

/--
A convenience function for `PreservesColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
/-
**CategoryTheory.Limits.isColimitOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [Preserv
esColimit K F] : IsColimit (F.mapCocone c)
参数：F : C ⥤ D；t : IsColimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimit.preserves`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A convenience function for `PreservesColimit`, which takes the functor as an exp
licit argument to
guide typeclass resolution.
-/
def isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F] :
    IsColimit (F.mapCocone c) :=
  (PreservesColimit.preserves t).some
/-
**CategoryTheory.Limits.preservesLimit_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (Preser
vesLimit K F)
参数：K : J ⥤ C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.preservesColimit_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (Pres
ervesColimit K F)
参数：K : J ⥤ C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.preservesLimitsOfShape_subsingleton** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C 
⥤ D) : Subsingleton (PreservesLimitsOfShape J F)
参数：J : Type w；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.preservesColimitsOfShape_subsingleton** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : 
C ⥤ D) : Subsingleton (PreservesColimitsOfShape J F)
参数：J : Type w；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.preservesLimitsOfSize_subsingleton** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_subsingleton (F : C ⥤ D) : Subsingleton (PreservesLi
mitsOfSize.{w', w} F)
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesLimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.preservesColimitsOfSize_subsingleton** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_subsingleton (F : C ⥤ D) : Subsingleton (Preserves
ColimitsOfSize.{w', w} F)
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesColimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.id_preservesLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：id_preservesLimitsOfSize : PreservesLimitsOfSize.{w', w} (𝟭 C) where prese
rvesLimitsOfShape {J} 𝒥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
-/
instance id_preservesLimitsOfSize : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }
/-
**CategoryTheory.Limits.id_preservesColimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：id_preservesColimitsOfSize : PreservesColimitsOfSize.{w', w} (𝟭 C) where p
reservesColimitsOfShape {J} 𝒥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
-/
instance id_preservesColimitsOfSize : PreservesColimitsOfSize.{w', w} (𝟭 C) where
  preservesColimitsOfShape {J} 𝒥 :=
    {
      preservesColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimit K] {F : C ⥤ D} [PreservesLimit K F] : HasLimit (K ⋙ F) where
  exists_limit := ⟨_, isLimitOfPreserves F (limit.isLimit K)⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimit K] {F : C ⥤ D} [PreservesColimit K F] : HasColimit (K ⋙ F) where
  exists_colimit := ⟨_, isColimitOfPreserves F (colimit.isColimit K)⟩

/-- To show that `F` preserves the limit of `K`, we may assume that `K` has a limit. -/
/-
**CategoryTheory.Limits.PreservesLimit.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.PreservesLimit`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {K : CategoryTheory.Functor J C}   {F : CategoryTheory
.Functor C D},   (CategoryTheory.Limits.HasLimit K → CategoryTheory.Limits.Prese
rvesLimit K F) →     CategoryTheory.Limits.PreservesLimit K F
参数：CategoryTheory.Limits.HasLimit K → CategoryTheory.Limits.PreservesLimit K F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimit.preserves`：∀ {C : Type u₁} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
To show that `F` preserves the limit of `K`, we may assume that `K` has a limit.
-/
lemma PreservesLimit.mk' {F : C ⥤ D} (h : HasLimit K → PreservesLimit K F) :
    PreservesLimit K F where
  preserves hc := (h ⟨_, hc⟩).preserves hc

/-- To show that `F` preserves the colimit of `K`, we may assume that `K` has a colimit. -/
/-
**CategoryTheory.Limits.PreservesColimit.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.PreservesColimit`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {K : CategoryTheory.Functor J C}   {F : CategoryTheory
.Functor C D},   (CategoryTheory.Limits.HasColimit K → CategoryTheory.Limits.Pre
servesColimit K F) →     CategoryTheory.Limits.PreservesColimit K F
参数：CategoryTheory.Limits.HasColimit K → CategoryTheory.Limits.PreservesColimit K
 F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimit.preserves`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
To show that `F` preserves the colimit of `K`, we may assume that `K` has a coli
mit.
-/
lemma PreservesColimit.mk' {F : C ⥤ D} (h : HasColimit K → PreservesColimit K F) :
    PreservesColimit K F where
  preserves hc := (h ⟨_, hc⟩).preserves hc

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

/-
**CategoryTheory.Limits.comp_preservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：comp_preservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] : Pres
ervesLimit K (F ⋙ G) where preserves hc
参数：K ⋙ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp_preservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) where
  preserves hc := ⟨isLimitOfPreserves G (isLimitOfPreserves F hc)⟩
/-
**CategoryTheory.Limits.comp_preservesLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {E : Type u₃} [ℰ : CategoryTheory.Category.{v₃, u₃} E]
   (F : CategoryTheory.Functor C D) (G : CategoryTheory.Functor D E) [CategoryTh
eory.Limits.PreservesLimitsOfShape J F]   [CategoryTheory.Limits.PreservesLimits
OfShape J G], CategoryTheory.Limits.PreservesLimitsOfShape J (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance comp_preservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) where
/-
**CategoryTheory.Limits.comp_preservesLimits** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ℰ : CategoryTheor
y.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheory.Fu
nctor D E) [CategoryTheory.Limits.PreservesLimitsOfSize.{w', w, v₁, v₂, u₁, u₂} 
F]   [CategoryTheory.Limits.PreservesLimitsOfSize.{w', w, v₂, v₃, u₂, u₃} G],   
CategoryTheory.Limits.PreservesLimitsOfSize.{w', w, v₁, v₃, u₁, u₃} (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance comp_preservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) where
/-
**CategoryTheory.Limits.comp_preservesColimit** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：comp_preservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] 
: PreservesColimit K (F ⋙ G) where preserves hc
参数：K ⋙ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp_preservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] :
    PreservesColimit K (F ⋙ G) where
  preserves hc := ⟨isColimitOfPreserves G (isColimitOfPreserves F hc)⟩
/-
**CategoryTheory.Limits.comp_preservesColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {E : Type u₃} [ℰ : CategoryTheory.Category.{v₃, u₃} E]
   (F : CategoryTheory.Functor C D) (G : CategoryTheory.Functor D E) [CategoryTh
eory.Limits.PreservesColimitsOfShape J F]   [CategoryTheory.Limits.PreservesColi
mitsOfShape J G], CategoryTheory.Limits.PreservesColimitsOfShape J (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance comp_preservesColimitsOfShape [PreservesColimitsOfShape J F]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J (F ⋙ G) where
/-
**CategoryTheory.Limits.comp_preservesColimits** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ℰ : CategoryTheor
y.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheory.Fu
nctor D E) [CategoryTheory.Limits.PreservesColimitsOfSize.{w', w, v₁, v₂, u₁, u₂
} F]   [CategoryTheory.Limits.PreservesColimitsOfSize.{w', w, v₂, v₃, u₂, u₃} G]
,   CategoryTheory.Limits.PreservesColimitsOfSize.{w', w, v₁, v₃, u₁, u₃} (F.com
p G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance comp_preservesColimits [PreservesColimitsOfSize.{w', w} F]
    [PreservesColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} (F ⋙ G) where

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
/-
**CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLim
it t) (hF : IsLimit (F.mapCone t)) : PreservesLimit K F where preserves h'
参数：h : IsLimit t；hF : IsLimit (F.mapCone t)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K.
-/
lemma preservesLimit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F where
  preserves h' := ⟨IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩
/-
**CategoryTheory.Limits.preservesLimit_iff_isLimit_mapCone** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimit_iff_isLimit_mapCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t
) : PreservesLimit K F ↔ Nonempty (IsLimit (F.mapCone t))
参数：h : IsLimit t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
-/
lemma preservesLimit_iff_isLimit_mapCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) :
    PreservesLimit K F ↔ Nonempty (IsLimit (F.mapCone t)) :=
  ⟨fun _ ↦ ⟨isLimitOfPreserves _ h⟩, fun h' ↦ preservesLimit_of_preserves_limit_cone h h'.some⟩

set_option backward.defeqAttrib.useBackward true in
/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
/-
**CategoryTheory.Limits.preservesLimit_of_iso_diagram** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [P
reservesLimit K₁ F] : PreservesLimit K₂ F where preserves {c} t
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer preservation of limits along a natural isomorphism in the diagram.
-/
lemma preservesLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesLimit K₁ F] : PreservesLimit K₂ F where
  preserves {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cone.ext (Iso.refl _)⟩
/-
**CategoryTheory.Limits.preservesLimit_iff_of_iso_diagram** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂
) : PreservesLimit K₁ F ↔ PreservesLimit K₂ F
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
-/
lemma preservesLimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) :
    PreservesLimit K₁ F ↔ PreservesLimit K₂ F :=
  ⟨fun _ ↦ preservesLimit_of_iso_diagram _ h, fun _ ↦ preservesLimit_of_iso_diagram _ h.symm⟩

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesLimit_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesL
imit K F] : PreservesLimit K G where preserves t
参数：K : J ⥤ C；h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer preservation of a limit along a natural isomorphism in the functor.
-/
lemma preservesLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G where
  preserves t := ⟨IsLimit.mapConeEquiv h (isLimitOfPreserves F t)⟩
/-
**CategoryTheory.Limits.preservesLimit_iff_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesLimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) : Prese
rvesLimit K F ↔ PreservesLimit K G
参数：K : J ⥤ C；h : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_natIso`：preservesLimit_of_natIso
 (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G
 where preserves t
-/
lemma preservesLimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimit K F ↔ PreservesLimit K G :=
  ⟨fun _ ↦ preservesLimit_of_natIso _ h, fun _ ↦ preservesLimit_of_natIso _ h.symm⟩

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_natIso** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit
sOfShape J F] : PreservesLimitsOfShape J G where preservesLimit {K}
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_natIso`：preservesLimit_of_natIso
 (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G
 where preserves t
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
Transfer preservation of limits of shape along a natural isomorphism in the func
tor.
-/
lemma preservesLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := preservesLimit_of_natIso K h
/-
**CategoryTheory.Limits.preservesLimitsOfShape_iff_of_natIso** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) : Preserves
LimitsOfShape J F ↔ PreservesLimitsOfShape J G
参数：h : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
-/
lemma preservesLimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimitsOfShape J F ↔ PreservesLimitsOfShape J G :=
  ⟨fun _ ↦ preservesLimitsOfShape_of_natIso h, fun _ ↦ preservesLimitsOfShape_of_natIso h.symm⟩

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesLimits_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize
.{w, w'} F] : PreservesLimitsOfSize.{w, w'} G where preservesLimitsOfShape
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Transfer preservation of limits along a natural isomorphism in the functor.
-/
lemma preservesLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G where
  preservesLimitsOfShape := preservesLimitsOfShape_of_natIso h
/-
**CategoryTheory.Limits.preservesLimitsOfSize_iff_of_natIso** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) : PreservesL
imitsOfSize.{w, w'} F ↔ PreservesLimitsOfSize.{w, w'} G
参数：h : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_natIso`：preservesLimits_of_natI
so {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] : PreservesLimits
OfSize.{w, w'} G where preservesLimit…
-/
lemma preservesLimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimitsOfSize.{w, w'} F ↔ PreservesLimitsOfSize.{w, w'} G :=
  ⟨fun _ ↦ preservesLimits_of_natIso h, fun _ ↦ preservesLimits_of_natIso h.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transfer preservation of limits along an equivalence in the shape. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_equiv** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J 
≌ J') (F : C ⥤ D) [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F whe
re preservesLimit {K}
参数：e : J ≌ J'；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.invFunIdAssoc_hom_app`：invFunIdAssoc_hom_app 
(e : C ≌ D) (F : D ⥤ E) (X : D) : (invFunIdAssoc e F).hom.app X = F.map (e.couni
t.app X)
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer preservation of limits along an equivalence in the shape.
-/
lemma preservesLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F where
  preservesLimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cone.ext (Iso.refl _) fun j => ?_
        simp [equ, ← Functor.map_comp]⟩ }

/-- A functor preserving larger limits also preserves smaller limits. -/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_of_univLE** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, 
w₂'}] [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F wher
e preservesLimitsOfShape {J}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A functor preserving larger limits also preserves smaller limits.
-/
lemma preservesLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F where
  preservesLimitsOfShape {J} := preservesLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/-- `PreservesLimitsOfSize_shrink.{w w'} F` tries to obtain `PreservesLimitsOfSize.{w w'} F`
from some other `PreservesLimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.preservesLimitsOfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfSize_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂,
 max w' w₂'} F] : PreservesLimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfSize_of_univLE`：preservesLimitsOf
Size_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}] [PreservesLimitsO
fSize.{w', w₂'} F] : PreservesLimitsOfSize.…

--- 原说明 ---
`PreservesLimitsOfSize_shrink.{w w'} F` tries to obtain `PreservesLimitsOfSize.{
w w'} F`
from some other `PreservesLimitsOfSize F`.
-/
lemma preservesLimitsOfSize_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F := preservesLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/-- Preserving limits at any universe level implies preserving limits in universe `0`. -/
/-
**CategoryTheory.Limits.preservesSmallestLimits_of_preservesLimits** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesSmallestLimits_of_preservesLimits (F : C ⥤ D) [PreservesLimitsOfS
ize.{v₃, u₃} F] : PreservesLimitsOfSize.{0, 0} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfSize_shrink`：preservesLimitsOfSiz
e_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] : Preserve
sLimitsOfSize.{w, w'} F

--- 原说明 ---
Preserving limits at any universe level implies preserving limits in universe `0
`.
-/
lemma preservesSmallestLimits_of_preservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesLimitsOfSize_shrink F

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
/-
**CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h
 : IsColimit t) (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F
参数：h : IsColimit t；hF : IsColimit (F.mapCocone t)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K.
-/
lemma preservesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
  ⟨fun h' => ⟨IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩⟩
/-
**CategoryTheory.Limits.preservesColimit_iff_isColimit_mapCocone** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_iff_isColimit_mapCocone {F : C ⥤ D} {t : Cocone K} (h : I
sColimit t) : PreservesColimit K F ↔ Nonempty (IsColimit (F.mapCocone t))
参数：h : IsColimit t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
-/
lemma preservesColimit_iff_isColimit_mapCocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t) :
    PreservesColimit K F ↔ Nonempty (IsColimit (F.mapCocone t)) :=
  ⟨fun _ ↦ ⟨isColimitOfPreserves _ h⟩,
    fun h' ↦ preservesColimit_of_preserves_colimit_cocone h h'.some⟩

set_option backward.defeqAttrib.useBackward true in
/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
/-
**CategoryTheory.Limits.preservesColimit_of_iso_diagram** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) 
[PreservesColimit K₁ F] : PreservesColimit K₂ F where preserves {c} t
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer preservation of colimits along a natural isomorphism in the shape.
-/
lemma preservesColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesColimit K₁ F] :
    PreservesColimit K₂ F where
  preserves {c} t := ⟨by
    apply IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsColimit.precomposeHomEquiv h c).symm t
    apply IsColimit.ofIsoColimit (isColimitOfPreserves F this)
    exact Cocone.ext (Iso.refl _)⟩
/-
**CategoryTheory.Limits.preservesColimit_iff_of_iso_diagram** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ 
K₂) : PreservesColimit K₁ F ↔ PreservesColimit K₂ F
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
-/
lemma preservesColimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) :
    PreservesColimit K₁ F ↔ PreservesColimit K₂ F :=
  ⟨fun _ ↦ preservesColimit_of_iso_diagram _ h, fun _ ↦ preservesColimit_of_iso_diagram _ h.symm⟩

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesColimit_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [Preserve
sColimit K F] : PreservesColimit K G where preserves t
参数：K : J ⥤ C；h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer preservation of a colimit along a natural isomorphism in the functor.
-/
lemma preservesColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] :
    PreservesColimit K G where
  preserves t := ⟨IsColimit.mapCoconeEquiv h (isColimitOfPreserves F t)⟩
/-
**CategoryTheory.Limits.preservesColimit_iff_of_natIso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) : Pre
servesColimit K F ↔ PreservesColimit K G
参数：K : J ⥤ C；h : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t
-/
lemma preservesColimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) :
    PreservesColimit K F ↔ PreservesColimit K G :=
  ⟨fun _ ↦ preservesColimit_of_natIso _ h, fun _ ↦ preservesColimit_of_natIso _ h.symm⟩

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_natIso** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesCol
imitsOfShape J F] : PreservesColimitsOfShape J G where preservesColimit {K}
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_natIso`：preservesColimit_of_na
tIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesCol
imit K G where preserves t
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
Transfer preservation of colimits of shape along a natural isomorphism in the fu
nctor.
-/
lemma preservesColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := preservesColimit_of_natIso K h
/-
**CategoryTheory.Limits.preservesColimitsOfShape_iff_of_natIso** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) : Preserv
esColimitsOfShape J F ↔ PreservesColimitsOfShape J G
参数：h : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_natIso`：preservesColim
itsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] : 
PreservesColimitsOfShape J G where preservesCo…
-/
lemma preservesColimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesColimitsOfShape J F ↔ PreservesColimitsOfShape J G :=
  ⟨fun _ ↦ preservesColimitsOfShape_of_natIso h, fun _ ↦ preservesColimitsOfShape_of_natIso h.symm⟩

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesColimits_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：preservesColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOf
Size.{w, w'} F] : PreservesColimitsOfSize.{w, w'} G where preservesColimitsOfSha
pe {_J} _𝒥₁
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_natIso`：preservesColim
itsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] : 
PreservesColimitsOfShape J G where preservesCo…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Transfer preservation of colimits along a natural isomorphism in the functor.
-/
lemma preservesColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G where
  preservesColimitsOfShape {_J} _𝒥₁ := preservesColimitsOfShape_of_natIso h
/-
**CategoryTheory.Limits.preservesColimitsOfSize_iff_of_natIso** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) : Preserve
sColimitsOfSize.{w, w'} F ↔ PreservesColimitsOfSize.{w, w'} G
参数：h : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_natIso`：preservesColimits_of_
natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] : Preserves
ColimitsOfSize.{w, w'} G where preserve…
-/
lemma preservesColimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesColimitsOfSize.{w, w'} F ↔ PreservesColimitsOfSize.{w, w'} G :=
  ⟨fun _ ↦ preservesColimits_of_natIso h, fun _ ↦ preservesColimits_of_natIso h.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transfer preservation of colimits along an equivalence in the shape. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_equiv** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : 
J ≌ J') (F : C ⥤ D) [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J'
 F where preservesColimit {K}
参数：e : J ≌ J'；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.invFunIdAssoc_inv_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer preservation of colimits along an equivalence in the shape.
-/
lemma preservesColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F where
  preservesColimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
        refine Cocone.ext (Iso.refl _) fun j => ?_
        simp [equ, ← Functor.map_comp]⟩ }

/-- A functor preserving larger colimits also preserves smaller colimits. -/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_of_univLE** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂
, w₂'}] [PreservesColimitsOfSize.{w', w₂'} F] : PreservesColimitsOfSize.{w, w₂} 
F where preservesColimitsOfShape {J}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A functor preserving larger colimits also preserves smaller colimits.
-/
lemma preservesColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesColimitsOfSize.{w', w₂'} F] : PreservesColimitsOfSize.{w, w₂} F where
  preservesColimitsOfShape {J} := preservesColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/--
`PreservesColimitsOfSize_shrink.{w w'} F` tries to obtain `PreservesColimitsOfSize.{w w'} F`
from some other `PreservesColimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.preservesColimitsOfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfSize_shrink (F : C ⥤ D) [PreservesColimitsOfSize.{max w
 w₂, max w' w₂'} F] : PreservesColimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfSize_of_univLE`：preservesColimi
tsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}] [PreservesCol
imitsOfSize.{w', w₂'} F] : PreservesColimitsO…

--- 原说明 ---
`PreservesColimitsOfSize_shrink.{w w'} F` tries to obtain `PreservesColimitsOfSi
ze.{w w'} F`
from some other `PreservesColimitsOfSize F`.
-/
lemma preservesColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesColimitsOfSize.{w, w'} F := preservesColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/-- Preserving colimits at any universe implies preserving colimits at universe `0`. -/
/-
**CategoryTheory.Limits.preservesSmallestColimits_of_preservesColimits** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesSmallestColimits_of_preservesColimits (F : C ⥤ D) [PreservesColim
itsOfSize.{v₃, u₃} F] : PreservesColimitsOfSize.{0, 0} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfSize_shrink`：preservesColimitsO
fSize_shrink (F : C ⥤ D) [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] : Pr
eservesColimitsOfSize.{w, w'} F

--- 原说明 ---
Preserving colimits at any universe implies preserving colimits at universe `0`.
-/
lemma preservesSmallestColimits_of_preservesColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{v₃, u₃} F] :
    PreservesColimitsOfSize.{0, 0} F :=
  preservesColimitsOfSize_shrink F

/-- A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
/-
**CategoryTheory.Limits.ReflectsLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] → CategoryTheory.F
unctor J C → CategoryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects {c : Cone K} (hc : IsLimit (F.mapCone c)) : Nonempty (IsLimit c)

/-- A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
/-
**CategoryTheory.Limits.ReflectsColimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] → CategoryTheory.F
unctor J C → CategoryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects {c : Cocone K} (hc : IsColimit (F.mapCocone c)) : Nonempty (IsColimit c)

/-- A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
/-
**CategoryTheory.Limits.ReflectsLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory.Limits`。
形式化陈述：ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop wh
ere reflectsLimit : forall {K : J ⥤ C}, ReflectsLimit K F
参数：J : Type w；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in 
`D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsLimit : ∀ {K : J ⥤ C}, ReflectsLimit K F := by infer_instance

/-- A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
/-
**CategoryTheory.Limits.ReflectsColimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop 
where reflectsColimit : forall {K : J ⥤ C}, ReflectsColimit K F
参数：J : Type w；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit coco
ne in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsColimit : ∀ {K : J ⥤ C}, ReflectsColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.ReflectsLimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：ReflectsLimitsOfSize (F : C ⥤ D) : Prop where reflectsLimitsOfShape : fora
ll {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in 
`D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimitsOfSize (F : C ⥤ D) : Prop where
  reflectsLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F := by
    infer_instance

/-- A functor `F : C ⥤ D` reflects (small) limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
/-
**CategoryTheory.Limits.ReflectsLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：ReflectsLimits (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects (small) limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in 
`D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
abbrev ReflectsLimits (F : C ⥤ D) :=
  ReflectsLimitsOfSize.{v₂, v₂} F

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.ReflectsColimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：ReflectsColimitsOfSize (F : C ⥤ D) : Prop where reflectsColimitsOfShape : 
forall {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit coco
ne in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimitsOfSize (F : C ⥤ D) : Prop where
  reflectsColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F := by
    infer_instance

/-- A functor `F : C ⥤ D` reflects (small) colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
/-
**CategoryTheory.Limits.ReflectsColimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：ReflectsColimits (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` reflects (small) colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit coco
ne in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
abbrev ReflectsColimits (F : C ⥤ D) :=
  ReflectsColimitsOfSize.{v₂, v₂} F

/-- A convenience function for `ReflectsLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
/-
**CategoryTheory.Limits.isLimitOfReflects** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c)) [Re
flectsLimit K F] : IsLimit c
参数：F : C ⥤ D；t : IsLimit (F.mapCone c)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ReflectsLimit.reflects`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A convenience function for `ReflectsLimit`, which takes the functor as an explic
it argument to
guide typeclass resolution.
-/
def isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c))
    [ReflectsLimit K F] : IsLimit c :=
  (ReflectsLimit.reflects t).some

/--
A convenience function for `ReflectsColimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
/-
**CategoryTheory.Limits.isColimitOfReflects** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone
 c)) [ReflectsColimit K F] : IsColimit c
参数：F : C ⥤ D；t : IsColimit (F.mapCocone c)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ReflectsColimit.reflects`：∀ {C : Type u₁} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A convenience function for `ReflectsColimit`, which takes the functor as an expl
icit argument to
guide typeclass resolution.
-/
def isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c))
    [ReflectsColimit K F] : IsColimit c :=
  (ReflectsColimit.reflects t).some
/-
**CategoryTheory.Limits.reflectsLimit_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (Reflect
sLimit K F)
参数：K : J ⥤ C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.reflectsColimit_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (Refle
ctsColimit K F)
参数：K : J ⥤ C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflectsColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (ReflectsColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_subsingleton** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤
 D) : Subsingleton (ReflectsLimitsOfShape J F)
参数：J : Type w；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_subsingleton** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C
 ⥤ D) : Subsingleton (ReflectsColimitsOfShape J F)
参数：J : Type w；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflectsColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.reflects_limits_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflects_limits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsLimitsOfS
ize.{w', w} F)
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflects_limits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
/-
**CategoryTheory.Limits.reflects_colimits_subsingleton** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflects_colimits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsColimit
sOfSize.{w', w} F)
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflects_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsLimit_of_reflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  ReflectsLimitsOfShape.reflectsLimit

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsColimit_of_reflectsColimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimit K F :=
  ReflectsColimitsOfShape.reflectsColimit

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsLimitsOfShape_of_reflectsLimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  ReflectsLimitsOfSize.reflectsLimitsOfShape

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsColimitsOfShape_of_reflectsColimits
    (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w', w} F] : ReflectsColimitsOfShape J F :=
  ReflectsColimitsOfSize.reflectsColimitsOfShape
/-
**CategoryTheory.Limits.id_reflectsLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：id_reflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where reflectsLimit
sOfShape {J} 𝒥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
-/
instance id_reflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  reflectsLimitsOfShape {J} 𝒥 :=
    { reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }
/-
**CategoryTheory.Limits.id_reflectsColimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：id_reflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where reflectsC
olimitsOfShape {J} 𝒥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
-/
instance id_reflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  reflectsColimitsOfShape {J} 𝒥 :=
    { reflectsColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

/-
**CategoryTheory.Limits.comp_reflectsLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：comp_reflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] : Reflect
sLimit K (F ⋙ G)
参数：K ⋙ F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ReflectsLimit.reflects`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance comp_reflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) :=
  ⟨fun h => ReflectsLimit.reflects (isLimitOfReflects G h)⟩
/-
**CategoryTheory.Limits.comp_reflectsLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {E : Type u₃} [ℰ : CategoryTheory.Category.{v₃, u₃} E]
   (F : CategoryTheory.Functor C D) (G : CategoryTheory.Functor D E) [CategoryTh
eory.Limits.ReflectsLimitsOfShape J F]   [CategoryTheory.Limits.ReflectsLimitsOf
Shape J G], CategoryTheory.Limits.ReflectsLimitsOfShape J (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance comp_reflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) where
/-
**CategoryTheory.Limits.comp_reflectsLimits** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ℰ : CategoryTheor
y.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheory.Fu
nctor D E) [CategoryTheory.Limits.ReflectsLimitsOfSize.{w', w, v₁, v₂, u₁, u₂} F
]   [CategoryTheory.Limits.ReflectsLimitsOfSize.{w', w, v₂, v₃, u₂, u₃} G],   Ca
tegoryTheory.Limits.ReflectsLimitsOfSize.{w', w, v₁, v₃, u₁, u₃} (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_reflectsLimitsOfShape`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
instance comp_reflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) where
/-
**CategoryTheory.Limits.comp_reflectsColimit** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：comp_reflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] : R
eflectsColimit K (F ⋙ G)
参数：K ⋙ F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ReflectsColimit.reflects`：∀ {C : Type u₁} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance comp_reflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] :
    ReflectsColimit K (F ⋙ G) :=
  ⟨fun h => ReflectsColimit.reflects (isColimitOfReflects G h)⟩
/-
**CategoryTheory.Limits.comp_reflectsColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {E : Type u₃} [ℰ : CategoryTheory.Category.{v₃, u₃} E]
   (F : CategoryTheory.Functor C D) (G : CategoryTheory.Functor D E) [CategoryTh
eory.Limits.ReflectsColimitsOfShape J F]   [CategoryTheory.Limits.ReflectsColimi
tsOfShape J G], CategoryTheory.Limits.ReflectsColimitsOfShape J (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance comp_reflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) where
/-
**CategoryTheory.Limits.comp_reflectsColimits** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ℰ : CategoryTheor
y.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheory.Fu
nctor D E) [CategoryTheory.Limits.ReflectsColimitsOfSize.{w', w, v₁, v₂, u₁, u₂}
 F]   [CategoryTheory.Limits.ReflectsColimitsOfSize.{w', w, v₂, v₃, u₂, u₃} G], 
  CategoryTheory.Limits.ReflectsColimitsOfSize.{w', w, v₁, v₃, u₁, u₃} (F.comp G
)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_reflectsColimitsOfShape`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
instance comp_reflectsColimits [ReflectsColimitsOfSize.{w', w} F]
    [ReflectsColimitsOfSize.{w', w} G] : ReflectsColimitsOfSize.{w', w} (F ⋙ G) where

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
/-
**CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [Reflec
tsLimit (K ⋙ F) G] : PreservesLimit K F
参数：F ⋙ G；K ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`.
-/
lemma preservesLimit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  ⟨fun h => ⟨by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩⟩

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J 
(F ⋙ G)] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F where preserve
sLimit
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves`：preserves
Limit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F)
 G] : PreservesLimit K F
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, t
hen `F` preserves
limits of shape `J`.
-/
lemma preservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F where
  preservesLimit := preservesLimit_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F
 ⋙ G)] [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F where 
preservesLimitsOfShape
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`：p
reservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)
] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits.
-/
lemma preservesLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F where
  preservesLimitsOfShape := preservesLimitsOfShape_of_reflects_of_preserves F G

set_option backward.defeqAttrib.useBackward true in
/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
/-
**CategoryTheory.Limits.reflectsLimit_of_iso_diagram** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：reflectsLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [Re
flectsLimit K₁ F] : ReflectsLimit K₂ F where reflects {c} t
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer reflection of limits along a natural isomorphism in the diagram.
-/
lemma reflectsLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F where
  reflects {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoLimit _
    exact Cone.ext (Iso.refl _)⟩

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.reflectsLimit_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：reflectsLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLim
it K F] : ReflectsLimit K G where reflects t
参数：K : J ⥤ C；h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ReflectsLimit.reflects`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
Transfer reflection of a limit along a natural isomorphism in the functor.
-/
lemma reflectsLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G where
  reflects t := ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_natIso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsO
fShape J F] : ReflectsLimitsOfShape J G where reflectsLimit {K}
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_natIso`：reflectsLimit_of_natIso (
K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] : ReflectsLimit K G whe
re reflects t
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
Transfer reflection of limits of shape along a natural isomorphism in the functo
r.
-/
lemma reflectsLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where
  reflectsLimit {K} := reflectsLimit_of_natIso K h

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.reflectsLimits_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：reflectsLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{
w', w} F] : ReflectsLimitsOfSize.{w', w} G where reflectsLimitsOfShape
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_natIso`：reflectsLimitsOfS
hape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] : ReflectsL
imitsOfShape J G where reflectsLimit {K}
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
Transfer reflection of limits along a natural isomorphism in the functor.
-/
lemma reflectsLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_natIso h

/-- Transfer reflection of limits along an equivalence in the shape. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌
 J') (F : C ⥤ D) [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F where 
reflectsLimit {K}
参数：e : J ≌ J'；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
Transfer reflection of limits along an equivalence in the shape.
-/
lemma reflectsLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F where
  reflectsLimit {K} :=
    { reflects := fun {c} t => ⟨by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _⟩ }

/-- A functor reflecting larger limits also reflects smaller limits. -/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_of_univLE** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w
₂'}] [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F where r
eflectsLimitsOfShape {J}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
A functor reflecting larger limits also reflects smaller limits.
-/
lemma reflectsLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F where
  reflectsLimitsOfShape {J} := reflectsLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/-- `reflectsLimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsLimitsOfSize.{w w'} F`
from some other `reflectsLimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.reflectsLimitsOfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfSize_shrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, m
ax w' w₂'} F] : ReflectsLimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfSize_of_univLE`：reflectsLimitsOfSi
ze_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}] [ReflectsLimitsOfSi
ze.{w', w₂'} F] : ReflectsLimitsOfSize.{w,…

--- 原说明 ---
`reflectsLimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsLimitsOfSize.{w 
w'} F`
from some other `reflectsLimitsOfSize F`.
-/
lemma reflectsLimitsOfSize_shrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F := reflectsLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/-- Reflecting limits at any universe implies reflecting limits at universe `0`. -/
/-
**CategoryTheory.Limits.reflectsSmallestLimits_of_reflectsLimits** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsSmallestLimits_of_reflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize
.{v₃, u₃} F] : ReflectsLimitsOfSize.{0, 0} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfSize_shrink`：reflectsLimitsOfSize_
shrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] : ReflectsLim
itsOfSize.{w, w'} F

--- 原说明 ---
Reflecting limits at any universe implies reflecting limits at universe `0`.
-/
lemma reflectsSmallestLimits_of_reflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsLimitsOfSize_shrink F

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F` (see also `JointlyReflectIsomorphisms.jointlyReflectsColimit` in
the file `CategoryTheory/Functor/ReflectsIso/Limits.lean` for the corresponding result
for a family of functors which joinly reflect isomorphisms).
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
/-
**CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsI
somorphisms] [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G where reflect
s {c} t
参数：F : J ⥤ C；G : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_isIso`：hom_isIso {s t : Cone F} (P : I
sLimit s) (Q : IsLimit t) (f : s ⟶ t) : IsIso f
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
lemma reflectsLimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G where
  reflects {c} t := by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from ⟨by
      apply IsLimit.ofPointIso (limit.isLimit F)⟩
    change IsIso ((Cone.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cone.forget F).map_isIso _
    suffices IsIso ((Cone.functoriality F G).map
      (IsLimit.liftConeMorphism (limit.isLimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cone.functoriality F G)
    exact t.hom_isIso (isLimitOfPreserves G (limit.isLimit F)) _

/-- If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
/-
**CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomo
rphisms] [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfS
hape J G where reflectsLimit {F}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms`：reflectsLim
it_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] [Has
Limit F] [PreservesLimit F G] : ReflectsLimit F G…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isom
orphisms then it
reflects limits of shape `J`.
-/
lemma reflectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G where
  reflectsLimit {F} := reflectsLimit_of_reflectsIsomorphisms F G

/-- If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
/-
**CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsLimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms
] [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] : ReflectsLimits
OfSize.{w', w} G where reflectsLimitsOfShape
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms th
en it reflects
limits.
-/
lemma reflectsLimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_reflectsIsomorphisms

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
/-
**CategoryTheory.Limits.preservesColimit_of_reflects_of_preserves** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_of_reflects_of_preserves [PreservesColimit K (F ⋙ G)] [Re
flectsColimit (K ⋙ F) G] : PreservesColimit K F
参数：F ⋙ G；K ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`.
-/
lemma preservesColimit_of_reflects_of_preserves
    [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  ⟨fun {c} h => ⟨by
    apply isColimitOfReflects G
    apply isColimitOfPreserves (F ⋙ G) h⟩⟩

/-- If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_reflects_of_preserves** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShap
e J (F ⋙ G)] [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F where 
preservesColimit
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_reflects_of_preserves`：preserv
esColimit_of_reflects_of_preserves [PreservesColimit K (F ⋙ G)] [ReflectsColimit
 (K ⋙ F) G] : PreservesColimit K F
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J
`, then `F`
preserves colimits of shape `J`.
-/
lemma preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (F ⋙ G)]
    [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit := preservesColimit_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_of_reflects_of_preserves** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimits_of_reflects_of_preserves [PreservesColimitsOfSize.{w', w
} (F ⋙ G)] [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} 
F where preservesColimitsOfShape
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_reflects_of_preserves`
：preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (
F ⋙ G)] [ReflectsColimitsOfShape J G] : PreservesColimitsOfSh…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves coli
mits.
-/
lemma preservesColimits_of_reflects_of_preserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F where
  preservesColimitsOfShape := preservesColimitsOfShape_of_reflects_of_preserves F G

set_option backward.defeqAttrib.useBackward true in
/-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/
/-
**CategoryTheory.Limits.reflectsColimit_of_iso_diagram** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：reflectsColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [
ReflectsColimit K₁ F] : ReflectsColimit K₂ F where reflects {c} t
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer reflection of colimits along a natural isomorphism in the diagram.
-/
lemma reflectsColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F where
  reflects {c} t := ⟨by
    apply IsColimit.precomposeHomEquiv h c (isColimitOfReflects F _)
    apply ((IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoColimit _
    exact Cocone.ext (Iso.refl _)⟩

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.reflectsColimit_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：reflectsColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsC
olimit K F] : ReflectsColimit K G where reflects t
参数：K : J ⥤ C；h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ReflectsColimit.reflects`：∀ {C : Type u₁} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
Transfer reflection of a colimit along a natural isomorphism in the functor.
-/
lemma reflectsColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] :
    ReflectsColimit K G where
  reflects t := ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_natIso** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColim
itsOfShape J F] : ReflectsColimitsOfShape J G where reflectsColimit {K}
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_natIso`：reflectsColimit_of_natI
so (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] : ReflectsColimit
 K G where reflects t
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
Transfer reflection of colimits of shape along a natural isomorphism in the func
tor.
-/
lemma reflectsColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G where
  reflectsColimit {K} := reflectsColimit_of_natIso K h

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.reflectsColimits_of_natIso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：reflectsColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSi
ze.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} G where reflectsColimitsOfShape
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_natIso`：reflectsColimit
sOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] : Ref
lectsColimitsOfShape J G where reflectsColimi…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
Transfer reflection of colimits along a natural isomorphism in the functor.
-/
lemma reflectsColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_natIso h

/-- Transfer reflection of colimits along an equivalence in the shape. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J
 ≌ J') (F : C ⥤ D) [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F 
where reflectsColimit
参数：e : J ≌ J'；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…

--- 原说明 ---
Transfer reflection of colimits along an equivalence in the shape.
-/
lemma reflectsColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F where
  reflectsColimit :=
    { reflects := fun {c} t => ⟨by
        apply IsColimit.ofWhiskerEquivalence e
        apply isColimitOfReflects F
        apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _).symm
        exact IsColimit.whiskerEquivalence t _⟩ }

/-- A functor reflecting larger colimits also reflects smaller colimits. -/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_of_univLE** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂,
 w₂'}] [ReflectsColimitsOfSize.{w', w₂'} F] : ReflectsColimitsOfSize.{w, w₂} F w
here reflectsColimitsOfShape {J}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
A functor reflecting larger colimits also reflects smaller colimits.
-/
lemma reflectsColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsColimitsOfSize.{w', w₂'} F] : ReflectsColimitsOfSize.{w, w₂} F where
  reflectsColimitsOfShape {J} := reflectsColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/-- `reflectsColimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsColimitsOfSize.{w w'} F`
from some other `reflectsColimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.reflectsColimitsOfSize_shrink** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfSize_shrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w
₂, max w' w₂'} F] : ReflectsColimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfSize_of_univLE`：reflectsColimits
OfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}] [ReflectsColimi
tsOfSize.{w', w₂'} F] : ReflectsColimitsOfSi…

--- 原说明 ---
`reflectsColimitsOfSize_shrink.{w w'} F` tries to obtain `reflectsColimitsOfSize
.{w w'} F`
from some other `reflectsColimitsOfSize F`.
-/
lemma reflectsColimitsOfSize_shrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsColimitsOfSize.{w, w'} F := reflectsColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/-- Reflecting colimits at any universe implies reflecting colimits at universe `0`. -/
/-
**CategoryTheory.Limits.reflectsSmallestColimits_of_reflectsColimits** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsSmallestColimits_of_reflectsColimits (F : C ⥤ D) [ReflectsColimits
OfSize.{v₃, u₃} F] : ReflectsColimitsOfSize.{0, 0} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfSize_shrink`：reflectsColimitsOfS
ize_shrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] : Refle
ctsColimitsOfSize.{w, w'} F

--- 原说明 ---
Reflecting colimits at any universe implies reflecting colimits at universe `0`.
-/
lemma reflectsSmallestColimits_of_reflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F] :
    ReflectsColimitsOfSize.{0, 0} F :=
  reflectsColimitsOfSize_shrink F

/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F` (see also `JointlyReflectIsomorphisms.jointlyReflectsLimit` in
the file `CategoryTheory/Functor/ReflectsIso/Limits.lean` for the corresponding result
for a family of functors which joinly reflect isomorphisms).
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
/-
**CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.Reflect
sIsomorphisms] [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G where
 reflects {c} t
参数：F : J ⥤ C；G : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_isIso`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.Limits.Cocone.reflects_cocone_isomorphism`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTh
eory.Category.{v₃, u₃} C]   {D : Type u₄} [ins…
-/
lemma reflectsColimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G where
  reflects {c} t := by
    suffices IsIso (IsColimit.desc (colimit.isColimit F) c) from ⟨by
      apply IsColimit.ofPointIso (colimit.isColimit F)⟩
    change IsIso ((Cocone.forget _).map ((colimit.isColimit F).descCoconeMorphism c))
    suffices IsIso (IsColimit.descCoconeMorphism (colimit.isColimit F) c) from by
      apply (Cocone.forget F).map_isIso _
    suffices IsIso ((Cocone.functoriality F G).map
      (IsColimit.descCoconeMorphism (colimit.isColimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cocone.functoriality F G)
    exact (isColimitOfPreserves G (colimit.isColimit F)).hom_isIso t _

/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
/-
**CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIso
morphisms] [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsCol
imitsOfShape J G where reflectsColimit {F}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms`：reflectsC
olimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] 
[HasColimit F] [PreservesColimit F G] : ReflectsCol…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects is
omorphisms then it
reflects colimits of shape `J`.
-/
lemma reflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G where
  reflectsColimit {F} := reflectsColimit_of_reflectsIsomorphisms F G

/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
/-
**CategoryTheory.Limits.reflectsColimits_of_reflectsIsomorphisms** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsColimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphis
ms] [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] : Reflects
ColimitsOfSize.{w', w} G where reflectsColimitsOfShape
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms`：r
eflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphis
ms] [HasColimitsOfShape J C] [PreservesColimitsOfShape J G]…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphism
s then it reflects
colimits.
-/
lemma reflectsColimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} G where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_reflectsIsomorphisms

end

section

open CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.isIso_app_coconePt_of_preservesColimit** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_app_coconePt_of_preservesColimit {C D J : Type*} [Category* C] [Cate
gory* D] [Category* J] (K : J ⥤ C) {L L' : C ⥤ D} (α : L ⟶ L') [IsIso (whiskerLe
ft K α)] (c : Cocone K) (hc : IsColimit c) [PreservesColimit K L] [PreservesColi
mit K L'] : IsIso (α.app c.pt)
参数：K : J ⥤ C；α : L ⟶ L'；whiskerLeft K α；c : Cocone K；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} C]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_app_coconePt_of_preservesColimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J] (K : J ⥤ C) {L L' : C ⥤ D}
    (α : L ⟶ L') [IsIso (whiskerLeft K α)] (c : Cocone K) (hc : IsColimit c)
    [PreservesColimit K L] [PreservesColimit K L'] :
    IsIso (α.app c.pt) := by
  let e := IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves L hc) (isColimitOfPreserves L' hc) (asIso (whiskerLeft K α))
  convert! (inferInstance : IsIso e.hom)
  apply (isColimitOfPreserves L hc).hom_ext fun j ↦ ?_
  simp only [Functor.comp_obj, Functor.mapCocone_pt, Functor.mapCocone_ι_app,
    NatTrans.naturality, IsColimit.coconePointsIsoOfNatIso_hom, asIso_hom, e]
  refine (((isColimitOfPreserves L hc).ι_map (L'.mapCocone c) (whiskerLeft K α) j).trans ?_).symm
  simp

end

variable (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency.types false in
/-- A fully faithful functor reflects limits. -/
/-
**CategoryTheory.Limits.fullyFaithful_reflectsLimits** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：fullyFaithful_reflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.
{w, w'} F where reflectsLimitsOfShape {J} 𝒥₁
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq_cone_morphism`：uniq_cone_morphism {s 
t : Cone F} (h : IsLimit t) {f f' : s ⟶ t} : f = f'

--- 原说明 ---
A fully faithful functor reflects limits.
-/
instance fullyFaithful_reflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {J} 𝒥₁ :=
    { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsLimit.mkConeMorphism fun _ =>
                (Cone.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cone.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cone_morphism⟩ } }
set_option backward.isDefEq.respectTransparency.types false in
/-- A fully faithful functor reflects colimits. -/
/-
**CategoryTheory.Limits.fullyFaithful_reflectsColimits** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：fullyFaithful_reflectsColimits [F.Full] [F.Faithful] : ReflectsColimitsOfS
ize.{w, w'} F where reflectsColimitsOfShape {J} 𝒥₁
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cocone.functoriality_full`：∀ {J : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Cate
gory.{v₃, u₃} C]   {D : Type u₄} [ins…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Limits.Cocone.functoriality_faithful`：∀ {J : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.
Category.{v₃, u₃} C]   {D : Type u₄} [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq_cocone_morphism`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory
.Category.{v₃, u₃} C]   {F : CategoryTheor…

--- 原说明 ---
A fully faithful functor reflects colimits.
-/
instance fullyFaithful_reflectsColimits [F.Full] [F.Faithful] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {J} 𝒥₁ :=
    { reflectsColimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsColimit.mkCoconeMorphism fun _ =>
                (Cocone.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (Cocone.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cocone_morphism⟩ } }

end CategoryTheory.Limits

