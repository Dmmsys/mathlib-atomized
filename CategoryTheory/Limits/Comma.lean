/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Unit
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Limits and colimits in comma categories

We build limits in the comma category `Comma L R` provided that the two source categories have
limits and `R` preserves them.
This is used to construct limits in the arrow category, structured arrow category and under
category, and show that the appropriate forgetful functors create limits.

The duals of all the above are also given.
-/

@[expose] public section


namespace CategoryTheory

open Category Limits CategoryTheory.Functor

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {J : Type w} [Category.{w'} J]
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

namespace Comma

variable {L : A ⥤ T} {R : B ⥤ T}
variable (F : J ⥤ Comma L R)

/-- (Implementation). An auxiliary cone which is useful in order to construct limits
in the comma category. -/
@[simps!]
/-
**CategoryTheory.Comma.limitAuxiliaryCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Comma`。
形式化陈述：limitAuxiliaryCone (c₁ : Cone (F ⋙ fst L R)) : Cone ((F ⋙ snd L R) ⋙ R)
参数：c₁ : Cone (F ⋙ fst L R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). An auxiliary cone which is useful in order to construct limits
in the comma category.
-/
def limitAuxiliaryCone (c₁ : Cone (F ⋙ fst L R)) : Cone ((F ⋙ snd L R) ⋙ R) :=
  (Cone.postcompose (whiskerLeft F (Comma.natTrans L R) :)).obj (L.mapCone c₁)

set_option backward.defeqAttrib.useBackward true in
/-- If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤ L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn out to be a limit
cone.
-/
@[simps]
/-
**CategoryTheory.Comma.coneOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Comma`。
形式化陈述：coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
 {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : Cone F where pt
参数：F ⋙ snd L R；c₁ : Cone (F ⋙ fst L R)；F ⋙ snd L R；t₂ : IsLimit c₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤
 L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn
 out to be a limit
cone.
-/
noncomputable def coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
    {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : Cone F where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j
          right := c₂.π.app j
          w := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm }
      naturality := fun j₁ j₂ t => by
        ext
        · simp [← c₁.w t]
        · simp [← c₂.w t] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `F : J ⥤ Comma L R`. If `R` preserves the limit of
`F ⋙ snd _ _`, then `Comma.fst L R` and `Comma.snd L R` jointly
reflect the limit of `F`, i.e. if `c` is a cone for `F` which
becomes a limit after applying `Comma.fst L R` and `Comma.snd L R`,
then `c` is a limit. -/
/-
**CategoryTheory.Comma.fstSndJointlyReflectLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Comma`。
形式化陈述：fstSndJointlyReflectLimit {F : J ⥤ Comma L R} {c : Cone F} [PreservesLimit
 (F ⋙ snd _ _) R] (h₁ : IsLimit ((fst _ _).mapCone c)) (h₂ : IsLimit ((snd _ _).
mapCone c)) : IsLimit c where lift s
参数：F ⋙ snd _ _；h₁ : IsLimit ((fst _ _).mapCone c)；h₂ : IsLimit ((snd _ _).mapCon
e c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F : J ⥤ Comma L R`. If `R` preserves the limit of
`F ⋙ snd _ _`, then `Comma.fst L R` and `Comma.snd L R` jointly
reflect the limit of `F`, i.e. if `c` is a cone for `F` which
becomes a limit after applying `Comma.fst L R` and `Comma.snd L R`,
then `c` is a limit.
-/
def fstSndJointlyReflectLimit {F : J ⥤ Comma L R} {c : Cone F}
    [PreservesLimit (F ⋙ snd _ _) R]
    (h₁ : IsLimit ((fst _ _).mapCone c))
    (h₂ : IsLimit ((snd _ _).mapCone c)) :
    IsLimit c where
  lift s :=
    { left := h₁.lift ((fst _ _).mapCone s)
      right := h₂.lift ((snd _ _).mapCone s)
      w := (isLimitOfPreserves R h₂).hom_ext (fun j ↦ by
        simp [← Functor.map_comp, ← Functor.map_comp_assoc, ← CommaMorphism.w,
          dsimp% h₂.fac ((snd _ _).mapCone s) j,
          dsimp% h₁.fac ((fst _ _).mapCone s) j]) }
  fac s j := by
    ext
    · exact h₁.fac ((fst _ _).mapCone s) j
    · exact h₂.fac ((snd _ _).mapCone s) j
  uniq s _ hm := by
    ext
    · exact h₁.uniq ((fst _ _).mapCone s) _ (by simp [← hm])
    · exact h₂.uniq ((snd _ _).mapCone s) _ (by simp [← hm])

/-- Provided that `R` preserves the appropriate limit, then the cone in `coneOfPreserves` is a
limit. -/
/-
**CategoryTheory.Comma.coneOfPreservesIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Comma`。
形式化陈述：coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fs
t L R)} (t₁ : IsLimit c₁) {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : IsLimit 
(coneOfPreserves F c₁ t₂)
参数：F ⋙ snd L R；F ⋙ fst L R；t₁ : IsLimit c₁；F ⋙ snd L R；t₂ : IsLimit c₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Provided that `R` preserves the appropriate limit, then the cone in `coneOfPrese
rves` is a
limit.
-/
noncomputable def coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
    (t₁ : IsLimit c₁) {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) :
    IsLimit (coneOfPreserves F c₁ t₂) :=
  fstSndJointlyReflectLimit t₁ t₂

/-- (Implementation). An auxiliary cocone which is useful in order to construct colimits
in the comma category. -/
@[simps!]
/-
**CategoryTheory.Comma.colimitAuxiliaryCocone** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Comma`。
形式化陈述：colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R)
 ⋙ L)
参数：c₂ : Cocone (F ⋙ snd L R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). An auxiliary cocone which is useful in order to construct coli
mits
in the comma category.
-/
def colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R) ⋙ L) :=
  (Cocone.precompose (whiskerLeft F (Comma.natTrans L R) :)).obj (R.mapCocone c₂)

set_option backward.defeqAttrib.useBackward true in
/--
If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ fst L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn out to be a
colimit cocone.
-/
@[simps]
/-
**CategoryTheory.Comma.coconeOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Comma`。
形式化陈述：coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst
 L R)} (t₁ : IsColimit c₁) (c₂ : Cocone (F ⋙ snd L R)) : Cocone F where pt
参数：F ⋙ fst L R；F ⋙ fst L R；t₁ : IsColimit c₁；c₂ : Cocone (F ⋙ snd L R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ f
st L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn
 out to be a
colimit cocone.
-/
noncomputable def coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) (c₂ : Cocone (F ⋙ snd L R)) : Cocone F where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j
          right := c₂.ι.app j
          w := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j }
      naturality := fun j₁ j₂ t => by
        ext
        · simp [← c₁.w t]
        · simp [← c₂.w t] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `F : J ⥤ Comma L R`. If `L` preserves the colimit of
`F ⋙ fst _ _`, then `Comma.fst L R` and `Comma.snd L R` jointly
reflect the colimit of `F`, i.e. if `c` is a cocone for `F` which
becomes a colimit after applying `Comma.fst L R` and `Comma.snd L R`,
then `c` is a colimit. -/
/-
**CategoryTheory.Comma.fstSndJointlyReflectColimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Comma`。
形式化陈述：fstSndJointlyReflectColimit {F : J ⥤ Comma L R} {c : Cocone F} [PreservesC
olimit (F ⋙ fst _ _) L] (h₁ : IsColimit ((fst _ _).mapCocone c)) (h₂ : IsColimit
 ((snd _ _).mapCocone c)) : IsColimit c where desc s
参数：F ⋙ fst _ _；h₁ : IsColimit ((fst _ _).mapCocone c)；h₂ : IsColimit ((snd _ _).
mapCocone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F : J ⥤ Comma L R`. If `L` preserves the colimit of
`F ⋙ fst _ _`, then `Comma.fst L R` and `Comma.snd L R` jointly
reflect the colimit of `F`, i.e. if `c` is a cocone for `F` which
becomes a colimit after applying `Comma.fst L R` and `Comma.snd L R`,
then `c` is a colimit.
-/
def fstSndJointlyReflectColimit {F : J ⥤ Comma L R} {c : Cocone F}
    [PreservesColimit (F ⋙ fst _ _) L]
    (h₁ : IsColimit ((fst _ _).mapCocone c))
    (h₂ : IsColimit ((snd _ _).mapCocone c)) :
    IsColimit c where
  desc s :=
    { left := h₁.desc ((fst _ _).mapCocone s)
      right := h₂.desc ((snd _ _).mapCocone s)
      w := (isColimitOfPreserves L h₁).hom_ext (fun j ↦ by
        simp [← Functor.map_comp_assoc, ← Functor.map_comp,
          dsimp% h₁.fac ((fst _ _).mapCocone s) j,
          dsimp% h₂.fac ((snd _ _).mapCocone s) j]) }
  fac s j := by
    ext
    · exact h₁.fac ((fst _ _).mapCocone s) j
    · exact h₂.fac ((snd _ _).mapCocone s) j
  uniq s _ hm := by
    ext
    · exact h₁.uniq ((fst _ _).mapCocone s) _ (by simp [← hm])
    · exact h₂.uniq ((snd _ _).mapCocone s) _ (by simp [← hm])

/-- Provided that `L` preserves the appropriate colimit, then the cocone in `coconeOfPreserves` is
a colimit. -/
/-
**CategoryTheory.Comma.coconeOfPreservesIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Comma`。
形式化陈述：coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone
 (F ⋙ fst L R)} (t₁ : IsColimit c₁) {c₂ : Cocone (F ⋙ snd L R)} (t₂ : IsColimit 
c₂) : IsColimit (coconeOfPreserves F t₁ c₂)
参数：F ⋙ fst L R；F ⋙ fst L R；t₁ : IsColimit c₁；F ⋙ snd L R；t₂ : IsColimit c₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Provided that `L` preserves the appropriate colimit, then the cocone in `coconeO
fPreserves` is
a colimit.
-/
noncomputable def coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L]
    {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) {c₂ : Cocone (F ⋙ snd L R)} (t₂ : IsColimit c₂) :
    IsColimit (coconeOfPreserves F t₁ c₂) :=
  fstSndJointlyReflectColimit t₁ t₂
/-
**CategoryTheory.Comma.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma`
。
形式化陈述：hasLimit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L
 R)] [PreservesLimit (F ⋙ snd L R) R] : HasLimit F
参数：F : J ⥤ Comma L R；F ⋙ fst L R；F ⋙ snd L R；F ⋙ snd L R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
    [PreservesLimit (F ⋙ snd L R) R] : HasLimit F :=
  HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩
/-
**CategoryTheory.Comma.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Comma`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] {A : Type u₁} [i
nst_1 : CategoryTheory.Category.{v₁, u₁} A]   {B : Type u₂} [inst_2 : CategoryTh
eory.Category.{v₂, u₂} B] {T : Type u₃}   [inst_3 : CategoryTheory.Category.{v₃,
 u₃} T] {L : CategoryTheory.Functor A T} {R : CategoryTheory.Functor B T}   [Cat
egoryTheory.Limits.HasLimitsOfShape J A] [CategoryTheory.Limits.HasLimitsOfShape
 J B]   [CategoryTheory.Limits.PreservesLimitsOfShape J R],   CategoryTheory.Lim
its.HasLimitsOfShape J (CategoryTheory.Comma L R)
参数：CategoryTheory.Comma L R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance hasLimitsOfShape [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : HasLimitsOfShape J (Comma L R) where
/-
**CategoryTheory.Comma.hasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Comma`。
形式化陈述：hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B] [P
reservesLimitsOfSize.{w, w'} R] : HasLimitsOfSize.{w, w'} (Comma L R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.hasLimitsOfShape`：∀ {J : Type w} [inst : CategoryTh
eory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u₁
} A]   {B : Type u₂} [inst_…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B]
    [PreservesLimitsOfSize.{w, w'} R] : HasLimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩
/-
**CategoryTheory.Comma.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Comma`。
形式化陈述：hasFiniteLimits [HasFiniteLimits A] [HasFiniteLimits B] [PreservesFiniteLi
mits R] : HasFiniteLimits (Comma L R) where out _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.hasLimitsOfShape`：∀ {J : Type w} [inst : CategoryTh
eory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u₁
} A]   {B : Type u₂} [inst_…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasFiniteLimits [HasFiniteLimits A] [HasFiniteLimits B]
    [PreservesFiniteLimits R] : HasFiniteLimits (Comma L R) where
      out _ _ _ := inferInstance
/-
**CategoryTheory.Comma.hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comm
a`。
形式化陈述：hasColimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙
 snd L R)] [PreservesColimit (F ⋙ fst L R) L] : HasColimit F
参数：F : J ⥤ Comma L R；F ⋙ fst L R；F ⋙ snd L R；F ⋙ fst L R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
    [PreservesColimit (F ⋙ fst L R) L] : HasColimit F :=
  HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩
/-
**CategoryTheory.Comma.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Comma`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] {A : Type u₁} [i
nst_1 : CategoryTheory.Category.{v₁, u₁} A]   {B : Type u₂} [inst_2 : CategoryTh
eory.Category.{v₂, u₂} B] {T : Type u₃}   [inst_3 : CategoryTheory.Category.{v₃,
 u₃} T] {L : CategoryTheory.Functor A T} {R : CategoryTheory.Functor B T}   [Cat
egoryTheory.Limits.HasColimitsOfShape J A] [CategoryTheory.Limits.HasColimitsOfS
hape J B]   [CategoryTheory.Limits.PreservesColimitsOfShape J L],   CategoryTheo
ry.Limits.HasColimitsOfShape J (CategoryTheory.Comma L R)
参数：CategoryTheory.Comma L R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance hasColimitsOfShape [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : HasColimitsOfShape J (Comma L R) where
/-
**CategoryTheory.Comma.hasColimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Comma`。
形式化陈述：hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'}
 B] [PreservesColimitsOfSize.{w, w'} L] : HasColimitsOfSize.{w, w'} (Comma L R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.hasColimitsOfShape`：∀ {J : Type w} [inst : Category
Theory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, 
u₁} A]   {B : Type u₂} [inst_…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'} B]
    [PreservesColimitsOfSize.{w, w'} L] : HasColimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩
/-
**CategoryTheory.Comma.hasFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Comma`。
形式化陈述：hasFiniteColimits [HasFiniteColimits A] [HasFiniteColimits B] [PreservesFi
niteColimits L] : HasFiniteColimits (Comma L R) where out _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.hasColimitsOfShape`：∀ {J : Type w} [inst : Category
Theory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, 
u₁} A]   {B : Type u₂} [inst_…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasFiniteColimits [HasFiniteColimits A] [HasFiniteColimits B]
    [PreservesFiniteColimits L] : HasFiniteColimits (Comma L R) where
      out _ _ _ := inferInstance
/-
**CategoryTheory.Comma.preservesColimitsOfShape_fst** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Comma`。
形式化陈述：preservesColimitsOfShape_fst [HasColimitsOfShape J A] [HasColimitsOfShape 
J B] [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.fst L R)
 where preservesColimit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance preservesColimitsOfShape_fst [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.fst L R) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)
/-
**CategoryTheory.Comma.preservesColimitsOfShape_snd** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Comma`。
形式化陈述：preservesColimitsOfShape_snd [HasColimitsOfShape J A] [HasColimitsOfShape 
J B] [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.snd L R)
 where preservesColimit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Comma.hasColimitsOfShape`：∀ {J : Type w} [inst : Category
Theory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, 
u₁} A]   {B : Type u₂} [inst_…
-/
instance preservesColimitsOfShape_snd [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.snd L R) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

end Comma

namespace Arrow

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Arrow.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arrow`
。
形式化陈述：hasLimit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (
F ⋙ rightFunc)] : HasLimit F
参数：F : J ⥤ Arrow T；F ⋙ leftFunc；F ⋙ rightFunc。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasLimit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)] :
    HasLimit F := by
  have : HasLimit (F ⋙ Comma.fst _ _) := i₁
  have : HasLimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasLimit
/-
**CategoryTheory.Arrow.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Arrow`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] {T : Type u₃} [i
nst_1 : CategoryTheory.Category.{v₃, u₃} T]   [CategoryTheory.Limits.HasLimitsOf
Shape J T], CategoryTheory.Limits.HasLimitsOfShape J (CategoryTheory.Arrow T)
参数：CategoryTheory.Arrow T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfShape [HasLimitsOfShape J T] : HasLimitsOfShape J (Arrow T) where
/-
**CategoryTheory.Arrow.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Arrow`。
形式化陈述：hasFiniteLimits [HasFiniteLimits T] : HasFiniteLimits (Arrow T) where out 
_ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.hasLimitsOfShape`：∀ {J : Type w} [inst : CategoryTh
eory.Category.{w', w} J] {T : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} T]   [CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteLimits [HasFiniteLimits T] : HasFiniteLimits (Arrow T) where
  out _ _ _ := inferInstance
/-
**CategoryTheory.Arrow.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：hasLimits [HasLimits T] : HasLimits (Arrow T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.hasLimitsOfShape`：∀ {J : Type w} [inst : CategoryTh
eory.Category.{w', w} J] {T : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} T]   [CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimits [HasLimits T] : HasLimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Arrow.hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：hasColimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)] [i₂ : HasCol
imit (F ⋙ rightFunc)] : HasColimit F
参数：F : J ⥤ Arrow T；F ⋙ leftFunc；F ⋙ rightFunc。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasColimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
    [i₂ : HasColimit (F ⋙ rightFunc)] : HasColimit F := by
  have : HasColimit (F ⋙ Comma.fst _ _) := i₁
  have : HasColimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasColimit
/-
**CategoryTheory.Arrow.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Arrow`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] {T : Type u₃} [i
nst_1 : CategoryTheory.Category.{v₃, u₃} T]   [CategoryTheory.Limits.HasColimits
OfShape J T], CategoryTheory.Limits.HasColimitsOfShape J (CategoryTheory.Arrow T
)
参数：CategoryTheory.Arrow T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfShape [HasColimitsOfShape J T] : HasColimitsOfShape J (Arrow T) where
/-
**CategoryTheory.Arrow.hasFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Arrow`。
形式化陈述：hasFiniteColimits [HasFiniteColimits T] : HasFiniteColimits (Arrow T) wher
e out _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.hasColimitsOfShape`：∀ {J : Type w} [inst : Category
Theory.Category.{w', w} J] {T : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} T]   [CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
-/
instance hasFiniteColimits [HasFiniteColimits T] : HasFiniteColimits (Arrow T) where
  out _ _ _ := inferInstance
/-
**CategoryTheory.Arrow.hasColimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：hasColimits [HasColimits T] : HasColimits (Arrow T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.hasColimitsOfShape`：∀ {J : Type w} [inst : Category
Theory.Category.{w', w} J] {T : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, 
u₃} T]   [CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimits [HasColimits T] : HasColimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩
/-
**CategoryTheory.Arrow.preservesColimitsOfShape_leftFunc** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Arrow`。
形式化陈述：preservesColimitsOfShape_leftFunc [HasColimitsOfShape J T] : PreservesColi
mitsOfShape J (Arrow.leftFunc : _ ⥤ T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance preservesColimitsOfShape_leftFunc [HasColimitsOfShape J T] :
    PreservesColimitsOfShape J (Arrow.leftFunc : _ ⥤ T) := by
  apply Comma.preservesColimitsOfShape_fst
/-
**CategoryTheory.Arrow.preservesColimitsOfShape_rightFunc** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Arrow`。
形式化陈述：preservesColimitsOfShape_rightFunc [HasColimitsOfShape J T] : PreservesCol
imitsOfShape J (Arrow.rightFunc : _ ⥤ T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance preservesColimitsOfShape_rightFunc [HasColimitsOfShape J T] :
    PreservesColimitsOfShape J (Arrow.rightFunc : _ ⥤ T) := by
  apply Comma.preservesColimitsOfShape_snd

end Arrow

namespace StructuredArrow

variable {X : T} {G : A ⥤ T} (F : J ⥤ StructuredArrow X G)

/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [G.Faithful] [G.Full] {Y : A} : HasInitial (StructuredArrow (G.obj Y) G) :=
  StructuredArrow.mkIdInitial.hasInitial

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.StructuredArrow.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.StructuredArrow`。
形式化陈述：hasLimit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G
) G] : HasLimit F
参数：F ⋙ proj X G；F ⋙ proj X G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfSizeDiscretePUnit`：CategoryTheory.L
imits.HasLimitsOfSize.{v', v, u_1, u_1} (CategoryTheory.Discrete PUnit.{u_1 + 1}
)
-/
instance hasLimit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G] :
    HasLimit F := by
  have : HasLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) := i₁
  have : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) _ := i₂
  apply Comma.hasLimit
/-
**CategoryTheory.StructuredArrow.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.StructuredArrow`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] {A : Type u₁} [i
nst_1 : CategoryTheory.Category.{v₁, u₁} A]   {T : Type u₃} [inst_2 : CategoryTh
eory.Category.{v₃, u₃} T] {X : T} {G : CategoryTheory.Functor A T}   [CategoryTh
eory.Limits.HasLimitsOfShape J A] [CategoryTheory.Limits.PreservesLimitsOfShape 
J G],   CategoryTheory.Limits.HasLimitsOfShape J (CategoryTheory.StructuredArrow
 X G)
参数：CategoryTheory.StructuredArrow X G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance hasLimitsOfShape [HasLimitsOfShape J A] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) where
/-
**CategoryTheory.StructuredArrow.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.StructuredArrow`。
形式化陈述：hasFiniteLimits [HasFiniteLimits A] [PreservesFiniteLimits G] : HasFiniteL
imits (StructuredArrow X G) where out _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.hasLimitsOfShape`：∀ {J : Type w} [inst : 
CategoryTheory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Catego
ry.{v₁, u₁} A]   {T : Type u₃} [inst_…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasFiniteLimits [HasFiniteLimits A] [PreservesFiniteLimits G] :
    HasFiniteLimits (StructuredArrow X G) where
      out _ _ _ := inferInstance
/-
**CategoryTheory.StructuredArrow.hasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.StructuredArrow`。
形式化陈述：hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'}
 G] : HasLimitsOfSize.{w, w'} (StructuredArrow X G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.hasLimitsOfShape`：∀ {J : Type w} [inst : 
CategoryTheory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Catego
ry.{v₁, u₁} A]   {T : Type u₃} [inst_…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'} G] :
    HasLimitsOfSize.{w, w'} (StructuredArrow X G) :=
  ⟨fun J hJ => by infer_instance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.StructuredArrow.createsLimit** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.StructuredArrow`。
形式化陈述：createsLimit [i : PreservesLimit (F ⋙ proj X G) G] : CreatesLimit F (proj 
X G)
参数：F ⋙ proj X G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance createsLimit [i : PreservesLimit (F ⋙ proj X G) G] :
    CreatesLimit F (proj X G) :=
  letI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) G := i
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := Comma.coneOfPreserves F punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm }
/-
**CategoryTheory.StructuredArrow.createsLimitsOfShape** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.StructuredArrow`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.Category.{w', w} J] →     {A : Typ
e u₁} →       [inst_1 : CategoryTheory.Category.{v₁, u₁} A] →         {T : Type 
u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} T] →             {X :
 T} →               {G : CategoryTheory.Functor A T} →                 [Category
Theory.Limits.PreservesLimitsOfShape J G] →                   CategoryTheory.Cre
atesLimitsOfShape J (CategoryTheory.StructuredArrow.proj X G)
参数：CategoryTheory.StructuredArrow.proj X G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (proj X G) where
/-
**CategoryTheory.StructuredArrow.createsFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.StructuredArrow`。
形式化陈述：createsFiniteLimits [PreservesFiniteLimits G] : CreatesFiniteLimits (proj 
X G) where createsFiniteLimits _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable instance createsFiniteLimits [PreservesFiniteLimits G] :
    CreatesFiniteLimits (proj X G) where
      createsFiniteLimits _ _ _ := inferInstance
/-
**CategoryTheory.StructuredArrow.createsLimitsOfSize** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.StructuredArrow`。
形式化陈述：{A : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} A] →     {T : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} T] →         {X : T} 
→           {G : CategoryTheory.Functor A T} →             [CategoryTheory.Limit
s.PreservesLimitsOfSize.{w, w', v₁, v₃, u₁, u₃} G] →               CategoryTheor
y.CreatesLimitsOfSize.{w, w', v₁, v₁, max u₁ v₃, u₁}                 (CategoryTh
eory.StructuredArrow.proj X G)
参数：CategoryTheory.StructuredArrow.proj X G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable instance createsLimitsOfSize [PreservesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (proj X G :) where
/-
**CategoryTheory.StructuredArrow.mono_right_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.StructuredArrow`。
形式化陈述：mono_right_of_mono [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan 
G] {Y Z : StructuredArrow X G} (f : Y ⟶ Z) [Mono f] : Mono f.right
参数：f : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimi
tsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance mono_right_of_mono [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) [Mono f] : Mono f.right :=
  show Mono ((proj X G).map f) from inferInstance
/-
**CategoryTheory.StructuredArrow.mono_iff_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.StructuredArrow`。
形式化陈述：mono_iff_mono_right [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan
 G] {Y Z : StructuredArrow X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.right
参数：f : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.mono_of_mono_right`：mono_of_mono_right {A
 B : StructuredArrow S T} (f : A ⟶ B) [h : Mono f.right] : Mono f
-/
theorem mono_iff_mono_right [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.right :=
  ⟨fun _ => inferInstance, fun _ => mono_of_mono_right f⟩

end StructuredArrow

namespace CostructuredArrow

variable {G : A ⥤ T} {X : T} (F : J ⥤ CostructuredArrow G X)

/-
**CategoryTheory.CostructuredArrow.hasTerminal** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.CostructuredArrow`。
形式化陈述：hasTerminal [G.Faithful] [G.Full] {Y : A} : HasTerminal (CostructuredArrow
 G (G.obj Y))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
-/
instance hasTerminal [G.Faithful] [G.Full] {Y : A} :
    HasTerminal (CostructuredArrow G (G.obj Y)) :=
  CostructuredArrow.mkIdTerminal.hasTerminal

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CostructuredArrow.hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.CostructuredArrow`。
形式化陈述：hasColimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ pr
oj G X) G] : HasColimit F
参数：F ⋙ proj G X；F ⋙ proj G X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfSizeDiscretePUnit`：CategoryTheory
.Limits.HasColimitsOfSize.{v', v, u_1, u_1} (CategoryTheory.Discrete PUnit.{u_1 
+ 1})
-/
instance hasColimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G] :
    HasColimit F := by
  have : HasColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) := i₁
  have : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) _ := i₂
  apply Comma.hasColimit
/-
**CategoryTheory.CostructuredArrow.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] {A : Type u₁} [i
nst_1 : CategoryTheory.Category.{v₁, u₁} A]   {T : Type u₃} [inst_2 : CategoryTh
eory.Category.{v₃, u₃} T] {G : CategoryTheory.Functor A T} {X : T}   [CategoryTh
eory.Limits.HasColimitsOfShape J A] [CategoryTheory.Limits.PreservesColimitsOfSh
ape J G],   CategoryTheory.Limits.HasColimitsOfShape J (CategoryTheory.Costructu
redArrow G X)
参数：CategoryTheory.CostructuredArrow G X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
instance hasColimitsOfShape [HasColimitsOfShape J A] [PreservesColimitsOfShape J G] :
    HasColimitsOfShape J (CostructuredArrow G X) where
/-
**CategoryTheory.CostructuredArrow.hasFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.CostructuredArrow`。
形式化陈述：hasFiniteColimits [HasFiniteColimits A] [PreservesFiniteColimits G] : HasF
initeColimits (CostructuredArrow G X) where out _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.hasColimitsOfShape`：∀ {J : Type w} [ins
t : CategoryTheory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} A]   {T : Type u₃} [inst_…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasFiniteColimits [HasFiniteColimits A] [PreservesFiniteColimits G] :
    HasFiniteColimits (CostructuredArrow G X) where
      out _ _ _ := inferInstance
/-
**CategoryTheory.CostructuredArrow.hasColimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.CostructuredArrow`。
形式化陈述：hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{
w, w'} G] : HasColimitsOfSize.{w, w'} (CostructuredArrow G X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.hasColimitsOfShape`：∀ {J : Type w} [ins
t : CategoryTheory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} A]   {T : Type u₃} [inst_…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{w, w'} G] :
    HasColimitsOfSize.{w, w'} (CostructuredArrow G X) :=
  ⟨fun _ _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CostructuredArrow.createsColimit** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.CostructuredArrow`。
形式化陈述：createsColimit [i : PreservesColimit (F ⋙ proj G X) G] : CreatesColimit F 
(proj G X)
参数：F ⋙ proj G X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance createsColimit [i : PreservesColimit (F ⋙ proj G X) G] :
    CreatesColimit F (proj G X) :=
  letI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) G := i
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Comma.coconeOfPreserves F t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocone.ext (Iso.refl _) fun _ => comp_id _ }
/-
**CategoryTheory.CostructuredArrow.createsColimitsOfShape** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.Category.{w', w} J] →     {A : Typ
e u₁} →       [inst_1 : CategoryTheory.Category.{v₁, u₁} A] →         {T : Type 
u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} T] →             {G :
 CategoryTheory.Functor A T} →               {X : T} →                 [Category
Theory.Limits.PreservesColimitsOfShape J G] →                   CategoryTheory.C
reatesColimitsOfShape J (CategoryTheory.CostructuredArrow.proj G X)
参数：CategoryTheory.CostructuredArrow.proj G X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance createsColimitsOfShape [PreservesColimitsOfShape J G] :
    CreatesColimitsOfShape J (proj G X) where
/-
**CategoryTheory.CostructuredArrow.createsFiniteColimits** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：createsFiniteColimits [PreservesFiniteColimits G] : CreatesFiniteColimits 
(proj G X) where createsFiniteColimits _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable instance createsFiniteColimits [PreservesFiniteColimits G] :
    CreatesFiniteColimits (proj G X) where
      createsFiniteColimits _ _ _ := inferInstance
/-
**CategoryTheory.CostructuredArrow.createsColimitsOfSize** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：{A : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} A] →     {T : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} T] →         {G : Cat
egoryTheory.Functor A T} →           {X : T} →             [CategoryTheory.Limit
s.PreservesColimitsOfSize.{w, w', v₁, v₃, u₁, u₃} G] →               CategoryThe
ory.CreatesColimitsOfSize.{w, w', v₁, v₁, max u₁ v₃, u₁}                 (Catego
ryTheory.CostructuredArrow.proj G X)
参数：CategoryTheory.CostructuredArrow.proj G X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable instance createsColimitsOfSize [PreservesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (proj G X :) where
/-
**CategoryTheory.CostructuredArrow.epi_left_of_epi** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.CostructuredArrow`。
形式化陈述：epi_left_of_epi [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G] {
Y Z : CostructuredArrow G X} (f : Y ⟶ Z) [Epi f] : Epi f.left
参数：f : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
instance epi_left_of_epi [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) [Epi f] : Epi f.left :=
  show Epi ((proj G X).map f) from inferInstance
/-
**CategoryTheory.CostructuredArrow.epi_iff_epi_left** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.CostructuredArrow`。
形式化陈述：epi_iff_epi_left [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G] 
{Y Z : CostructuredArrow G X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left
参数：f : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.epi_of_epi_left`：epi_of_epi_left {A B :
 CostructuredArrow S T} (f : A ⟶ B) [h : Epi f.left] : Epi f
-/
theorem epi_iff_epi_left [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left :=
  ⟨fun _ => inferInstance, fun _ => epi_of_epi_left f⟩

end CostructuredArrow

namespace Over

/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : T} : HasTerminal (Over X) := CostructuredArrow.hasTerminal

end Over

namespace Under

/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : T} : HasInitial (Under X) := Under.mkIdInitial.hasInitial

end Under

end CategoryTheory

