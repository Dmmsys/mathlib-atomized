/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Weak limits

If `F : J ⥤ C` is a functor and `c : Cone F`, we say that `c` is a weak limit of `F` if
every cone over `F` admits a (not necessarily unique) morphism to `c`. In other words, a
weak limit satisfies the same "versal property" as a limit, without the uniqueness
condition. In particular, weak limits are not unique, and they are not functorial.

We set up some API for weak limits, mostly copied from that for limits, prove that any
limit cone is a weak limit cone, and that, if a limit exists, then it is a retract of any
weak limit (see `IsWeakLimit.retractOfIsLimit`).

In the files `WeakEqualizers.lean`, `WeakKernels.lean` and `WeakPullbacks.lean`, we specialize
to weak equalizers, weak kernels and weak pullbacks, and give some API for those shapes,
again inspired from the non-weak case. We prove that a category with weak equalizers and
pullbacks has weak pullbacks, and that a preadditive category has weak equalizers if and only
if it has weak kernels.

## References

* [Peter J Freyd, *Representations in Abelian categories*, p. 99][freyd1966repabelian]

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

variable {J : Type*} [Category* J] {K : Type*} [Category* K] {C : Type*}
    [Category* C] {F : Functor J C} {D : Type*} [Category* D] {G : Functor K D}

namespace CategoryTheory.Limits

/-- A cone `t` over `F` is a weak limit cone if each cone over `F` admits a
cone morphism to `t`. -/
/-
**CategoryTheory.Limits.IsWeakLimit** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：IsWeakLimit (t : Cone F) where /-- There is a morphism from any cone point
 to `t.pt` -/ lift : forall s : Cone F, s.pt ⟶ t.pt /-- The map makes the triang
le with the two natural transformations commute -/ fac : forall (s : Cone F) (j 
: J), lift s ≫ t.π.app j = s.π.app j
参数：t : Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone `t` over `F` is a weak limit cone if each cone over `F` admits a
cone morphism to `t`.
-/
structure IsWeakLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch

attribute [reassoc (attr := simp)] IsWeakLimit.fac

/--
If `F` has a limit, then it is a retract of any weak limit of `F`.
-/
/-
**CategoryTheory.Limits.IsWeakLimit.retractOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] →         {F
 : CategoryTheory.Functor J C} →           {t t' : CategoryTheory.Limits.Cone F}
 →             CategoryTheory.Limits.IsLimit t → CategoryTheory.Limits.IsWeakLim
it t' → CategoryTheory.Retract t.pt t'.pt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` has a limit, then it is a retract of any weak limit of `F`.
-/
def IsWeakLimit.retractOfIsLimit {t t' : Cone F} (l : IsLimit t) (l' : IsWeakLimit t') :
    Retract t.pt t'.pt where
  i := l'.lift t
  r := l.lift t'
  retract := l.hom_ext (fun _ ↦ by rw [assoc, id_comp, l.fac t', l'.fac t])

/--
If `c : Cone F` is a limit, then it is a weak limit.
-/
/-
**CategoryTheory.Limits.IsLimit.isWeakLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.IsLimit`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] →         {F
 : CategoryTheory.Functor J C} →           {t : CategoryTheory.Limits.Cone F} → 
CategoryTheory.Limits.IsLimit t → CategoryTheory.Limits.IsWeakLimit t
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…

--- 原说明 ---
If `c : Cone F` is a limit, then it is a weak limit.
-/
def IsLimit.isWeakLimit {t : Cone F} (l : IsLimit t) : IsWeakLimit t where
  lift := l.lift
  fac := l.fac

/-- `WeakLimitCone F` contains a cone over `F` together with the information that it is
a weak limit. -/
/-
**CategoryTheory.Limits.WeakLimitCone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] → CategoryTh
eory.Functor J C → Type (max (max u_1 u_3) v_3)
参数：max (max u_1 u_3) v_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WeakLimitCone F` contains a cone over `F` together with the information that it
 is
a weak limit.
-/
structure WeakLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the weak limit cone -/
  isWeakLimit : IsWeakLimit cone

/--
Any limit cone defines a weak limit cone with the same underlying cone over `F` and the same
lifts.
-/
/-
**CategoryTheory.Limits.WeakLimitCone.ofLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.WeakLimitCone`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] →         {F
 : CategoryTheory.Functor J C} → CategoryTheory.Limits.LimitCone F → CategoryThe
ory.Limits.WeakLimitCone F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any limit cone defines a weak limit cone with the same underlying cone over `F` 
and the same
lifts.
-/
def WeakLimitCone.ofLimitCone {F : J ⥤ C} (c : LimitCone F) : WeakLimitCone F where
  cone := c.cone
  isWeakLimit := c.isLimit.isWeakLimit

/-- `HasWeakLimit F` represents the mere existence of a weak limit for `F`. -/
/-
**CategoryTheory.Limits.HasWeakLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} → [inst_1 : CategoryTheory.Category.{v_3, u_3} C] → CategoryTheory.F
unctor J C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasWeakLimit F` represents the mere existence of a weak limit for `F`.
-/
class HasWeakLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some weak limit cone for `F` -/
  exists_weakLimitCone : Nonempty (WeakLimitCone F)

/--
If `F` has a limit, then it has a weak limit.
-/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` has a limit, then it has a weak limit.
-/
instance (F : J ⥤ C) [HasLimit F] : HasWeakLimit F where
  exists_weakLimitCone := Nonempty.intro (WeakLimitCone.ofLimitCone (getLimitCone F))
/-
**CategoryTheory.Limits.HasWeakLimit.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.HasWeakLimit`。
形式化陈述：∀ {J : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} J] {C : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} C] {F : CategoryTheory.Functo
r J C}   (d : CategoryTheory.Limits.WeakLimitCone F), CategoryTheory.Limits.HasW
eakLimit F
参数：d : CategoryTheory.Limits.WeakLimitCone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasWeakLimit.mk {F : J ⥤ C} (d : WeakLimitCone F) : HasWeakLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit F`. -/
@[no_expose]
/-
**CategoryTheory.Limits.getWeakLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F
参数：F : J ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasWeakLimit.exists_weakLimitCone`：∀ {J : Type u_1
} {inst : CategoryTheory.Category.{v_1, u_1} J} {C : Type u_3}   {inst_1 : Categ
oryTheory.Category.{v_3, u_3} C} {F : Categor…

--- 原说明 ---
Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit
 F`.
-/
def getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F :=
  Classical.choice <| HasWeakLimit.exists_weakLimitCone

variable (J C) in
/-- `C` has weak limits of shape `J` if there exists a weak limit for every functor
`F : J ⥤ C`. -/
/-
**CategoryTheory.Limits.HasWeakLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：HasWeakLimitsOfShape : Prop where /-- All functors `F : J ⥤ C` from `J` ha
ve weak limits -/ hasWeakLimit : forall F : J ⥤ C, HasWeakLimit F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has weak limits of shape `J` if there exists a weak limit for every functor
`F : J ⥤ C`.
-/
class HasWeakLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have weak limits -/
  hasWeakLimit : ∀ F : J ⥤ C, HasWeakLimit F := by infer_instance

attribute [instance] HasWeakLimitsOfShape.hasWeakLimit
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [HasLimitsOfShape J C] : HasWeakLimitsOfShape J C where

-- Interface to the `HasWeakLimit` class.
/-- An arbitrary choice of weak limit cone for a functor. -/
/-
**CategoryTheory.Limits.weakLimit.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.weakLimit`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] →         (F
 : CategoryTheory.Functor J C) → [CategoryTheory.Limits.HasWeakLimit F] → Catego
ryTheory.Limits.Cone F
参数：F : CategoryTheory.Functor J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of weak limit cone for a functor.
-/
def weakLimit.cone (F : J ⥤ C) [HasWeakLimit F] : Cone F :=
  (getWeakLimitCone F).cone

/-- An arbitrary choice of weak limit object of a functor. -/
/-
**CategoryTheory.Limits.weakLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：weakLimit (F : J ⥤ C) [HasWeakLimit F]
参数：F : J ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of weak limit object of a functor.
-/
def weakLimit (F : J ⥤ C) [HasWeakLimit F] :=
  (weakLimit.cone F).pt

/-- The projection from the weak limit object to a value of the functor. -/
/-
**CategoryTheory.Limits.weakLimit.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the weak limit object to a value of the functor.
-/
def weakLimit.π (F : J ⥤ C) [HasWeakLimit F] (j : J) : weakLimit F ⟶ F.obj j :=
  (weakLimit.cone F).π.app j

@[reassoc]
/-
**CategoryTheory.Limits.weakLimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.π_comp_eqToHom (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (hj : j = j') :
    weakLimit.π F j ≫ eqToHom (by subst hj; rfl) = weakLimit.π F j' := by
  subst hj
  simp

@[simp]
/-
**CategoryTheory.Limits.weakLimit.cone_pt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.weakLimit`。
形式化陈述：∀ {J : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} J] {C : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} C] {F : CategoryTheory.Functo
r J C}   [inst_2 : CategoryTheory.Limits.HasWeakLimit F],   (CategoryTheory.Limi
ts.weakLimit.cone F).pt = CategoryTheory.Limits.weakLimit F
参数：CategoryTheory.Limits.weakLimit.cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.cone_pt {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).pt = weakLimit F := rfl

@[simp]
/-
**CategoryTheory.Limits.weakLimit.cone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.cone_π {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).π.app = weakLimit.π _ := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.weakLimit.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits.weakLimit`。
形式化陈述：∀ {J : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} J] {C : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} C] (F : CategoryTheory.Functo
r J C)   [inst_2 : CategoryTheory.Limits.HasWeakLimit F] {j j' : J} (f : j ⟶ j')
,   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.weakLimit.π F j) (
F.map f) =     CategoryTheory.Limits.weakLimit.π F j'
参数：F : CategoryTheory.Functor J C；f : j ⟶ j'；CategoryTheory.Limits.weakLimit.π F
 j；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
-/
theorem weakLimit.w (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (f : j ⟶ j') :
    weakLimit.π F j ≫ F.map f = weakLimit.π F j' :=
  (weakLimit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `weakLimit.cone F`
is a weak limit cone. -/
/-
**CategoryTheory.Limits.weakLimit.isWeakLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.weakLimit`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] →         (F
 : CategoryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasWe
akLimit F] →             CategoryTheory.Limits.IsWeakLimit (CategoryTheory.Limit
s.weakLimit.cone F)
参数：F : CategoryTheory.Functor J C；CategoryTheory.Limits.weakLimit.cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evidence that the arbitrary choice of cone provided by `weakLimit.cone F`
is a weak limit cone.
-/
def weakLimit.isWeakLimit (F : J ⥤ C) [HasWeakLimit F] :
    IsWeakLimit (weakLimit.cone F) :=
  (getWeakLimitCone F).isWeakLimit

/-- A morphism from the cone point of any other cone to the weak limit object. -/
/-
**CategoryTheory.Limits.weakLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.weakLimit`。
形式化陈述：{J : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} J] →     {C 
: Type u_3} →       [inst_1 : CategoryTheory.Category.{v_3, u_3} C] →         (F
 : CategoryTheory.Functor J C) →           [inst_2 : CategoryTheory.Limits.HasWe
akLimit F] →             (c : CategoryTheory.Limits.Cone F) → c.pt ⟶ CategoryThe
ory.Limits.weakLimit F
参数：F : CategoryTheory.Functor J C；c : CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism from the cone point of any other cone to the weak limit object.
-/
def weakLimit.lift (F : J ⥤ C) [HasWeakLimit F] (c : Cone F) :
    c.pt ⟶ weakLimit F :=
  (weakLimit.isWeakLimit F).lift c

@[simp]
/-
**CategoryTheory.Limits.weakLimit.isWeakLimit_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.weakLimit`。
形式化陈述：∀ {J : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} J] {C : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} C] {F : CategoryTheory.Functo
r J C}   [inst_2 : CategoryTheory.Limits.HasWeakLimit F] (c : CategoryTheory.Lim
its.Cone F),   (CategoryTheory.Limits.weakLimit.isWeakLimit F).lift c = Category
Theory.Limits.weakLimit.lift F c
参数：c : CategoryTheory.Limits.Cone F；CategoryTheory.Limits.weakLimit.isWeakLimit 
F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.isWeakLimit_lift {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) :
    (weakLimit.isWeakLimit F).lift c = weakLimit.lift F c :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.weakLimit.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.lift_π {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) (j : J) :
    weakLimit.lift F c ≫ weakLimit.π F j = c.π.app j :=
  IsWeakLimit.fac _ c j

namespace IsWeakLimit

/-- Transport evidence that a cone is a weak limit cone across an isomorphism of cones. -/
@[simps]
/-
**CategoryTheory.Limits.IsWeakLimit.ofIsoWeakLimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.IsWeakLimit`。
形式化陈述：ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimi
t t where lift s
参数：P : IsWeakLimit r；i : r ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport evidence that a cone is a weak limit cone across an isomorphism of con
es.
-/
def ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimit t where
  lift s := P.lift s ≫ i.hom.hom

/-- Isomorphism of cones preserves whether or not they are weak limit cones. -/
/-
**CategoryTheory.Limits.IsWeakLimit.equivIsoWeakLimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：equivIsoWeakLimit {r t : Cone F} (i : r ≅ t) : IsWeakLimit r ≃ IsWeakLimit
 t where toFun h
参数：i : r ≅ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphism of cones preserves whether or not they are weak limit cones.
-/
def equivIsoWeakLimit {r t : Cone F} (i : r ≅ t) : IsWeakLimit r ≃ IsWeakLimit t where
  toFun h := h.ofIsoWeakLimit i
  invFun h := h.ofIsoWeakLimit i.symm
  left_inv _ := by simp [ofIsoWeakLimit]
  right_inv _ := by simp [ofIsoWeakLimit]

@[simp]
/-
**CategoryTheory.Limits.IsWeakLimit.equivIsoWeakLimit_apply** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：equivIsoWeakLimit_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit r) : e
quivIsoWeakLimit i P = P.ofIsoWeakLimit i
参数：i : r ≅ t；P : IsWeakLimit r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivIsoWeakLimit_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit r) :
    equivIsoWeakLimit i P = P.ofIsoWeakLimit i :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.IsWeakLimit.equivIsoWeakLimit_symm_apply** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：equivIsoWeakLimit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit t
) : (equivIsoWeakLimit i).symm P = P.ofIsoWeakLimit i.symm
参数：i : r ≅ t；P : IsWeakLimit t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivIsoWeakLimit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit t) :
    (equivIsoWeakLimit i).symm P = P.ofIsoWeakLimit i.symm :=
  rfl

/-- The versal morphism from any other cone to a weak limit cone. -/
@[simps]
/-
**CategoryTheory.Limits.IsWeakLimit.liftConeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：liftConeMorphism {t : Cone F} (h : IsWeakLimit t) (s : Cone F) : s ⟶ t whe
re hom
参数：h : IsWeakLimit t；s : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The versal morphism from any other cone to a weak limit cone.
-/
def liftConeMorphism {t : Cone F} (h : IsWeakLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

/-- Alternative constructor for `isWeakLimit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[simps]
/-
**CategoryTheory.Limits.IsWeakLimit.mkOfConeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：mkOfConeMorphism {t : Cone F} (lift : forall s : Cone F, s ⟶ t) : IsWeakLi
mit t where lift s
参数：lift : forall s : Cone F, s ⟶ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for `isWeakLimit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
def mkOfConeMorphism {t : Cone F} (lift : ∀ s : Cone F, s ⟶ t) : IsWeakLimit t where
  lift s := (lift s).hom

/-- Given a right adjoint functor between categories of cones,
the image of a weak limit cone is a weak limit cone.
-/
/-
**CategoryTheory.Limits.IsWeakLimit.ofRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.IsWeakLimit`。
形式化陈述：ofRightAdjoint {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F} (adj : l
eft ⊣ right) {c : Cone G} (t : IsWeakLimit c) : IsWeakLimit (right.obj c)
参数：adj : left ⊣ right；t : IsWeakLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right adjoint functor between categories of cones,
the image of a weak limit cone is a weak limit cone.
-/
def ofRightAdjoint {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsWeakLimit c) : IsWeakLimit (right.obj c) :=
  mkOfConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))

/-- Given two functors which have equivalent categories of cones, we can transport evidence of
a weak limit cone across the equivalence.
-/
/-
**CategoryTheory.Limits.IsWeakLimit.iff_of_cone_equiv** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：iff_of_cone_equiv {D : Type*} [Category* D] {G : K ⥤ D} (h : Cone G ≌ Cone
 F) {c : Cone G} : Nonempty (IsWeakLimit (h.functor.obj c)) ↔ Nonempty (IsWeakLi
mit c)
参数：h : Cone G ≌ Cone F。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functors which have equivalent categories of cones, we can transport e
vidence of
a weak limit cone across the equivalence.
-/
lemma iff_of_cone_equiv {D : Type*} [Category* D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} :
    Nonempty (IsWeakLimit (h.functor.obj c)) ↔ Nonempty (IsWeakLimit c) :=
  ⟨fun P ↦ Nonempty.intro (IsWeakLimit.ofIsoWeakLimit
    (IsWeakLimit.ofRightAdjoint h.toAdjunction P.some) (h.unitIso.symm.app c)),
   fun P ↦ Nonempty.intro (IsWeakLimit.ofRightAdjoint h.symm.toAdjunction P.some)⟩

/-- A cone postcomposed with a natural isomorphism is a weak limit cone
if and only if the original cone is.
-/
/-
**CategoryTheory.Limits.IsWeakLimit.postcompose_hom_iff_of_iso** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：postcompose_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) : Nonemp
ty (IsWeakLimit ((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWeakLimit c)
参数：α : F ≅ G；c : Cone F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.IsWeakLimit.iff_of_cone_equiv`：iff_of_cone_equiv {
D : Type*} [Category* D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} : Nonemp
ty (IsWeakLimit (h.functor.obj c)) ↔ None…

--- 原说明 ---
A cone postcomposed with a natural isomorphism is a weak limit cone
if and only if the original cone is.
-/
lemma postcompose_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) :
    Nonempty (IsWeakLimit ((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWeakLimit c) :=
  iff_of_cone_equiv (Cone.postcomposeEquivalence α)

/-- A cone postcomposed with the inverse of a natural isomorphism is a weak limit cone
if and only if the original cone is.
-/
/-
**CategoryTheory.Limits.IsWeakLimit.postcompose_inv_iff_of_iso** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：postcompose_inv_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) : Nonemp
ty (IsWeakLimit ((Cone.postcompose α.inv).obj c)) ↔ Nonempty (IsWeakLimit c)
参数：α : F ≅ G；c : Cone G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.IsWeakLimit.postcompose_hom_iff_of_iso`：postcompos
e_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) : Nonempty (IsWeakLimit 
((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWe…

--- 原说明 ---
A cone postcomposed with the inverse of a natural isomorphism is a weak limit co
ne
if and only if the original cone is.
-/
lemma postcompose_inv_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) :
    Nonempty (IsWeakLimit ((Cone.postcompose α.inv).obj c)) ↔ Nonempty (IsWeakLimit c) :=
  postcompose_hom_iff_of_iso α.symm c

/-- Constructing an equivalence between `Nonempty (IsWeakLimit c)` and `Nonempty (IsWeakLimit d)`
from a natural isomorphism between the underlying functors, and then an isomorphism between `c`
transported along this and `d`.
-/
/-
**CategoryTheory.Limits.IsWeakLimit.iff_of_natIso_of_iso** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits.IsWeakLimit`。
形式化陈述：iff_of_natIso_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G) (
w : (Cone.postcompose α.hom).obj c ≅ d) : Nonempty (IsWeakLimit c) ↔ Nonempty (I
sWeakLimit d)
参数：α : F ≅ G；c : Cone F；d : Cone G；w : (Cone.postcompose α.hom).obj c ≅ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.Limits.IsWeakLimit.postcompose_hom_iff_of_iso`：postcompos
e_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) : Nonempty (IsWeakLimit 
((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWe…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β

--- 原说明 ---
Constructing an equivalence between `Nonempty (IsWeakLimit c)` and `Nonempty (Is
WeakLimit d)`
from a natural isomorphism between the underlying functors, and then an isomorph
ism between `c`
transported along this and `d`.
-/
lemma iff_of_natIso_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
    (w : (Cone.postcompose α.hom).obj c ≅ d) :
    Nonempty (IsWeakLimit c) ↔  Nonempty (IsWeakLimit d) :=
  (postcompose_hom_iff_of_iso α _).symm.trans (IsWeakLimit.equivIsoWeakLimit w).nonempty_congr

end IsWeakLimit

/-- If a functor `F` has a weak limit, so does any naturally isomorphic functor.
-/
/-
**CategoryTheory.Limits.hasWeakLimit_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：hasWeakLimit_of_iso {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLi
mit G
参数：α : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasWeakLimit.mk`：∀ {J : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Category
.{v_3, u_3} C] {F : Categor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Limits.IsWeakLimit.postcompose_hom_iff_of_iso`：postcompos
e_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) : Nonempty (IsWeakLimit 
((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWe…

--- 原说明 ---
If a functor `F` has a weak limit, so does any naturally isomorphic functor.
-/
theorem hasWeakLimit_of_iso {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G :=
  HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit :=
        Nonempty.some ((IsWeakLimit.postcompose_hom_iff_of_iso α _ ).mpr
        (Nonempty.intro (weakLimit.isWeakLimit F))) }
/-
**CategoryTheory.Limits.hasWeakLimit_iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasWeakLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasWeakLimit F ↔ HasWe
akLimit G
参数：α : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasWeakLimit_of_iso`：hasWeakLimit_of_iso {F G : J 
⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G
-/
theorem hasWeakLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasWeakLimit F ↔ HasWeakLimit G :=
  ⟨fun _ ↦ hasWeakLimit_of_iso α, fun _ ↦ hasWeakLimit_of_iso α.symm⟩

end CategoryTheory.Limits

