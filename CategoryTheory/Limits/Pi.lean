/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ Pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ Pi.eval C i`, we can produce a
   `HasLimit F` instance
-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.pi

universe v₁ v₂ u₁ u₂

variable {I : Type v₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
variable {J : Type v₁} [SmallCategory J]
variable {F : J ⥤ ∀ i, C i}

/-- A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙ Pi.eval C i`.
-/
/-
**CategoryTheory.pi.coneCompEval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.pi`。
形式化陈述：coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval C i) where pt
参数：c : Cone F；i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙
 Pi.eval C i`.
-/
def coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

/--
A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the `F ⋙ Pi.eval C i`.
-/
/-
**CategoryTheory.pi.coconeCompEval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.pi`
。
形式化陈述：coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ Pi.eval C i) where pt
参数：c : Cocone F；i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the 
`F ⋙ Pi.eval C i`.
-/
def coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

/--
Given a family of cones over the `F ⋙ Pi.eval C i`, we can assemble these together as a `Cone F`.
-/
/-
**CategoryTheory.pi.coneOfConeCompEval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.pi`。
形式化陈述：coneOfConeCompEval (c : forall i, Cone (F ⋙ Pi.eval C i)) : Cone F where p
t i
参数：c : forall i, Cone (F ⋙ Pi.eval C i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of cones over the `F ⋙ Pi.eval C i`, we can assemble these togeth
er as a `Cone F`.
-/
def coneOfConeCompEval (c : ∀ i, Cone (F ⋙ Pi.eval C i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).π.naturality f }

/-- Given a family of cocones over the `F ⋙ Pi.eval C i`,
we can assemble these together as a `Cocone F`.
-/
/-
**CategoryTheory.pi.coconeOfCoconeCompEval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.pi`。
形式化陈述：coconeOfCoconeCompEval (c : forall i, Cocone (F ⋙ Pi.eval C i)) : Cocone F
 where pt i
参数：c : forall i, Cocone (F ⋙ Pi.eval C i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of cocones over the `F ⋙ Pi.eval C i`,
we can assemble these together as a `Cocone F`.
-/
def coconeOfCoconeCompEval (c : ∀ i, Cocone (F ⋙ Pi.eval C i)) : Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).ι.naturality f }

/-- Given a family of limit cones over the `F ⋙ Pi.eval C i`,
assembling them together as a `Cone F` produces a limit cone.
-/
/-
**CategoryTheory.pi.coneOfConeEvalIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.pi`。
形式化陈述：coneOfConeEvalIsLimit {c : forall i, Cone (F ⋙ Pi.eval C i)} (P : forall i
, IsLimit (c i)) : IsLimit (coneOfConeCompEval c) where lift s i
参数：F ⋙ Pi.eval C i；P : forall i, IsLimit (c i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of limit cones over the `F ⋙ Pi.eval C i`,
assembling them together as a `Cone F` produces a limit cone.
-/
def coneOfConeEvalIsLimit {c : ∀ i, Cone (F ⋙ Pi.eval C i)} (P : ∀ i, IsLimit (c i)) :
    IsLimit (coneOfConeCompEval c) where
  lift s i := (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coneCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i

/-- Given a family of colimit cocones over the `F ⋙ Pi.eval C i`,
assembling them together as a `Cocone F` produces a colimit cocone.
-/
/-
**CategoryTheory.pi.coconeOfCoconeEvalIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.pi`。
形式化陈述：coconeOfCoconeEvalIsColimit {c : forall i, Cocone (F ⋙ Pi.eval C i)} (P : 
forall i, IsColimit (c i)) : IsColimit (coconeOfCoconeCompEval c) where desc s i
参数：F ⋙ Pi.eval C i；P : forall i, IsColimit (c i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of colimit cocones over the `F ⋙ Pi.eval C i`,
assembling them together as a `Cocone F` produces a colimit cocone.
-/
def coconeOfCoconeEvalIsColimit {c : ∀ i, Cocone (F ⋙ Pi.eval C i)} (P : ∀ i, IsColimit (c i)) :
    IsColimit (coconeOfCoconeCompEval c) where
  desc s i := (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coconeCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i

section

variable [∀ i, HasLimit (F ⋙ Pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have limits for each of the `F ⋙ Pi.eval C i`,
then `F` has a limit.
-/
/-
**CategoryTheory.pi.hasLimit_of_hasLimit_comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.pi`。
形式化陈述：hasLimit_of_hasLimit_comp_eval : HasLimit F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have limits for each of the `F ⋙ Pi.eval C i`,
then `F` has a limit.
-/
theorem hasLimit_of_hasLimit_comp_eval : HasLimit F :=
  HasLimit.mk
    { cone := coneOfConeCompEval fun _ => limit.cone _
      isLimit := coneOfConeEvalIsLimit fun _ => limit.isLimit _ }

end

section

variable [∀ i, HasColimit (F ⋙ Pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and colimits exist for each of the `F ⋙ Pi.eval C i`,
there is a colimit for `F`.
-/
/-
**CategoryTheory.pi.hasColimit_of_hasColimit_comp_eval** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.pi`。
形式化陈述：hasColimit_of_hasColimit_comp_eval : HasColimit F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and colimits exist for each of the `F ⋙ Pi.eval C i`,
there is a colimit for `F`.
-/
theorem hasColimit_of_hasColimit_comp_eval : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfCoconeCompEval fun _ => colimit.cocone _
      isColimit := coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _ }

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import CategoryTheory.Limits.Types.Products`
we can use:
```
attribute [local instance] hasLimit_of_hasLimit_comp_eval
example : hasBinaryProducts (I → Type v₁) := ⟨by infer_instance⟩
```
-/


end CategoryTheory.pi

