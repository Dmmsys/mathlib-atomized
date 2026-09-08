/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The pullback of an isomorphism

This file provides some basic results about the pullback (and pushout) of an isomorphism.

-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

section PullbackLeftIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：pullbackConeOfLeftIso : PullbackCone f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone.
-/
def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by simp

@[simp]
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso_x** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y := rfl

@[simp]
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f := rfl

@[simp]
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ := rfl
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by simp
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl
/-
**CategoryTheory.Limits.pullbackConeOfLeftIso_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ := rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
/-
**CategoryTheory.Limits.pullbackConeOfLeftIsoIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that the constructed limit cone is indeed a limit.
-/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩
/-
**CategoryTheory.Limits.hasPullback_of_left_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasPullback_of_left_iso : HasPullback f g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_left_iso

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback_snd_iso_of_left_iso** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullback_snd_iso_of_left_iso : IsIso (pullback.snd f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_of_left_iso`：hasPullback_of_left_iso :
 HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd f g) := by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullback_inv_snd_fst_of_left_isIso** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_inv_snd_fst_of_left_isIso : inv (pullback.snd f g) ≫ pullback.fst
 f g = g ≫ inv f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_of_left_iso`：hasPullback_of_left_iso :
 HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma pullback_inv_snd_fst_of_left_isIso :
    inv (pullback.snd f g) ≫ pullback.fst f g = g ≫ inv f := by
  rw [IsIso.inv_comp_eq, ← pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
/-
**CategoryTheory.Limits.pullbackConeOfRightIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pullbackConeOfRightIso : PullbackCone f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone.
-/
def pullbackConeOfRightIso : PullbackCone f g :=
  PullbackCone.mk (𝟙 _) (f ≫ inv g) <| by simp

@[simp]
/-
**CategoryTheory.Limits.pullbackConeOfRightIso_x** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X := rfl

@[simp]
/-
**CategoryTheory.Limits.pullbackConeOfRightIso_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.pullbackConeOfRightIso_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g := rfl
/-
**CategoryTheory.Limits.pullbackConeOfRightIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f := by simp
/-
**CategoryTheory.Limits.pullbackConeOfRightIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl
/-
**CategoryTheory.Limits.pullbackConeOfRightIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
/-
**CategoryTheory.Limits.pullbackConeOfRightIsoIsLimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that the constructed limit cone is indeed a limit.
-/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩
/-
**CategoryTheory.Limits.hasPullback_of_right_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasPullback_of_right_iso : HasPullback f g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_right_iso

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback_fst_iso_of_right_iso** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pullback_fst_iso_of_right_iso : IsIso (pullback.fst f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_of_right_iso`：hasPullback_of_right_iso
 : HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
instance pullback_fst_iso_of_right_iso : IsIso (pullback.fst f g) := by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullback_inv_fst_snd_of_right_isIso** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_inv_fst_snd_of_right_isIso : inv (pullback.fst f g) ≫ pullback.sn
d f g = f ≫ inv g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_of_right_iso`：hasPullback_of_right_iso
 : HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma pullback_inv_fst_snd_of_right_isIso :
    inv (pullback.fst f g) ≫ pullback.snd f g = f ≫ inv g := by
  rw [IsIso.inv_comp_eq, pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pushoutCoconeOfLeftIso : PushoutCocone f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone.
-/
def pushoutCoconeOfLeftIso : PushoutCocone f g :=
  PushoutCocone.mk (inv f ≫ g) (𝟙 _) <| by simp

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso_x** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z := rfl

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso_inl** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g := rfl

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso_inr** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ := rfl
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfLeftIso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g := by
  simp

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfLeftIso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIso_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfLeftIso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
/-
**CategoryTheory.Limits.pushoutCoconeOfLeftIsoIsLimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that the constructed cocone is indeed a colimit.
-/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩
/-
**CategoryTheory.Limits.hasPushout_of_left_iso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasPushout_of_left_iso : HasPushout f g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasPushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPushout_of_left_iso

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout_inr_iso_of_left_iso** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pushout_inr_iso_of_left_iso : IsIso (pushout.inr f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_of_left_iso`：hasPushout_of_left_iso : H
asPushout f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr f g) := by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushout_inl_inv_inr_of_right_isIso** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pushout_inl_inv_inr_of_right_isIso : pushout.inl f g ≫ inv (pushout.inr f 
g) = inv f ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_of_left_iso`：hasPushout_of_left_iso : H
asPushout f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `CategoryTheory.Limits.pushout.condition_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : 
CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma pushout_inl_inv_inr_of_right_isIso :
    pushout.inl f g ≫ inv (pushout.inr f g) = inv f ≫ g := by
  rw [IsIso.eq_inv_comp, pushout.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso g]

/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：pushoutCoconeOfRightIso : PushoutCocone f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone.
-/
def pushoutCoconeOfRightIso : PushoutCocone f g :=
  PushoutCocone.mk (𝟙 _) (inv g ≫ f) <| by simp

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso_x** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y := rfl

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso_inl** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso_inr** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ 
f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f := rfl
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfRightIso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f := by
  simp

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfRightIso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIso_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCoconeOfRightIso_ι_app_right :
    (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
/-
**CategoryTheory.Limits.pushoutCoconeOfRightIsoIsLimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that the constructed cocone is indeed a colimit.
-/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩
/-
**CategoryTheory.Limits.hasPushout_of_right_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasPushout_of_right_iso : HasPushout f g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasPushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPushout_of_right_iso

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout_inl_iso_of_right_iso** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pushout_inl_iso_of_right_iso : IsIso (pushout.inl _ _ : _ ⟶ pushout f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_of_right_iso`：hasPushout_of_right_iso :
 HasPushout f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
-/
instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl _ _ : _ ⟶ pushout f g) := by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp
  · simp [pushout.condition]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushout_inr_inv_inl_of_right_isIso** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pushout_inr_inv_inl_of_right_isIso : pushout.inr f g ≫ inv (pushout.inl f 
g) = inv g ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_of_right_iso`：hasPushout_of_right_iso :
 HasPushout f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pushout.condition_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : 
CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma pushout_inr_inv_inl_of_right_isIso :
    pushout.inr f g ≫ inv (pushout.inl f g) = inv g ≫ f := by
  rw [IsIso.eq_inv_comp, ← pushout.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PushoutRightIso


end CategoryTheory.Limits

