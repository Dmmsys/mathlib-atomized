/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-!
# Equalizers and coequalizers in `C` and `Cᵒᵖ`

We construct equalizers and coequalizers in the opposite categories.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

/-
**CategoryTheory.Limits.hasEqualizers_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasEqualizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
-/
instance hasEqualizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ :=
  haveI : HasColimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasLimitsOfShape_op_of_hasColimitsOfShape
/-
**CategoryTheory.Limits.hasCoequalizers_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasCoequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
instance hasCoequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ :=
  haveI : HasLimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasColimitsOfShape_op_of_hasLimitsOfShape

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `parallelPair f.op g.op` and `(parallelPair f g).op` -/
/-
**CategoryTheory.Limits.parallelPairOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：parallelPairOpIso {X Y : C} (f g : X ⟶ Y) : parallelPair f.op g.op ≅ walki
ngParallelPairOpEquiv.functor ⋙ (parallelPair f g).op
参数：f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `parallelPair f.op g.op` and `(parallelPair f
 g).op`
-/
def parallelPairOpIso {X Y : C} (f g : X ⟶ Y) :
    parallelPair f.op g.op ≅ walkingParallelPairOpEquiv.functor ⋙ (parallelPair f g).op :=
  NatIso.ofComponents (fun
    | .zero => .refl _
    | .one => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

@[simp]
/-
**CategoryTheory.Limits.parallelPairOpIso_hom_app_zero** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：parallelPairOpIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) : (parallelPairOpIs
o f g).hom.app WalkingParallelPair.zero = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma parallelPairOpIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).hom.app WalkingParallelPair.zero = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPairOpIso_hom_app_one** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：parallelPairOpIso_hom_app_one {X Y : C} (f g : X ⟶ Y) : (parallelPairOpIso
 f g).hom.app WalkingParallelPair.one = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma parallelPairOpIso_hom_app_one {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).hom.app WalkingParallelPair.one = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPairOpIso_inv_app_zero** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：parallelPairOpIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) : (parallelPairOpIs
o f g).inv.app WalkingParallelPair.zero = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma parallelPairOpIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).inv.app WalkingParallelPair.zero = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPairOpIso_inv_app_one** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：parallelPairOpIso_inv_app_one {X Y : C} (f g : X ⟶ Y) : (parallelPairOpIso
 f g).inv.app WalkingParallelPair.one = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma parallelPairOpIso_inv_app_one {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).inv.app WalkingParallelPair.one = 𝟙 _ := rfl

/-- The canonical isomorphism relating `(parallelPair f g).op` and `parallelPair f.op g.op` -/
/-
**CategoryTheory.Limits.opParallelPairIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：opParallelPairIso {X Y : C} (f g : X ⟶ Y) : (parallelPair f g).op ≅ walkin
gParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op
参数：f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `(parallelPair f g).op` and `parallelPair f.o
p g.op`
-/
def opParallelPairIso {X Y : C} (f g : X ⟶ Y) :
    (parallelPair f g).op ≅ walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op :=
  calc
    (parallelPair f g).op ≅ 𝟭 _ ⋙ (parallelPair f g).op := .refl _
    _ ≅ (walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor) ⋙ _ :=
      isoWhiskerRight walkingParallelPairOpEquiv.symm.unitIso _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor ⋙ _ :=
      Functor.associator _ _ _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op :=
      isoWhiskerLeft _ (parallelPairOpIso f g).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.opParallelPairIso_hom_app_zero** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：opParallelPairIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) : (opParallelPairIs
o f g).hom.app (op WalkingParallelPair.zero) = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opParallelPairIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).hom.app (op WalkingParallelPair.zero) = 𝟙 _ := by
  simp [opParallelPairIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.opParallelPairIso_hom_app_one** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：opParallelPairIso_hom_app_one {X Y : C} (f g : X ⟶ Y) : (opParallelPairIso
 f g).hom.app (op WalkingParallelPair.one) = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opParallelPairIso_hom_app_one {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).hom.app (op WalkingParallelPair.one) = 𝟙 _ := by
  simp [opParallelPairIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.opParallelPairIso_inv_app_zero** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：opParallelPairIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) : (opParallelPairIs
o f g).inv.app (op WalkingParallelPair.zero) = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opParallelPairIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).inv.app (op WalkingParallelPair.zero) = 𝟙 _ := by
  simp [opParallelPairIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.opParallelPairIso_inv_app_one** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：opParallelPairIso_inv_app_one {X Y : C} (f g : X ⟶ Y) : (opParallelPairIso
 f g).inv.app (op WalkingParallelPair.one) = 𝟙 _
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opParallelPairIso_inv_app_one {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).inv.app (op WalkingParallelPair.one) = 𝟙 _ := by
  simp [opParallelPairIso]

namespace Cofork

/-- The obvious map `Cofork f g → Fork f.unop g.unop` -/
/-
**CategoryTheory.Limits.Cofork.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Cofork`。
形式化陈述：unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.unop g.unop
参数：c : Cofork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `Cofork f g → Fork f.unop g.unop`
-/
def unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.unop g.unop :=
  Cocone.unop ((Cocone.precompose (opParallelPairIso f.unop g.unop).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.inverse c))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Cofork.unop_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_π_app_one {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.π.app .one = Quiver.Hom.unop (c.ι.app .zero) := by
  simp [unop]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Cofork.unop_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_π_app_zero {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.π.app .zero = Quiver.Hom.unop (c.ι.app .one) := by
  simp [unop]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Cofork.unop_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_ι {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.ι = c.π.unop := by simp [Cofork.unop, Fork.ι]

/-- The obvious map `Cofork f g → Fork f.op g.op` -/
/-
**CategoryTheory.Limits.Cofork.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Cofork`。
形式化陈述：op {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.op g.op
参数：c : Cofork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `Cofork f g → Fork f.op g.op`
-/
def op {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.op g.op :=
  (Cone.postcompose (parallelPairOpIso f g).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.functor (Cocone.op c))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Cofork.op_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_π_app_one {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.π.app .one = Quiver.Hom.op (c.ι.app .zero) := by
  simp [op]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Cofork.op_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_π_app_zero {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.π.app .zero = Quiver.Hom.op (c.ι.app .one) := by
  simp [op]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Cofork.op_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_ι {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.ι = c.π.op := by simp [Cofork.op, Fork.ι]

end Cofork

namespace Fork

/-- The obvious map `Fork f g → Cofork f.unop g.unop` -/
/-
**CategoryTheory.Limits.Fork.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Fork`。
形式化陈述：unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.unop g.unop
参数：c : Fork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `Fork f g → Cofork f.unop g.unop`
-/
def unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.unop g.unop :=
  Cone.unop ((Cone.postcompose (opParallelPairIso f.unop g.unop).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.inverse c))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Fork.unop_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_ι_app_one {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.ι.app .one = Quiver.Hom.unop (c.π.app .zero) := by
  simp [unop]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Fork.unop_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_ι_app_zero {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.ι.app .zero = Quiver.Hom.unop (c.π.app .one) := by
  simp [unop]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Fork.unop_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_π {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.π = c.ι.unop := by simp [Fork.unop, Cofork.π]

/-- The obvious map `Fork f g → Cofork f.op g.op` -/
@[simps!]
/-
**CategoryTheory.Limits.Fork.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Fork`。
形式化陈述：op {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.op g.op
参数：c : Fork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `Fork f g → Cofork f.op g.op`
-/
def op {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.op g.op :=
  (Cocone.precompose (parallelPairOpIso f g).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.functor (Cone.op c))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Fork.op_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limit
s.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_ι_app_one {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.ι.app .one = Quiver.Hom.op (c.π.app .zero) := by
  simp [op]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Fork.op_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limit
s.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_ι_app_zero {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.ι.app .zero = Quiver.Hom.op (c.π.app .one) := by
  simp [op]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Fork.op_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_π {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.π = c.ι.op := by simp [Fork.op, Cofork.π]

end Fork

namespace Cofork

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Cofork.op_unop_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop_π {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop.π = c.π := by
  simp [Fork.unop_π, Cofork.op_ι]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Cofork.unop_op_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op_π {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op.π = c.π := by
  simp [Fork.op_π, Cofork.unop_ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a cofork, then `c.op.unop` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.Cofork.opUnopIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Cofork`。
形式化陈述：opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop ≅ c
参数：c : Cofork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a cofork, then `c.op.unop` is isomorphic to `c`.
-/
def opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop ≅ c :=
  Cofork.ext (Iso.refl _) (by simp [op_unop_π])

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a cofork in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.Cofork.unopOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Cofork`。
形式化陈述：unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op ≅ c
参数：c : Cofork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a cofork in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`.
-/
def unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op ≅ c :=
  Cofork.ext (Iso.refl _) (by simp [unop_op_π])

end Cofork

namespace Fork

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Fork.op_unop_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop_ι {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop.ι = c.ι := by
  simp [Cofork.unop_ι, Fork.op_π]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Fork.unop_op_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op_ι {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op.ι = c.ι := by
  simp [Fork.unop_π, Cofork.op_ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a fork, then `c.op.unop` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.Fork.opUnopIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Fork`。
形式化陈述：opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop ≅ c
参数：c : Fork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a fork, then `c.op.unop` is isomorphic to `c`.
-/
def opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop ≅ c :=
  Fork.ext (Iso.refl _) (by simp [op_unop_ι])

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a fork in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.Fork.unopOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Fork`。
形式化陈述：unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op ≅ c
参数：c : Fork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a fork in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`.
-/
def unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op ≅ c :=
  Fork.ext (Iso.refl _) (by simp [unop_op_ι])

end Fork

namespace Cofork

/-- A cofork is a colimit cocone if and only if the corresponding fork in the opposite category is
a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/-
**CategoryTheory.Limits.Cofork.isColimitEquivIsLimitOp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Cofork`。
形式化陈述：isColimitEquivIsLimitOp {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : IsColim
it c ≃ IsLimit c.op
参数：c : Cofork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isColimitEquivIsLimitOp {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun ((IsLimit.whiskerEquivalenceEquiv _).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun (((IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop)

/-- A cofork is a colimit cocone in `Cᵒᵖ` if and only if the corresponding fork in `C` is
a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/-
**CategoryTheory.Limits.Cofork.isColimitEquivIsLimitUnop** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.Cofork`。
形式化陈述：isColimitEquivIsLimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : IsC
olimit c ≃ IsLimit c.unop
参数：c : Cofork f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isColimitEquivIsLimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun ((IsColimit.whiskerEquivalenceEquiv _).toFun h.op))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `(Cofork.ofπ π w).op` and `Fork.ofι π.op w'`. -/
/-
**CategoryTheory.Limits.Cofork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between `(Cofork.ofπ π w).op` and `Fork.ofι π.op w'`.
-/
def ofπOpIsoOfι {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.op ≫ f.op = π'.op ≫ g.op) (h : π = π') :
    (Cofork.ofπ π w).op ≅ Fork.ofι π'.op w' :=
  Fork.ext (Iso.refl _) (by simp [Cofork.op_ι, h])

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `(Cofork.ofπ π w).unop` and `Fork.ofι π.unop w'`. -/
/-
**CategoryTheory.Limits.Cofork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between `(Cofork.ofπ π w).unop` and `Fork.ofι π.unop w
'`.
-/
def ofπUnopIsoOfι {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.unop ≫ f.unop = π'.unop ≫ g.unop) (h : π = π') :
    (Cofork.ofπ π w).unop ≅ Fork.ofι π'.unop w' :=
  Fork.ext (Iso.refl _) (by simp [Cofork.unop_ι, h])

/-- `Cofork.ofπ π w` is a colimit cocone if and only if `Fork.ofι π.op w'` in the opposite
category is a limit cone. -/
/-
**CategoryTheory.Limits.Cofork.isColimitOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cofork.ofπ π w` is a colimit cocone if and only if `Fork.ofι π.op w'` in the op
posite
category is a limit cone.
-/
def isColimitOfπEquivIsLimitOp {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.op ≫ f.op = π'.op ≫ g.op) (h : π = π') :
    IsColimit (Cofork.ofπ π w) ≃ IsLimit (Fork.ofι π'.op w') :=
  (Cofork.ofπ π w).isColimitEquivIsLimitOp.trans (IsLimit.equivIsoLimit (ofπOpIsoOfι π π' w w' h))

/-- `Cofork.ofπ π w` is a colimit cocone in `Cᵒᵖ` if and only if `Fork.ofι π'.unop w'` in `C` is
a limit cone. -/
/-
**CategoryTheory.Limits.Cofork.isColimitOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cofork.ofπ π w` is a colimit cocone in `Cᵒᵖ` if and only if `Fork.ofι π'.unop w
'` in `C` is
a limit cone.
-/
def isColimitOfπEquivIsLimitUnop {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.unop ≫ f.unop = π'.unop ≫ g.unop) (h : π = π') :
    IsColimit (Cofork.ofπ π w) ≃ IsLimit (Fork.ofι π'.unop w') :=
  (Cofork.ofπ π w).isColimitEquivIsLimitUnop.trans
    (IsLimit.equivIsoLimit (ofπUnopIsoOfι π π' w w' h))

end Cofork

namespace Fork

/-- A fork is a limit cone if and only if the corresponding cofork in the opposite category is
a colimit cocone. -/
/-
**CategoryTheory.Limits.Fork.isLimitEquivIsColimitOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Fork`。
形式化陈述：isLimitEquivIsColimitOp {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : IsLimit c
 ≃ IsColimit c.op
参数：c : Fork f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A fork is a limit cone if and only if the corresponding cofork in the opposite c
ategory is
a colimit cocone.
-/
def isLimitEquivIsColimitOp {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/-- A fork is a limit cone in `Cᵒᵖ` if and only if the corresponding cofork in `C` is
a colimit cocone. -/
/-
**CategoryTheory.Limits.Fork.isLimitEquivIsColimitUnop** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.Fork`。
形式化陈述：isLimitEquivIsColimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : IsLim
it c ≃ IsColimit c.unop
参数：c : Fork f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A fork is a limit cone in `Cᵒᵖ` if and only if the corresponding cofork in `C` i
s
a colimit cocone.
-/
def isLimitEquivIsColimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism between `(Fork.ofι ι w).op` and `Cofork.ofπ ι.op w'`. -/
/-
**CategoryTheory.Limits.Fork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between `(Fork.ofι ι w).op` and `Cofork.ofπ ι.op w'`.
-/
def ofιOpIsoOfπ {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.op ≫ ι'.op = g.op ≫ ι'.op) (h : ι = ι') :
    (Fork.ofι ι w).op ≅ Cofork.ofπ ι'.op w' :=
  Cofork.ext (Iso.refl _) (by simp [Fork.op_π, h])

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `(Fork.ofι ι w).unop` and `Cofork.ofπ ι.unop w.unop`. -/
/-
**CategoryTheory.Limits.Fork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between `(Fork.ofι ι w).unop` and `Cofork.ofπ ι.unop w
.unop`.
-/
def ofιUnopIsoOfπ {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.unop ≫ ι'.unop = g.unop ≫ ι'.unop) (h : ι = ι') :
    (Fork.ofι ι w).unop ≅ Cofork.ofπ ι'.unop w' :=
  Cofork.ext (Iso.refl _) (by simp [Fork.unop_π, h])

/-- `Fork.ofι ι w` is a limit cone if and only if `Cofork.ofπ ι'.op w'` in the opposite
category is a colimit cocone. -/
/-
**CategoryTheory.Limits.Fork.isLimitOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fork.ofι ι w` is a limit cone if and only if `Cofork.ofπ ι'.op w'` in the oppos
ite
category is a colimit cocone.
-/
def isLimitOfιEquivIsColimitOp {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.op ≫ ι'.op = g.op ≫ ι'.op) (h : ι = ι') :
    IsLimit (Fork.ofι ι w) ≃ IsColimit (Cofork.ofπ ι'.op w') :=
  (Fork.ofι ι w).isLimitEquivIsColimitOp.trans (IsColimit.equivIsoColimit (ofιOpIsoOfπ ι ι' w w' h))

/-- `Fork.ofι ι w` is a limit cone in `Cᵒᵖ` if and only if `Cofork.ofπ ι.unop w.unop` in `C` is
a colimit cocone. -/
/-
**CategoryTheory.Limits.Fork.isLimitOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Fork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fork.ofι ι w` is a limit cone in `Cᵒᵖ` if and only if `Cofork.ofπ ι.unop w.unop
` in `C` is
a colimit cocone.
-/
def isLimitOfιEquivIsColimitUnop {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.unop ≫ ι'.unop = g.unop ≫ ι'.unop) (h : ι = ι') :
    IsLimit (Fork.ofι ι w) ≃ IsColimit (Cofork.ofπ ι'.unop w') :=
  (Fork.ofι ι w).isLimitEquivIsColimitUnop.trans
    (IsColimit.equivIsoColimit (ofιUnopIsoOfπ ι ι' w w' h))

end Fork

namespace Cofork

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Cofork.ofπ f pullback.condition` is a colimit cocone if and only if
`Fork.ofι f.op pushout.condition` in the opposite category is a limit cone. -/
/-
**CategoryTheory.Limits.Cofork.isColimitCoforkPushoutEquivIsColimitForkOpPullbac
k** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Cofork`。
形式化陈述：isColimitCoforkPushoutEquivIsColimitForkOpPullback {X Y : C} {f : X ⟶ Y} [
HasPullback f f] : IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.o
fι f.op pushout.condition) where toFun h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…

--- 原说明 ---
`Cofork.ofπ f pullback.condition` is a colimit cocone if and only if
`Fork.ofι f.op pushout.condition` in the opposite category is a limit cone.
-/
def isColimitCoforkPushoutEquivIsColimitForkOpPullback
    {X Y : C} {f : X ⟶ Y} [HasPullback f f] :
    IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.ofι f.op pushout.condition) where
  toFun h := Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f f
    pullback.condition (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoUnopPushout f f).op.symm (.refl _)
        (by simp [← op_comp]) (by simp [← op_comp]) (by simp)
  invFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f.op f.op
    pushout.condition (by rw [← unop_comp, ← unop_comp, pushout.condition]) rfl h) _
      (pullbackIsoUnopPushout f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Cofork.ofπ f pullback.condition` is a colimit cocone in `Cᵒᵖ` if and only if
`Fork.ofι f.unop pushout.condition` in `C` is a limit cone. -/
/-
**CategoryTheory.Limits.Cofork.isColimitCoforkPushoutEquivIsColimitForkUnopPullb
ack** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Cofork`。
形式化陈述：isColimitCoforkPushoutEquivIsColimitForkUnopPullback {X Y : Cᵒᵖ} {f : X ⟶ 
Y} [HasPullback f f] : IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fo
rk.ofι f.unop pushout.condition) where toFun h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…

--- 原说明 ---
`Cofork.ofπ f pullback.condition` is a colimit cocone in `Cᵒᵖ` if and only if
`Fork.ofι f.unop pushout.condition` in `C` is a limit cone.
-/
def isColimitCoforkPushoutEquivIsColimitForkUnopPullback
    {X Y : Cᵒᵖ} {f : X ⟶ Y} [HasPullback f f] :
    IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.ofι f.unop pushout.condition) where
  toFun h := Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f f pullback.condition
    (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoOpPushout f f).unop.symm (.refl _)
        (by simp [← unop_comp]) (by simp [← unop_comp]) (by simp)
  invFun h :=
    Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f.unop f.unop pushout.condition
      (by rw [← op_comp, ← op_comp, pushout.condition]) rfl h) _
        (pullbackIsoOpPushout f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  left_inv := by cat_disch
  right_inv := by cat_disch

end Cofork

namespace Fork

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Fork.ofι f pushout.condition` is a limit cone if and only if
`Cofork.ofπ f.op pullback.condition` in the opposite category is a colimit cocone. -/
/-
**CategoryTheory.Limits.Fork.isLimitForkPushoutEquivIsColimitForkOpPullback** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Fork`。
形式化陈述：isLimitForkPushoutEquivIsColimitForkOpPullback {X Y : C} {f : X ⟶ Y} [HasP
ushout f f] : IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.o
p pullback.condition) where toFun h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…

--- 原说明 ---
`Fork.ofι f pushout.condition` is a limit cone if and only if
`Cofork.ofπ f.op pullback.condition` in the opposite category is a colimit cocon
e.
-/
def isLimitForkPushoutEquivIsColimitForkOpPullback
    {X Y : C} {f : X ⟶ Y} [HasPushout f f] :
    IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.op pullback.condition) where
  toFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f f
    pushout.condition (by simp only [← op_comp, pushout.condition]) rfl h) _
      ((pushoutIsoUnopPullback f f).op.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f.op f.op
      pullback.condition (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
        ((pushoutIsoUnopPullback f f).symm) (.refl _) ?_ ?_ (by simp)
    · rw [Iso.symm_hom, ← Quiver.Hom.unop_op (pushoutIsoUnopPullback f f).inv, ← unop_comp,
        pushoutIsoUnopPullback_inv_fst, Quiver.Hom.unop_op, Iso.refl_hom, Category.id_comp]
    · rw [Iso.symm_hom, ← Quiver.Hom.unop_op (pushoutIsoUnopPullback f f).inv, ← unop_comp,
        pushoutIsoUnopPullback_inv_snd, Quiver.Hom.unop_op, Iso.refl_hom, Category.id_comp]
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Fork.ofι f pushout.condition` is a limit cone in `Cᵒᵖ` if and only if
`Cofork.ofπ f.op pullback.condition` in `C` is a colimit cocone. -/
/-
**CategoryTheory.Limits.Fork.isLimitForkPushoutEquivIsColimitForkUnopPullback** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.Fork`。
形式化陈述：isLimitForkPushoutEquivIsColimitForkUnopPullback {X Y : Cᵒᵖ} {f : X ⟶ Y} [
HasPushout f f] : IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ
 f.unop pullback.condition) where toFun h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …

--- 原说明 ---
`Fork.ofι f pushout.condition` is a limit cone in `Cᵒᵖ` if and only if
`Cofork.ofπ f.op pullback.condition` in `C` is a colimit cocone.
-/
def isLimitForkPushoutEquivIsColimitForkUnopPullback
    {X Y : Cᵒᵖ} {f : X ⟶ Y} [HasPushout f f] :
    IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.unop pullback.condition) where
  toFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f f pushout.condition
    (by simp only [← unop_comp, pushout.condition]) rfl h) _
      ((pushoutIsoOpPullback f f).unop.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f.unop f.unop pullback.condition
      (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
        ((pushoutIsoOpPullback f f).symm) (.refl _) ?_ ?_ (by simp)
    · rw [Iso.symm_hom, ← Quiver.Hom.op_unop (pushoutIsoOpPullback f f).inv, ← op_comp,
        pushoutIsoOpPullback_inv_fst, Quiver.Hom.op_unop, Iso.refl_hom, Category.id_comp]
    · rw [Iso.symm_hom, ← Quiver.Hom.op_unop (pushoutIsoOpPullback f f).inv, ← op_comp,
        pushoutIsoOpPullback_inv_snd, Quiver.Hom.op_unop, Iso.refl_hom, Category.id_comp]
  left_inv := by cat_disch
  right_inv := by cat_disch

end Fork

end CategoryTheory.Limits

