/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Binary (co)products of type-valued functors

Defines an explicit construction of binary products and coproducts of type-valued functors.

Also defines isomorphisms to the categorical product and coproduct, respectively.
-/

@[expose] public section


open CategoryTheory Limits ConcreteCategory

universe w v u

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]
variable (F G : C ⥤ Type w)

section prod

/-- `prod F G` is the explicit binary product of type-valued functors `F` and `G`. -/
@[simps obj map]
/-
**CategoryTheory.FunctorToTypes.prod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctorToTypes`。
形式化陈述：prod : C ⥤ Type w where obj a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prod F G` is the explicit binary product of type-valued functors `F` and `G`.
-/
def prod : C ⥤ Type w where
  obj a := F.obj a × G.obj a
  map f := ↾fun a ↦ (F.map f a.1, G.map f a.2)

variable {F G}

/-- The first projection of `prod F G`, onto `F`. -/
@[simps app]
/-
**CategoryTheory.FunctorToTypes.prod.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.FunctorToTypes.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C (Type w)} → CategoryTheory.FunctorToTypes.prod F G ⟶ F
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of `prod F G`, onto `F`.
-/
def prod.fst : prod F G ⟶ F where
  app _ := ↾fun a ↦ a.1

/-- The second projection of `prod F G`, onto `G`. -/
@[simps app]
/-
**CategoryTheory.FunctorToTypes.prod.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.FunctorToTypes.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C (Type w)} → CategoryTheory.FunctorToTypes.prod F G ⟶ G
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of `prod F G`, onto `G`.
-/
def prod.snd : prod F G ⟶ G where
  app _ := ↾fun a ↦ a.2

set_option backward.isDefEq.respectTransparency.types false in
/-- Given natural transformations `F ⟶ F₁` and `F ⟶ F₂`, construct
a natural transformation `F ⟶ prod F₁ F₂`. -/
@[simps]
/-
**CategoryTheory.FunctorToTypes.prod.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.FunctorToTypes.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F F₁ F₂ 
: CategoryTheory.Functor C (Type w)} → (F ⟶ F₁) → (F ⟶ F₂) → (F ⟶ CategoryTheory
.FunctorToTypes.prod F₁ F₂)
参数：Type w；F ⟶ F₁；F ⟶ F₂；F ⟶ CategoryTheory.FunctorToTypes.prod F₁ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given natural transformations `F ⟶ F₁` and `F ⟶ F₂`, construct
a natural transformation `F ⟶ prod F₁ F₂`.
-/
def prod.lift {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ prod F₁ F₂ where
  app x := ↾fun y ↦ ⟨τ₁.app x y, τ₂.app x y⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.prod.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.FunctorToTypes.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F F₁ F₂ : Catego
ryTheory.Functor C (Type w)} (τ₁ : F ⟶ F₁)   (τ₂ : F ⟶ F₂),   CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.FunctorToTypes.prod.lift τ₁ τ₂)       CategoryT
heory.FunctorToTypes.prod.fst =     τ₁
参数：Type w；τ₁ : F ⟶ F₁；τ₂ : F ⟶ F₂；CategoryTheory.FunctorToTypes.prod.lift τ₁ τ₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod.lift_fst {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.fst = τ₁ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.prod.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.FunctorToTypes.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F F₁ F₂ : Catego
ryTheory.Functor C (Type w)} (τ₁ : F ⟶ F₁)   (τ₂ : F ⟶ F₂),   CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.FunctorToTypes.prod.lift τ₁ τ₂)       CategoryT
heory.FunctorToTypes.prod.snd =     τ₂
参数：Type w；τ₁ : F ⟶ F₁；τ₂ : F ⟶ F₂；CategoryTheory.FunctorToTypes.prod.lift τ₁ τ₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod.lift_snd {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.snd = τ₂ := rfl

variable (F G)

/-- The binary fan whose point is `prod F G`. -/
@[simps!]
/-
**CategoryTheory.FunctorToTypes.binaryProductCone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.FunctorToTypes`。
形式化陈述：binaryProductCone : BinaryFan F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary fan whose point is `prod F G`.
-/
def binaryProductCone : BinaryFan F G :=
  BinaryFan.mk prod.fst prod.snd

set_option backward.isDefEq.respectTransparency.types false in
/-- `prod F G` is a limit cone. -/
@[simps]
/-
**CategoryTheory.FunctorToTypes.binaryProductLimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FunctorToTypes`。
形式化陈述：binaryProductLimit : IsLimit (binaryProductCone F G) where lift (s : Binar
yFan F G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prod F G` is a limit cone.
-/
def binaryProductLimit : IsLimit (binaryProductCone F G) where
  lift (s : BinaryFan F G) := prod.lift s.fst s.snd
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr

set_option backward.isDefEq.respectTransparency.types false in
/-- `prod F G` is a binary product for `F` and `G`. -/
/-
**CategoryTheory.FunctorToTypes.binaryProductLimitCone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductLimitCone : Limits.LimitCone (pair F G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prod F G` is a binary product for `F` and `G`.
-/
def binaryProductLimitCone : Limits.LimitCone (pair F G) :=
  ⟨_, binaryProductLimit F G⟩

/-- The categorical binary product of type-valued functors is `prod F G`. -/
/-
**CategoryTheory.FunctorToTypes.binaryProductIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso : F ⨯ G ≅ prod F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical binary product of type-valued functors is `prod F G`.
-/
noncomputable def binaryProductIso : F ⨯ G ≅ prod F G :=
  limit.isoLimitCone (binaryProductLimitCone F G)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.binaryProductIso_hom_comp_fst** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso_hom_comp_fst : (binaryProductIso F G).hom ≫ prod.fst = Li
mits.prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma binaryProductIso_hom_comp_fst :
    (binaryProductIso F G).hom ≫ prod.fst = Limits.prod.fst := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.binaryProductIso_hom_comp_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso_hom_comp_snd : (binaryProductIso F G).hom ≫ prod.snd = Li
mits.prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma binaryProductIso_hom_comp_snd :
    (binaryProductIso F G).hom ≫ prod.snd = Limits.prod.snd := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_fst** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso_inv_comp_fst : (binaryProductIso F G).inv ≫ Limits.prod.f
st = prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.FunctorToTypes.binaryProductCone_π_app`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] (F G : CategoryTheory.Functor C (Type w)
)   (x : CategoryTheory.Discrete CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma binaryProductIso_inv_comp_fst :
    (binaryProductIso F G).inv ≫ Limits.prod.fst = prod.fst := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
/-
**CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_fst_apply** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso_inv_comp_fst_apply (a : C) (z : (prod F G).obj a) : dsimp
% (Limits.prod.fst (X
参数：a : C；z : (prod F G).obj a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_fst`：binaryProdu
ctIso_inv_comp_fst : (binaryProductIso F G).inv ≫ Limits.prod.fst = prod.fst
-/
lemma binaryProductIso_inv_comp_fst_apply (a : C) (z : (prod F G).obj a) :
    dsimp% (Limits.prod.fst (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.1 :=
  congr_hom (congr_app (binaryProductIso_inv_comp_fst F G) a) z

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso_inv_comp_snd : (binaryProductIso F G).inv ≫ Limits.prod.s
nd = prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.FunctorToTypes.binaryProductCone_π_app`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] (F G : CategoryTheory.Functor C (Type w)
)   (x : CategoryTheory.Discrete CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma binaryProductIso_inv_comp_snd :
    (binaryProductIso F G).inv ≫ Limits.prod.snd = prod.snd := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
/-
**CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_snd_apply** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryProductIso_inv_comp_snd_apply (a : C) (z : (prod F G).obj a) : dsimp
% (Limits.prod.snd (X
参数：a : C；z : (prod F G).obj a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_snd`：binaryProdu
ctIso_inv_comp_snd : (binaryProductIso F G).inv ≫ Limits.prod.snd = prod.snd
-/
lemma binaryProductIso_inv_comp_snd_apply (a : C) (z : (prod F G).obj a) :
    dsimp% (Limits.prod.snd (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.2 :=
  congr_hom (congr_app (binaryProductIso_inv_comp_snd F G) a) z

variable {F G}

/-- Construct an element of `(F ⨯ G).obj a` from an element of `F.obj a` and
an element of `G.obj a`. -/
noncomputable
/-
**CategoryTheory.FunctorToTypes.prodMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.FunctorToTypes`。
形式化陈述：prodMk {a : C} (x : F.obj a) (y : G.obj a) : (F ⨯ G).obj a
参数：x : F.obj a；y : G.obj a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodMk {a : C} (x : F.obj a) (y : G.obj a) : (F ⨯ G).obj a :=
  ((binaryProductIso F G).inv).app a ⟨x, y⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.prodMk_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.FunctorToTypes`。
形式化陈述：prodMk_fst {a : C} (x : F.obj a) (y : G.obj a) : (Limits.prod.fst (X
参数：x : F.obj a；y : G.obj a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_fst_apply`：binar
yProductIso_inv_comp_fst_apply (a : C) (z : (prod F G).obj a) : dsimp% (Limits.p
rod.fst (X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodMk_fst {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.fst (X := F)).app a (prodMk x y) = x := by
  simp [prodMk]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.prodMk_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.FunctorToTypes`。
形式化陈述：prodMk_snd {a : C} (x : F.obj a) (y : G.obj a) : (Limits.prod.snd (X
参数：x : F.obj a；y : G.obj a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.FunctorToTypes.binaryProductIso_inv_comp_snd_apply`：binar
yProductIso_inv_comp_snd_apply (a : C) (z : (prod F G).obj a) : dsimp% (Limits.p
rod.snd (X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodMk_snd {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.snd (X := F)).app a (prodMk x y) = y := by
  simp [prodMk]

@[ext]
/-
**CategoryTheory.FunctorToTypes.prod_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.FunctorToTypes`。
形式化陈述：prod_ext {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2
) : z = w
参数：z w : (prod F G).obj a；h1 : z.1 = w.1；h2 : z.2 = w.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
lemma prod_ext {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2) :
    z = w := Prod.ext h1 h2

variable (F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- `(F ⨯ G).obj a` is in bijection with the product of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
/-
**CategoryTheory.FunctorToTypes.binaryProductEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FunctorToTypes`。
形式化陈述：binaryProductEquiv (a : C) : (F ⨯ G).obj a ≃ (F.obj a) × (G.obj a) where t
oFun z
参数：a : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def binaryProductEquiv (a : C) : (F ⨯ G).obj a ≃ (F.obj a) × (G.obj a) where
  toFun z := ⟨((binaryProductIso F G).hom.app a z).1, ((binaryProductIso F G).hom.app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [-prod_obj, prodMk]
  right_inv _ := by simp [-prod_obj, prodMk]

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/-
**CategoryTheory.FunctorToTypes.prod_ext'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.FunctorToTypes`。
形式化陈述：prod_ext' (a : C) (z w : (F ⨯ G).obj a) (h1 : (Limits.prod.fst (X
参数：a : C；z w : (F ⨯ G).obj a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.FunctorToTypes.binaryProductEquiv_apply`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (F G : CategoryTheory.Functor C (Type w
)) (a : C)   (z : (F ⨯ G).obj a),   (Categor…
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
lemma prod_ext' (a : C) (z w : (F ⨯ G).obj a)
    (h1 : (Limits.prod.fst (X := F)).app a z = (Limits.prod.fst (X := F)).app a w)
    (h2 : (Limits.prod.snd (X := F)).app a z = (Limits.prod.snd (X := F)).app a w) :
    z = w := by
  apply Equiv.injective (binaryProductEquiv F G a)
  aesop

end prod

section coprod

/-- `coprod F G` is the explicit binary coproduct of type-valued functors `F` and `G`. -/
@[simps obj map]
/-
**CategoryTheory.FunctorToTypes.coprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.FunctorToTypes`。
形式化陈述：coprod : C ⥤ Type w where obj a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coprod F G` is the explicit binary coproduct of type-valued functors `F` and `G
`.
-/
def coprod : C ⥤ Type w where
  obj a := F.obj a ⊕ G.obj a
  map f := ↾(Sum.map (F.map f) (G.map f))
  map_id _ := by ext ⟨⟩ <;> simp
  map_comp _ _ := by ext ⟨⟩ <;> simp

variable {F G}

/-- The left inclusion of `F` into `coprod F G`. -/
@[simps]
/-
**CategoryTheory.FunctorToTypes.coprod.inl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.FunctorToTypes.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C (Type w)} → F ⟶ CategoryTheory.FunctorToTypes.coprod F G
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inclusion of `F` into `coprod F G`.
-/
def coprod.inl : F ⟶ coprod F G where
  app _ := ↾fun x ↦ .inl x

/-- The right inclusion of `G` into `coprod F G`. -/
@[simps]
/-
**CategoryTheory.FunctorToTypes.coprod.inr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.FunctorToTypes.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor C (Type w)} → G ⟶ CategoryTheory.FunctorToTypes.coprod F G
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion of `G` into `coprod F G`.
-/
def coprod.inr : G ⟶ coprod F G where
  app _ := ↾fun x ↦ .inr x

set_option backward.defeqAttrib.useBackward true in
/-- Given natural transformations `F₁ ⟶ F` and `F₂ ⟶ F`, construct
a natural transformation `coprod F₁ F₂ ⟶ F`. -/
@[simps]
/-
**CategoryTheory.FunctorToTypes.coprod.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.FunctorToTypes.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F F₁ F₂ 
: CategoryTheory.Functor C (Type w)} →       (F₁ ⟶ F) → (F₂ ⟶ F) → (CategoryTheo
ry.FunctorToTypes.coprod F₁ F₂ ⟶ F)
参数：Type w；F₁ ⟶ F；F₂ ⟶ F；CategoryTheory.FunctorToTypes.coprod F₁ F₂ ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given natural transformations `F₁ ⟶ F` and `F₂ ⟶ F`, construct
a natural transformation `coprod F₁ F₂ ⟶ F`.
-/
def coprod.desc {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod F₁ F₂ ⟶ F where
  app a := ↾(Sum.elim (τ₁.app a) (τ₂.app a))
  naturality _ _ _ := by ext ⟨⟩ <;> simp

@[simp]
/-
**CategoryTheory.FunctorToTypes.coprod.desc_inl** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.FunctorToTypes.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F F₁ F₂ : Catego
ryTheory.Functor C (Type w)} (τ₁ : F₁ ⟶ F)   (τ₂ : F₂ ⟶ F),   CategoryTheory.Cat
egoryStruct.comp CategoryTheory.FunctorToTypes.coprod.inl       (CategoryTheory.
FunctorToTypes.coprod.desc τ₁ τ₂) =     τ₁
参数：Type w；τ₁ : F₁ ⟶ F；τ₂ : F₂ ⟶ F；CategoryTheory.FunctorToTypes.coprod.desc τ₁ τ
₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coprod.desc_inl {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inl ≫ coprod.desc τ₁ τ₂ = τ₁ := rfl

@[simp]
/-
**CategoryTheory.FunctorToTypes.coprod.desc_inr** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.FunctorToTypes.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F F₁ F₂ : Catego
ryTheory.Functor C (Type w)} (τ₁ : F₁ ⟶ F)   (τ₂ : F₂ ⟶ F),   CategoryTheory.Cat
egoryStruct.comp CategoryTheory.FunctorToTypes.coprod.inr       (CategoryTheory.
FunctorToTypes.coprod.desc τ₁ τ₂) =     τ₂
参数：Type w；τ₁ : F₁ ⟶ F；τ₂ : F₂ ⟶ F；CategoryTheory.FunctorToTypes.coprod.desc τ₁ τ
₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coprod.desc_inr {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inr ≫ coprod.desc τ₁ τ₂ = τ₂ := rfl

variable (F G)

/-- The binary cofan whose point is `coprod F G`. -/
@[simps!]
/-
**CategoryTheory.FunctorToTypes.binaryCoproductCocone** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.FunctorToTypes`。
形式化陈述：binaryCoproductCocone : BinaryCofan F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary cofan whose point is `coprod F G`.
-/
def binaryCoproductCocone : BinaryCofan F G :=
  BinaryCofan.mk coprod.inl coprod.inr

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `coprod F G` is a colimit cocone. -/
@[simps]
/-
**CategoryTheory.FunctorToTypes.binaryCoproductColimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryCoproductColimit : IsColimit (binaryCoproductCocone F G) where desc 
(s : BinaryCofan F G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coprod F G` is a colimit cocone.
-/
def binaryCoproductColimit : IsColimit (binaryCoproductCocone F G) where
  desc (s : BinaryCofan F G) := coprod.desc s.inl s.inr
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]

/-- `coprod F G` is a binary coproduct for `F` and `G`. -/
/-
**CategoryTheory.FunctorToTypes.binaryCoproductColimitCocone** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：binaryCoproductColimitCocone : Limits.ColimitCocone (pair F G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coprod F G` is a binary coproduct for `F` and `G`.
-/
def binaryCoproductColimitCocone : Limits.ColimitCocone (pair F G) :=
  ⟨_, binaryCoproductColimit F G⟩

/-- The categorical binary coproduct of type-valued functors is `coprod F G`. -/
/-
**CategoryTheory.FunctorToTypes.binaryCoproductIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FunctorToTypes`。
形式化陈述：binaryCoproductIso : F ⨿ G ≅ coprod F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical binary coproduct of type-valued functors is `coprod F G`.
-/
noncomputable def binaryCoproductIso : F ⨿ G ≅ coprod F G :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone F G)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.inl_comp_binaryCoproductIso_hom** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inl_comp_binaryCoproductIso_hom : Limits.coprod.inl ≫ (binaryCoproductIso 
F G).hom = coprod.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma inl_comp_binaryCoproductIso_hom :
    Limits.coprod.inl ≫ (binaryCoproductIso F G).hom = coprod.inl := by
  simp only [binaryCoproductIso]
  aesop

@[simp]
/-
**CategoryTheory.FunctorToTypes.inl_comp_binaryCoproductIso_hom_apply** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inl_comp_binaryCoproductIso_hom_apply (a : C) (x : F.obj a) : dsimp% (bina
ryCoproductIso F G).hom.app a ((Limits.coprod.inl (X
参数：a : C；x : F.obj a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.FunctorToTypes.inl_comp_binaryCoproductIso_hom`：inl_comp_
binaryCoproductIso_hom : Limits.coprod.inl ≫ (binaryCoproductIso F G).hom = copr
od.inl
-/
lemma inl_comp_binaryCoproductIso_hom_apply (a : C) (x : F.obj a) :
    dsimp% (binaryCoproductIso F G).hom.app a ((Limits.coprod.inl (X := F)).app a x) = .inl x :=
  congr_hom (congr_app (inl_comp_binaryCoproductIso_hom F G) a) x

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.FunctorToTypes.inr_comp_binaryCoproductIso_hom** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inr_comp_binaryCoproductIso_hom : Limits.coprod.inr ≫ (binaryCoproductIso 
F G).hom = coprod.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma inr_comp_binaryCoproductIso_hom :
    Limits.coprod.inr ≫ (binaryCoproductIso F G).hom = coprod.inr := by
  simp [binaryCoproductIso]
  aesop

@[simp]
/-
**CategoryTheory.FunctorToTypes.inr_comp_binaryCoproductIso_hom_apply** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inr_comp_binaryCoproductIso_hom_apply (a : C) (x : G.obj a) : dsimp% (bina
ryCoproductIso F G).hom.app a ((Limits.coprod.inr (X
参数：a : C；x : G.obj a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.FunctorToTypes.inr_comp_binaryCoproductIso_hom`：inr_comp_
binaryCoproductIso_hom : Limits.coprod.inr ≫ (binaryCoproductIso F G).hom = copr
od.inr
-/
lemma inr_comp_binaryCoproductIso_hom_apply (a : C) (x : G.obj a) :
    dsimp% (binaryCoproductIso F G).hom.app a ((Limits.coprod.inr (X := F)).app a x) = .inr x :=
  congr_hom (congr_app (inr_comp_binaryCoproductIso_hom F G) a) x

@[simp]
/-
**CategoryTheory.FunctorToTypes.inl_comp_binaryCoproductIso_inv** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inl_comp_binaryCoproductIso_inv : coprod.inl ≫ (binaryCoproductIso F G).in
v = (Limits.coprod.inl (X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma inl_comp_binaryCoproductIso_inv :
    coprod.inl ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inl (X := F)) := rfl

@[simp]
/-
**CategoryTheory.FunctorToTypes.inl_comp_binaryCoproductIso_inv_apply** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inl_comp_binaryCoproductIso_inv_apply (a : C) (x : F.obj a) : dsimp% (bina
ryCoproductIso F G).inv.app a (.inl x) = (Limits.coprod.inl (X
参数：a : C；x : F.obj a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma inl_comp_binaryCoproductIso_inv_apply (a : C) (x : F.obj a) :
    dsimp% (binaryCoproductIso F G).inv.app a (.inl x) = (Limits.coprod.inl (X := F)).app a x := rfl

@[simp]
/-
**CategoryTheory.FunctorToTypes.inr_comp_binaryCoproductIso_inv** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inr_comp_binaryCoproductIso_inv : coprod.inr ≫ (binaryCoproductIso F G).in
v = (Limits.coprod.inr (X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma inr_comp_binaryCoproductIso_inv :
    coprod.inr ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inr (X := F)) := rfl

@[simp]
/-
**CategoryTheory.FunctorToTypes.inr_comp_binaryCoproductIso_inv_apply** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：inr_comp_binaryCoproductIso_inv_apply (a : C) (x : G.obj a) : dsimp% (bina
ryCoproductIso F G).inv.app a (.inr x) = (Limits.coprod.inr (X
参数：a : C；x : G.obj a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma inr_comp_binaryCoproductIso_inv_apply (a : C) (x : G.obj a) :
    dsimp% (binaryCoproductIso F G).inv.app a (.inr x) = (Limits.coprod.inr (X := F)).app a x := rfl

variable {F G}

/-- Construct an element of `(F ⨿ G).obj a` from an element of `F.obj a` -/
noncomputable
/-
**CategoryTheory.FunctorToTypes.coprodInl** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.FunctorToTypes`。
形式化陈述：coprodInl {a : C} (x : F.obj a) : (F ⨿ G).obj a
参数：x : F.obj a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev coprodInl {a : C} (x : F.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inl x)

/-- Construct an element of `(F ⨿ G).obj a` from an element of `G.obj a` -/
noncomputable
/-
**CategoryTheory.FunctorToTypes.coprodInr** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.FunctorToTypes`。
形式化陈述：coprodInr {a : C} (x : G.obj a) : (F ⨿ G).obj a
参数：x : G.obj a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev coprodInr {a : C} (x : G.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inr x)

variable (F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- `(F ⨿ G).obj a` is in bijection with disjoint union of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
/-
**CategoryTheory.FunctorToTypes.binaryCoproductEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.FunctorToTypes`。
形式化陈述：binaryCoproductEquiv (a : C) : (F ⨿ G).obj a ≃ (F.obj a) oplus (G.obj a) w
here toFun z
参数：a : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def binaryCoproductEquiv (a : C) :
    (F ⨿ G).obj a ≃ (F.obj a) ⊕ (G.obj a) where
  toFun z := (binaryCoproductIso F G).hom.app a z
  invFun z := (binaryCoproductIso F G).inv.app a z
  left_inv _ := by simp [-coprod_obj]
  right_inv _ := by simp [-coprod_obj]

end coprod

end CategoryTheory.FunctorToTypes

