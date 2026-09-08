/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.FinCategory.AsType

/-!
# Creation of finite limits

This file defines the classes `CreatesFiniteLimits`, `CreatesFiniteColimits`,
`CreatesFiniteProducts` and `CreatesFiniteCoproducts`.
-/

@[expose] public section

namespace CategoryTheory.Limits


universe w w' v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- We say that a functor creates finite limits if it creates all limits of shape `J` where
`J : Type` is a finite category. -/
/-
**CategoryTheory.Limits.CreatesFiniteLimits** 是 Mathlib 中的一个类，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：CreatesFiniteLimits (F : C ⥤ D) where /-- `F` creates all finite limits. -
/ createsFiniteLimits : forall (J : Type) [SmallCategory J] [FinCategory J], Cre
atesLimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a functor creates finite limits if it creates all limits of shape `J
` where
`J : Type` is a finite category.
-/
class CreatesFiniteLimits (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  createsFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], CreatesLimitsOfShape J F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteLimits.createsFiniteLimits

noncomputable section
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) createsLimitsOfShapeOfCreatesFiniteLimits (F : C ⥤ D)
    [CreatesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J F :=
  createsLimitsOfShapeOfEquiv (FinCategory.equivAsType J) _

-- Cannot be an instance because of unbound universe variables.
/-- If `F` creates limits of any size, it creates finite limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.CreatesLimitsOfSize.createsFiniteLimits** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.CreatesLimitsOfSize`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) →           [CategoryTheory.CreatesLimitsOfSize.{w, w',
 v₁, v₂, u₁, u₂} F] → CategoryTheory.Limits.CreatesFiniteLimits F
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates limits of any size, it creates finite limits.
-/
def CreatesLimitsOfSize.createsFiniteLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) CreatesLimitsOfSize0.createsFiniteLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{0, 0} F] : CreatesFiniteLimits F :=
  CreatesLimitsOfSize.createsFiniteLimits F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CreatesLimits.createsFiniteLimits (F : C ⥤ D)
    [CreatesLimits F] : CreatesFiniteLimits F :=
  CreatesLimitsOfSize.createsFiniteLimits F

attribute [local instance] uliftCategory in
/-- If `F` creates finite limits in any universe, then it creates finite limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfCreatesFiniteLimitsOfSize** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfCreatesFiniteLimitsOfSize (F : C ⥤ D) (h : forall (J 
: Type w) {_ : SmallCategory J} (_ : FinCategory J), CreatesLimitsOfShape J F) :
 CreatesFiniteLimits F where createsFiniteLimits J _ _
参数：F : C ⥤ D；h : forall (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), 
CreatesLimitsOfShape J F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates finite limits in any universe, then it creates finite limits.
-/
def createsFiniteLimitsOfCreatesFiniteLimitsOfSize (F : C ⥤ D)
    (h : ∀ (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), CreatesLimitsOfShape J F) :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ :=
    haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _
/-
**CategoryTheory.Limits.compCreatesFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：compCreatesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteLimits F] [C
reatesFiniteLimits G] : CreatesFiniteLimits (F ⋙ G) where createsFiniteLimits _ 
_ _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteLimits F]
    [CreatesFiniteLimits G] : CreatesFiniteLimits (F ⋙ G) where
  createsFiniteLimits _ _ _ := compCreatesLimitsOfShape F G

/-- Transfer creation of finite limits along a natural isomorphism in the functor. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteLimits
 F] : CreatesFiniteLimits G where createsFiniteLimits _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer creation of finite limits along a natural isomorphism in the functor.
-/
def createsFiniteLimitsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteLimits F] :
    CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ := createsLimitsOfShapeOfNatIso h
/-
**CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimit
s** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (F : C ⥤ D) [Has
FiniteLimits D] [CreatesFiniteLimits F] : HasFiniteLimits C where out _ _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
`：hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimi
tsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
theorem hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (F : C ⥤ D) [HasFiniteLimits D]
    [CreatesFiniteLimits F] : HasFiniteLimits C where
  out _ _ _ := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesFiniteLimits_of_createsFiniteLimits_and_hasFiniteLimits
    (F : C ⥤ D) [CreatesFiniteLimits F] [HasFiniteLimits D] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := inferInstance

end

/-- We say that a functor creates finite products if it creates all limits of shape `Discrete J`
where `J : Type` is finite. -/
/-
**CategoryTheory.Limits.CreatesFiniteProducts** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory.Limits`。
形式化陈述：CreatesFiniteProducts (F : C ⥤ D) where /-- `F` creates all finite limits.
 -/ creates : forall (J : Type) [Fintype J], CreatesLimitsOfShape (Discrete J) F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a functor creates finite products if it creates all limits of shape 
`Discrete J`
where `J : Type` is finite.
-/
class CreatesFiniteProducts (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  creates :
    ∀ (J : Type) [Fintype J], CreatesLimitsOfShape (Discrete J) F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteProducts.creates

noncomputable section

/-- The condition of `CreatesFiniteProducts` can be checked for finite types in an arbitrary
universe. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.CreatesFiniteProducts.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.CreatesFiniteProducts`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) →           ((J : Type w) → [Fintype J] → CategoryTheor
y.CreatesLimitsOfShape (CategoryTheory.Discrete J) F) →             CategoryTheo
ry.Limits.CreatesFiniteProducts F
参数：F : CategoryTheory.Functor C D；(J : Type w) → [Fintype J] → CategoryTheory.Cr
eatesLimitsOfShape (CategoryTheory.Discrete J) F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition of `CreatesFiniteProducts` can be checked for finite types in an a
rbitrary
universe.
-/
def CreatesFiniteProducts.mk' (F : C ⥤ D)
    (H : ∀ (J : Type w) [Fintype J], CreatesLimitsOfShape (Discrete J) F) :
    CreatesFiniteProducts F where
  creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift.{w}) F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) createsLimitsOfShapeOfCreatesFiniteProducts (F : C ⥤ D)
    [CreatesFiniteProducts F] (J : Type w) [Finite J] : CreatesLimitsOfShape (Discrete J) F :=
  createsLimitsOfShapeOfEquiv
    (Discrete.equivalence (Finite.exists_equiv_fin J).choose_spec.some.symm) F
/-
**CategoryTheory.Limits.compCreatesFiniteProducts** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：compCreatesFiniteProducts (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteProducts F
] [CreatesFiniteProducts G] : CreatesFiniteProducts (F ⋙ G) where creates _ _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesFiniteProducts (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteProducts F]
    [CreatesFiniteProducts G] : CreatesFiniteProducts (F ⋙ G) where
  creates _ _ := compCreatesLimitsOfShape _ _

/-- Transfer creation of finite products along a natural isomorphism in the functor. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteProductsOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsFiniteProductsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteProd
ucts F] : CreatesFiniteProducts G where creates _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer creation of finite products along a natural isomorphism in the functor.
-/
def createsFiniteProductsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteProducts F] :
    CreatesFiniteProducts G where
  creates _ _ := createsLimitsOfShapeOfNatIso h
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [CreatesFiniteLimits F] : CreatesFiniteProducts F where
  creates _ _ := inferInstance

end

/-- We say that a functor creates finite colimits if it creates all colimits of shape `J` where
`J : Type` is a finite category. -/
/-
**CategoryTheory.Limits.CreatesFiniteColimits** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory.Limits`。
形式化陈述：CreatesFiniteColimits (F : C ⥤ D) where /-- `F` creates all finite colimit
s. -/ createsFiniteColimits : forall (J : Type) [SmallCategory J] [FinCategory J
], CreatesColimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a functor creates finite colimits if it creates all colimits of shap
e `J` where
`J : Type` is a finite category.
-/
class CreatesFiniteColimits (F : C ⥤ D) where
  /-- `F` creates all finite colimits. -/
  createsFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], CreatesColimitsOfShape J F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteColimits.createsFiniteColimits

noncomputable section
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) createsColimitsOfShapeOfCreatesFiniteColimits (F : C ⥤ D)
    [CreatesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J F :=
  createsColimitsOfShapeOfEquiv (FinCategory.equivAsType J) _

-- Cannot be an instance because of unbound universe variables.
/-- If `F` creates colimits of any size, it creates finite colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.CreatesColimitsOfSize.createsFiniteColimits** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits.CreatesColimitsOfSize`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) →           [CategoryTheory.CreatesColimitsOfSize.{w, w
', v₁, v₂, u₁, u₂} F] →             CategoryTheory.Limits.CreatesFiniteColimits 
F
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates colimits of any size, it creates finite colimits.
-/
def CreatesColimitsOfSize.createsFiniteColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) CreatesColimitsOfSize0.createsFiniteColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{0, 0} F] : CreatesFiniteColimits F :=
  CreatesColimitsOfSize.createsFiniteColimits F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CreatesColimits.createsFiniteColimits (F : C ⥤ D)
    [CreatesColimits F] : CreatesFiniteColimits F :=
  CreatesColimitsOfSize.createsFiniteColimits F

attribute [local instance] uliftCategory in
/-- If `F` creates finite colimits in any universe, then it creates finite colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfCreatesFiniteColimitsOfSize** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfCreatesFiniteColimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), CreatesColimitsOfShape 
J F) : CreatesFiniteColimits F where createsFiniteColimits J _ _
参数：F : C ⥤ D；h : forall (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), 
CreatesColimitsOfShape J F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates finite colimits in any universe, then it creates finite colimits.
-/
def createsFiniteColimitsOfCreatesFiniteColimitsOfSize (F : C ⥤ D)
    (h : ∀ (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), CreatesColimitsOfShape J F) :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ :=
    haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _
/-
**CategoryTheory.Limits.compCreatesFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：compCreatesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteColimits F
] [CreatesFiniteColimits G] : CreatesFiniteColimits (F ⋙ G) where createsFiniteC
olimits _ _ _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteColimits F]
    [CreatesFiniteColimits G] : CreatesFiniteColimits (F ⋙ G) where
  createsFiniteColimits _ _ _ := compCreatesColimitsOfShape F G

/-- Transfer creation of finite colimits along a natural isomorphism in the functor. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteColi
mits F] : CreatesFiniteColimits G where createsFiniteColimits _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer creation of finite colimits along a natural isomorphism in the functor.
-/
def createsFiniteColimitsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteColimits F] :
    CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ := createsColimitsOfShapeOfNatIso h
/-
**CategoryTheory.Limits.hasFiniteColimits_of_hasColimits_of_createsFiniteColimit
s** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (F : C ⥤ D) [Has
FiniteColimits D] [CreatesFiniteColimits F] : HasFiniteColimits C where out _ _ 
_
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsO
fShape`：hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤
 D) [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColim…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
-/
theorem hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (F : C ⥤ D) [HasFiniteColimits D]
    [CreatesFiniteColimits F] : HasFiniteColimits C where
  out _ _ _ := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preservesFiniteColimits_of_createsFiniteColimits_and_hasFiniteColimits
    (F : C ⥤ D) [CreatesFiniteColimits F] [HasFiniteColimits D] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := inferInstance

end

/-- We say that a functor creates finite limits if it creates all limits of shape `J` where
`J : Type` is a finite category. -/
/-
**CategoryTheory.Limits.CreatesFiniteCoproducts** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：CreatesFiniteCoproducts (F : C ⥤ D) where /-- `F` creates all finite limit
s. -/ creates : forall (J : Type) [Fintype J], CreatesColimitsOfShape (Discrete 
J) F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a functor creates finite limits if it creates all limits of shape `J
` where
`J : Type` is a finite category.
-/
class CreatesFiniteCoproducts (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  creates :
    ∀ (J : Type) [Fintype J], CreatesColimitsOfShape (Discrete J) F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteCoproducts.creates

noncomputable section
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) createsColimitsOfShapeOfCreatesFiniteProducts (F : C ⥤ D)
    [CreatesFiniteCoproducts F] (J : Type w) [Finite J] : CreatesColimitsOfShape (Discrete J) F :=
  createsColimitsOfShapeOfEquiv
    (Discrete.equivalence (Finite.exists_equiv_fin J).choose_spec.some.symm) F
/-
**CategoryTheory.Limits.compCreatesFiniteCoproducts** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：compCreatesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteCoproduc
ts F] [CreatesFiniteCoproducts G] : CreatesFiniteCoproducts (F ⋙ G) where create
s _ _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteCoproducts F]
    [CreatesFiniteCoproducts G] : CreatesFiniteCoproducts (F ⋙ G) where
  creates _ _ := compCreatesColimitsOfShape _ _

/-- Transfer creation of finite limits along a natural isomorphism in the functor. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteCoproductsOfNatIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：createsFiniteCoproductsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteCo
products F] : CreatesFiniteCoproducts G where creates _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer creation of finite limits along a natural isomorphism in the functor.
-/
def createsFiniteCoproductsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteCoproducts F] :
    CreatesFiniteCoproducts G where
  creates _ _ := createsColimitsOfShapeOfNatIso h
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [CreatesFiniteColimits F] : CreatesFiniteCoproducts F where
  creates _ _ := inferInstance

end

end CategoryTheory.Limits

