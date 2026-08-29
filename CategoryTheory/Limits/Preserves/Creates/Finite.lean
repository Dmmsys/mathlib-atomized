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

/--
Definition of `CreatesFiniteLimits` / `CreatesFiniteLimits` 的定义

English:
class CreatesFiniteLimits
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - createsFiniteLimits : forall (J : Type) [SmallCategory J] [FinCategory J], CreatesLimitsOfShape J F  [default: by infer_instance]

中文:
类 创造有限极限
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - createsFiniteLimits : 对任意 (J : 类型) [小范畴 J] [有限范畴 J], 创造形状极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesFiniteLimits (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  createsFiniteLimits :
    forall (J : Type) [SmallCategory J] [FinCategory J], CreatesLimitsOfShape J F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteLimits.createsFiniteLimits

noncomputable section

instance (priority := 100) createsLimitsOfShapeOfCreatesFiniteLimits (F : C ⥤ D)
    [CreatesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J F :=
  createsLimitsOfShapeOfEquiv (FinCategory.equivAsType J) _

-- Cannot be an instance because of unbound universe variables.
/-- If `F` creates limits of any size, it creates finite limits. -/
@[instance_reducible]
/--
Definition of `CreatesLimitsOfSize.createsFiniteLimits` / `CreatesLimitsOfSize.createsFiniteLimits` 的定义

English:
definition CreatesLimitsOfSize.createsFiniteLimits
  signature: (F : C ⥤ D)
  body: createsLimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _

中文:
定义 CreatesLimitsOfSize.createsFiniteLimits
  签名: (F : C ⥤ D)
  定义体: createsLimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _

Depends on / 依赖: createsLimitsOfShapeOfEquiv
-/
def CreatesLimitsOfSize.createsFiniteLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _

instance (priority := 120) CreatesLimitsOfSize0.createsFiniteLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{0, 0} F] : CreatesFiniteLimits F :=
  CreatesLimitsOfSize.createsFiniteLimits F

instance (priority := 100) CreatesLimits.createsFiniteLimits (F : C ⥤ D)
    [CreatesLimits F] : CreatesFiniteLimits F :=
  CreatesLimitsOfSize.createsFiniteLimits F

attribute [local instance] uliftCategory in
/-- If `F` creates finite limits in any universe, then it creates finite limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfCreatesFiniteLimitsOfSize` / `createsFiniteLimitsOfCreatesFiniteLimitsOfSize` 的定义

English:
definition createsFiniteLimitsOfCreatesFiniteLimitsOfSize
  signature: (F : C ⥤ D)
  body: haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _

中文:
定义 createsFiniteLimitsOfCreatesFiniteLimitsOfSize
  签名: (F : C ⥤ D)
  定义体: haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _

Depends on / 依赖: CategoryTheory, CategoryTheory.finCategoryUlift, ULiftHom, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, createsLimitsOfShapeOfEquiv, finCategoryUlift
-/
def createsFiniteLimitsOfCreatesFiniteLimitsOfSize (F : C ⥤ D)
    (h : forall (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), CreatesLimitsOfShape J F) :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ :=
    haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _

/--
Instance `compCreatesFiniteLimits` / 实例 `compCreatesFiniteLimits`

English:
instance compCreatesFiniteLimits
  signature: (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteLimits F]
  body: compCreatesLimitsOfShape F G

中文:
实例 compCreatesFiniteLimits
  签名: (F : C ⥤ D) (G : D ⥤ E) [创造有限极限 F]
  定义体: compCreatesLimitsOfShape F G

Depends on / 依赖: compCreatesLimitsOfShape
-/
instance compCreatesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteLimits F]
    [CreatesFiniteLimits G] : CreatesFiniteLimits (F ⋙ G) where
  createsFiniteLimits _ _ _ := compCreatesLimitsOfShape F G

/-- Transfer creation of finite limits along a natural isomorphism in the functor. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfNatIso` / `createsFiniteLimitsOfNatIso` 的定义

English:
definition createsFiniteLimitsOfNatIso
  signature: {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteLimits F]
  body: createsLimitsOfShapeOfNatIso h

中文:
定义 createsFiniteLimitsOf自然数Iso
  签名: {F G : C ⥤ D} {h : F ≅ G} [创造有限极限 F]
  定义体: createsLimitsOfShapeOfNatIso h

Depends on / 依赖: createsLimitsOfShapeOfNatIso
-/
def createsFiniteLimitsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteLimits F] :
    CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ := createsLimitsOfShapeOfNatIso h

/--
theorem `hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits` / 定理 `hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits`

English:
theorem hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
  statement: (F : C ⥤ D) [HasFiniteLimits D]
  proof: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F

中文:
定理 hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
  结论: (F : C ⥤ D) [有有限极限 D]
  证明: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F

Depends on / 依赖: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
theorem hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (F : C ⥤ D) [HasFiniteLimits D]
    [CreatesFiniteLimits F] : HasFiniteLimits C where
  out _ _ _ := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F

instance (priority := 100) preservesFiniteLimits_of_createsFiniteLimits_and_hasFiniteLimits
    (F : C ⥤ D) [CreatesFiniteLimits F] [HasFiniteLimits D] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := inferInstance

end

/--
Definition of `CreatesFiniteProducts` / `CreatesFiniteProducts` 的定义

English:
class CreatesFiniteProducts
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - creates : forall (J : Type) [Fintype J], CreatesLimitsOfShape (Discrete J) F  [default: by infer_instance]

中文:
类 CreatesFiniteProducts
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - creates : 对任意 (J : 类型) [有限类型 J], 创造形状极限 (离散 J) F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesFiniteProducts (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  creates :
    forall (J : Type) [Fintype J], CreatesLimitsOfShape (Discrete J) F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteProducts.creates

noncomputable section

/-- The condition of `CreatesFiniteProducts` can be checked for finite types in an arbitrary
universe. -/
@[instance_reducible]
/--
Definition of `CreatesFiniteProducts.mk'` / `CreatesFiniteProducts.mk'` 的定义

English:
definition CreatesFiniteProducts.mk'
  signature: (F : C ⥤ D)
  body: createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift.{w}) F

中文:
定义 CreatesFiniteProducts.mk'
  签名: (F : C ⥤ D)
  定义体: createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift.{w}) F

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.ulift, createsLimitsOfShapeOfEquiv, equivalence
-/
def CreatesFiniteProducts.mk' (F : C ⥤ D)
    (H : forall (J : Type w) [Fintype J], CreatesLimitsOfShape (Discrete J) F) :
    CreatesFiniteProducts F where
  creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift.{w}) F

instance (priority := 100) createsLimitsOfShapeOfCreatesFiniteProducts (F : C ⥤ D)
    [CreatesFiniteProducts F] (J : Type w) [Finite J] : CreatesLimitsOfShape (Discrete J) F :=
  createsLimitsOfShapeOfEquiv
    (Discrete.equivalence (Finite.exists_equiv_fin J).choose_spec.some.symm) F

/--
Instance `compCreatesFiniteProducts` / 实例 `compCreatesFiniteProducts`

English:
instance compCreatesFiniteProducts
  signature: (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteProducts F]
  body: compCreatesLimitsOfShape _ _

中文:
实例 compCreatesFiniteProducts
  签名: (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteProducts F]
  定义体: compCreatesLimitsOfShape _ _

Depends on / 依赖: compCreatesLimitsOfShape
-/
instance compCreatesFiniteProducts (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteProducts F]
    [CreatesFiniteProducts G] : CreatesFiniteProducts (F ⋙ G) where
  creates _ _ := compCreatesLimitsOfShape _ _

/-- Transfer creation of finite products along a natural isomorphism in the functor. -/
@[instance_reducible]
/--
Definition of `createsFiniteProductsOfNatIso` / `createsFiniteProductsOfNatIso` 的定义

English:
definition createsFiniteProductsOfNatIso
  signature: {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteProducts F]
  body: createsLimitsOfShapeOfNatIso h

中文:
定义 createsFiniteProductsOf自然数Iso
  签名: {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteProducts F]
  定义体: createsLimitsOfShapeOfNatIso h

Depends on / 依赖: createsLimitsOfShapeOfNatIso
-/
def createsFiniteProductsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteProducts F] :
    CreatesFiniteProducts G where
  creates _ _ := createsLimitsOfShapeOfNatIso h

instance (F : C ⥤ D) [CreatesFiniteLimits F] : CreatesFiniteProducts F where
  creates _ _ := inferInstance

end

/--
Definition of `CreatesFiniteColimits` / `CreatesFiniteColimits` 的定义

English:
class CreatesFiniteColimits
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - createsFiniteColimits : forall (J : Type) [SmallCategory J] [FinCategory J], CreatesColimitsOfShape J F  [default: by infer_instance]

中文:
类 创造有限余极限
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - createsFiniteColimits : 对任意 (J : 类型) [小范畴 J] [有限范畴 J], 创造形状余极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesFiniteColimits (F : C ⥤ D) where
  /-- `F` creates all finite colimits. -/
  createsFiniteColimits :
    forall (J : Type) [SmallCategory J] [FinCategory J], CreatesColimitsOfShape J F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteColimits.createsFiniteColimits

noncomputable section

instance (priority := 100) createsColimitsOfShapeOfCreatesFiniteColimits (F : C ⥤ D)
    [CreatesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J F :=
  createsColimitsOfShapeOfEquiv (FinCategory.equivAsType J) _

-- Cannot be an instance because of unbound universe variables.
/-- If `F` creates colimits of any size, it creates finite colimits. -/
@[instance_reducible]
/--
Definition of `CreatesColimitsOfSize.createsFiniteColimits` / `CreatesColimitsOfSize.createsFiniteColimits` 的定义

English:
definition CreatesColimitsOfSize.createsFiniteColimits
  signature: (F : C ⥤ D)
  body: createsColimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _

中文:
定义 CreatesColimitsOfSize.createsFiniteColimits
  签名: (F : C ⥤ D)
  定义体: createsColimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _

Depends on / 依赖: createsColimitsOfShapeOfEquiv
-/
def CreatesColimitsOfSize.createsFiniteColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfEquiv
    ((ShrinkHoms.equivalence.{w} J).trans (Shrink.equivalence.{w'} _)).symm _

instance (priority := 120) CreatesColimitsOfSize0.createsFiniteColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{0, 0} F] : CreatesFiniteColimits F :=
  CreatesColimitsOfSize.createsFiniteColimits F

instance (priority := 100) CreatesColimits.createsFiniteColimits (F : C ⥤ D)
    [CreatesColimits F] : CreatesFiniteColimits F :=
  CreatesColimitsOfSize.createsFiniteColimits F

attribute [local instance] uliftCategory in
/-- If `F` creates finite colimits in any universe, then it creates finite colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfCreatesFiniteColimitsOfSize` / `createsFiniteColimitsOfCreatesFiniteColimitsOfSize` 的定义

English:
definition createsFiniteColimitsOfCreatesFiniteColimitsOfSize
  signature: (F : C ⥤ D)
  body: haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _

中文:
定义 createsFiniteColimitsOfCreatesFiniteColimitsOfSize
  签名: (F : C ⥤ D)
  定义体: haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _

Depends on / 依赖: CategoryTheory, CategoryTheory.finCategoryUlift, ULiftHom, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, createsColimitsOfShapeOfEquiv, finCategoryUlift
-/
def createsFiniteColimitsOfCreatesFiniteColimitsOfSize (F : C ⥤ D)
    (h : forall (J : Type w) {_ : SmallCategory J} (_ : FinCategory J), CreatesColimitsOfShape J F) :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ :=
    haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
    createsColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv J).symm _

/--
Instance `compCreatesFiniteColimits` / 实例 `compCreatesFiniteColimits`

English:
instance compCreatesFiniteColimits
  signature: (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteColimits F]
  body: compCreatesColimitsOfShape F G

中文:
实例 compCreatesFiniteColimits
  签名: (F : C ⥤ D) (G : D ⥤ E) [创造有限余极限 F]
  定义体: compCreatesColimitsOfShape F G

Depends on / 依赖: compCreatesColimitsOfShape
-/
instance compCreatesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteColimits F]
    [CreatesFiniteColimits G] : CreatesFiniteColimits (F ⋙ G) where
  createsFiniteColimits _ _ _ := compCreatesColimitsOfShape F G

/-- Transfer creation of finite colimits along a natural isomorphism in the functor. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfNatIso` / `createsFiniteColimitsOfNatIso` 的定义

English:
definition createsFiniteColimitsOfNatIso
  signature: {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteColimits F]
  body: createsColimitsOfShapeOfNatIso h

中文:
定义 createsFiniteColimitsOf自然数Iso
  签名: {F G : C ⥤ D} {h : F ≅ G} [创造有限余极限 F]
  定义体: createsColimitsOfShapeOfNatIso h

Depends on / 依赖: createsColimitsOfShapeOfNatIso
-/
def createsFiniteColimitsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteColimits F] :
    CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ := createsColimitsOfShapeOfNatIso h

/--
theorem `hasFiniteColimits_of_hasColimits_of_createsFiniteColimits` / 定理 `hasFiniteColimits_of_hasColimits_of_createsFiniteColimits`

English:
theorem hasFiniteColimits_of_hasColimits_of_createsFiniteColimits
  statement: (F : C ⥤ D) [HasFiniteColimits D]
  proof: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F

中文:
定理 hasFiniteColimits_of_hasColimits_of_createsFiniteColimits
  结论: (F : C ⥤ D) [有有限余极限 D]
  证明: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F

Depends on / 依赖: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
theorem hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (F : C ⥤ D) [HasFiniteColimits D]
    [CreatesFiniteColimits F] : HasFiniteColimits C where
  out _ _ _ := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F

instance (priority := 100) preservesFiniteColimits_of_createsFiniteColimits_and_hasFiniteColimits
    (F : C ⥤ D) [CreatesFiniteColimits F] [HasFiniteColimits D] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := inferInstance

end

/--
Definition of `CreatesFiniteCoproducts` / `CreatesFiniteCoproducts` 的定义

English:
class CreatesFiniteCoproducts
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - creates : forall (J : Type) [Fintype J], CreatesColimitsOfShape (Discrete J) F  [default: by infer_instance]

中文:
类 CreatesFiniteCoproducts
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - creates : 对任意 (J : 类型) [有限类型 J], 创造形状余极限 (离散 J) F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesFiniteCoproducts (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  creates :
    forall (J : Type) [Fintype J], CreatesColimitsOfShape (Discrete J) F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteCoproducts.creates

noncomputable section

instance (priority := 100) createsColimitsOfShapeOfCreatesFiniteProducts (F : C ⥤ D)
    [CreatesFiniteCoproducts F] (J : Type w) [Finite J] : CreatesColimitsOfShape (Discrete J) F :=
  createsColimitsOfShapeOfEquiv
    (Discrete.equivalence (Finite.exists_equiv_fin J).choose_spec.some.symm) F

/--
Instance `compCreatesFiniteCoproducts` / 实例 `compCreatesFiniteCoproducts`

English:
instance compCreatesFiniteCoproducts
  signature: (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteCoproducts F]
  body: compCreatesColimitsOfShape _ _

中文:
实例 compCreatesFiniteCoproducts
  签名: (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteCoproducts F]
  定义体: compCreatesColimitsOfShape _ _

Depends on / 依赖: compCreatesColimitsOfShape
-/
instance compCreatesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E) [CreatesFiniteCoproducts F]
    [CreatesFiniteCoproducts G] : CreatesFiniteCoproducts (F ⋙ G) where
  creates _ _ := compCreatesColimitsOfShape _ _

/-- Transfer creation of finite limits along a natural isomorphism in the functor. -/
@[instance_reducible]
/--
Definition of `createsFiniteCoproductsOfNatIso` / `createsFiniteCoproductsOfNatIso` 的定义

English:
definition createsFiniteCoproductsOfNatIso
  signature: {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteCoproducts F]
  body: createsColimitsOfShapeOfNatIso h

中文:
定义 createsFiniteCoproductsOf自然数Iso
  签名: {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteCoproducts F]
  定义体: createsColimitsOfShapeOfNatIso h

Depends on / 依赖: createsColimitsOfShapeOfNatIso
-/
def createsFiniteCoproductsOfNatIso {F G : C ⥤ D} {h : F ≅ G} [CreatesFiniteCoproducts F] :
    CreatesFiniteCoproducts G where
  creates _ _ := createsColimitsOfShapeOfNatIso h

instance (F : C ⥤ D) [CreatesFiniteColimits F] : CreatesFiniteCoproducts F where
  creates _ _ := inferInstance

end

end CategoryTheory.Limits
