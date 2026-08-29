/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# Category of types with an omega complete partial order

In this file, we bundle the class `OmegaCompletePartialOrder` into a
concrete category and prove that continuous functions also form
an `OmegaCompletePartialOrder`.

## Main definitions

* `ωCPO`
  * an instance of `Category` and `ConcreteCategory`

-/

@[expose] public section


open CategoryTheory

universe u v


/--
Definition of `ωCPO` / `ωCPO` 的定义

English:
structure ωCPO
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [str : OmegaCompletePartialOrder carrier]

中文:
结构 ωCPO
  参数: : 类型 (u + 1) where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [str : OmegaCompletePartial序 carrier]
-/
structure ωCPO : Type (u + 1) where
  /-- Construct a bundled ωCPO from the underlying type and typeclass. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [str : OmegaCompletePartialOrder carrier]

attribute [instance] ωCPO.str

namespace ωCPO

open OmegaCompletePartialOrder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort ωCPO Type*
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort ωCPO 类型
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort ωCPO Type* :=
  ⟨carrier⟩

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [OmegaCompletePartialOrder α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [OmegaCompletePartial序 α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [OmegaCompletePartialOrder α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} ωCPO
  body: ContinuousHom X Y
  id X := ContinuousHom.id
  comp f g := g.comp f

中文:
实例 :
  签名: 大范畴.{u} ωCPO
  定义体: ContinuousHom X Y
  id X := ContinuousHom.id
  comp f g := g.comp f

Depends on / 依赖: ContinuousHom
-/
instance : LargeCategory.{u} ωCPO where
  Hom X Y := ContinuousHom X Y
  id X := ContinuousHom.id
  comp f g := g.comp f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory ωCPO (ContinuousHom · ·)
  body: f
  ofHom f := f

中文:
实例 :
  签名: 余ncrete范畴 ωCPO (连续态射 · ·)
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory ωCPO (ContinuousHom · ·) where
  hom f := f
  ofHom f := f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ωCPO
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 ωCPO
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited ωCPO :=
  ⟨of PUnit⟩

section

open CategoryTheory.Limits

namespace HasProducts

/--
Definition of `product` / `product` 的定义

English:
definition product
  signature: {J : Type v} (f : J -> ωCPO.{v})
  body: Fan.mk (of (forall j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl

中文:
定义 product
  签名: {J : 类型v} (f : J -> ωCPO.{v})
  定义体: Fan.mk (of (forall j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl

Depends on / 依赖: Fan.mk, Pi.evalOrderHom, evalOrderHom
-/
def product {J : Type v} (f : J -> ωCPO.{v}) : Fan f :=
  Fan.mk (of (forall j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl

/--
Definition of `isProduct` / `isProduct` 的定义

English:
definition isProduct
  signature: (J : Type v) (f : J -> ωCPO)
  body: ⟨⟨fun t j => (s.π.app ⟨j⟩) t, fun _ _ h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext t j`
    change m t j = (s.π.app ⟨j⟩) t
    rw [← w ⟨j⟩]
    rfl
  fac _ _ := rfl

中文:
定义 isProduct
  签名: (J : 类型v) (f : J -> ωCPO)
  定义体: ⟨⟨fun t j => (s.π.app ⟨j⟩) t, fun _ _ h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext t j`
    change m t j = (s.π.app ⟨j⟩) t
    rw [← w ⟨j⟩]
    rfl
  fac _ _ := rfl

Depends on / 依赖: Originally, Porting, community, continuous, github, github.com, issues, leanprover, mathlib4, monotone
-/
def isProduct (J : Type v) (f : J -> ωCPO) : IsLimit (product f) where
  lift s :=
    ⟨⟨fun t j => (s.π.app ⟨j⟩) t, fun _ _ h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext t j`
    change m t j = (s.π.app ⟨j⟩) t
    rw [← w ⟨j⟩]
    rfl
  fac _ _ := rfl

instance (J : Type v) (f : J -> ωCPO.{v}) : HasProduct f :=
  HasLimit.mk ⟨_, isProduct _ f⟩

end HasProducts

/--
Instance `omegaCompletePartialOrderEqualizer` / 实例 `omegaCompletePartialOrderEqualizer`

English:
instance omegaCompletePartialOrderEqualizer
  signature: {α β : Type*} [OmegaCompletePartialOrder α]
  body: OmegaCompletePartialOrder.subtype _ fun c hc => by
    rw [f.continuous]; rw [g.continuous]
    congr 1
    ext x
    apply hc _ ⟨_, rfl⟩

中文:
实例 omegaCompletePartialOrderEqualizer
  签名: {α β : 类型} [OmegaCompletePartial序 α]
  定义体: OmegaCompletePartialOrder.subtype _ fun c hc => by
    rw [f.continuous]; rw [g.continuous]
    congr 1
    ext x
    apply hc _ ⟨_, rfl⟩

Depends on / 依赖: OmegaCompletePartialOrder, OmegaCompletePartialOrder.subtype, continuous, f.continuous, g.continuous, subtype
-/
instance omegaCompletePartialOrderEqualizer {α β : Type*} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f g : α ->𝒄 β) :
    OmegaCompletePartialOrder { a : α // f a = g a } :=
  OmegaCompletePartialOrder.subtype _ fun c hc => by
    rw [f.continuous]; rw [g.continuous]
    congr 1
    ext x
    apply hc _ ⟨_, rfl⟩

namespace HasEqualizers

/--
Definition of `equalizerι` / `equalizerι` 的定义

English:
definition equalizerι
  signature: {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
  body: .mk (OrderHom.Subtype.val _) fun _ => rfl

中文:
定义 equalizerι
  签名: {α β : 类型} [OmegaCompletePartial序 α] [OmegaCompletePartial序 β]
  定义体: .mk (OrderHom.Subtype.val _) fun _ => rfl

Depends on / 依赖: OrderHom, OrderHom.Subtype.val, Subtype
-/
def equalizerι {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α ->𝒄 β) : { a : α // f a = g a } ->𝒄 α :=
  .mk (OrderHom.Subtype.val _) fun _ => rfl

/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  signature: {X Y : ωCPO.{v}} (f g : X ⟶ Y)
  body: Fork.ofι (P := ωCPO.of { a // f a = g a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)

中文:
定义 equalizer
  签名: {X Y : ωCPO.{v}} (f g : X ⟶ Y)
  定义体: Fork.ofι (P := ωCPO.of { a // f a = g a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)

Depends on / 依赖: CPO.of, ContinuousHom, ContinuousHom.ext, Fork.of
-/
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := ωCPO.of { a // f a = g a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)

/--
Definition of `isEqualizer` / `isEqualizer` 的定义

English:
definition isEqualizer
  signature: {X Y : ωCPO.{v}} (f g : X ⟶ Y)
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨{ toFun := fun x => ⟨s.ι x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun _ _ h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      ext x : 2; apply Subtype.ext ?_ -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
      apply ContinuousHom.congr_fun hm⟩

中文:
定义 isEqualizer
  签名: {X Y : ωCPO.{v}} (f g : X ⟶ Y)
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨{ toFun := fun x => ⟨s.ι x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun _ _ h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      ext x : 2; apply Subtype.ext ?_ -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
      apply ContinuousHom.congr_fun hm⟩

Depends on / 依赖: ContinuousHom, ContinuousHom.congr_fun, Fork.IsLimit.mk, IsLimit, Originally, Porting, Subtype, Subtype.ext, community, condition, congr_fun, continuous, github, github.com, issues, leanprover, mathlib4, monotone, s.condition
-/
def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨{ toFun := fun x => ⟨s.ι x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun _ _ h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      ext x : 2; apply Subtype.ext ?_ -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
      apply ContinuousHom.congr_fun hm⟩

end HasEqualizers

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasProducts.{v} ωCPO.{v}
  body: fun _ => { has_limit := fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm }

中文:
实例 :
  签名: HasProducts.{v} ωCPO.{v}
  定义体: fun _ => { has_limit := fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm }

Depends on / 依赖: Discrete, Discrete.natIsoFunctor.symm, hasLimit_of_iso, has_limit, natIsoFunctor
-/
instance : HasProducts.{v} ωCPO.{v} :=
  fun _ => { has_limit := fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm }

instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_, HasEqualizers.isEqualizer f g⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasEqualizers ωCPO.{v}
  body: hasEqualizers_of_hasLimit_parallelPair _

中文:
实例 :
  签名: HasEqualizers ωCPO.{v}
  定义体: hasEqualizers_of_hasLimit_parallelPair _

Depends on / 依赖: hasEqualizers_of_hasLimit_parallelPair
-/
instance : HasEqualizers ωCPO.{v} :=
  hasEqualizers_of_hasLimit_parallelPair _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits ωCPO.{v}
  body: has_limits_of_hasEqualizers_and_products

中文:
实例 :
  签名: 有极限 ωCPO.{v}
  定义体: has_limits_of_hasEqualizers_and_products

Depends on / 依赖: has_limits_of_hasEqualizers_and_products
-/
instance : HasLimits ωCPO.{v} :=
  has_limits_of_hasEqualizers_and_products

end

end ωCPO
