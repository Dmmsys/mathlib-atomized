/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Countable.Small

/-!
# Countable categories

A category is countable in this sense if it has countably many objects and countably many morphisms.

-/

@[expose] public section

universe w v u

noncomputable section

namespace CategoryTheory

/-
**CategoryTheory.discreteCountable** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：discreteCountable {α : Type*} [Countable α] : Countable (Discrete α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance discreteCountable {α : Type*} [Countable α] : Countable (Discrete α) :=
  Countable.of_equiv α discreteEquiv.symm

/-- A category with countably many objects and morphisms. -/
/-
**CategoryTheory.CountableCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：CountableCategory (J : Type*) [Category* J] : Prop where countableObj : Co
untable J
参数：J : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with countably many objects and morphisms.
-/
class CountableCategory (J : Type*) [Category* J] : Prop where
  countableObj : Countable J := by infer_instance
  countableHom : ∀ j j' : J, Countable (j ⟶ j') := by infer_instance

attribute [instance] CountableCategory.countableObj CountableCategory.countableHom
/-
**CategoryTheory.countableCategoryDiscreteOfCountable** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
形式化陈述：∀ (J : Type u_1) [Countable J], CategoryTheory.CountableCategory (Category
Theory.Discrete J)
参数：J : Type u_1；CategoryTheory.Discrete J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance countableCategoryDiscreteOfCountable (J : Type*) [Countable J] :
    CountableCategory (Discrete J) where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type u} [Countable J] [Category* J] [Quiver.IsThin J] : CountableCategory J :=
  CountableCategory.mk inferInstance (fun _ _ ↦ ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CountableCategory ℕ where

namespace CountableCategory

variable (α : Type u) [Category.{v} α] [CountableCategory α]

/-- A countable category `α` is equivalent to a category with objects in `Type`. -/
/-
**CategoryTheory.CountableCategory.ObjAsType** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.CountableCategory`。
形式化陈述：ObjAsType : Type
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A countable category `α` is equivalent to a category with objects in `Type`.
-/
abbrev ObjAsType : Type :=
  InducedCategory α (equivShrink.{0} α).symm
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (ObjAsType α) := Countable.of_equiv α (equivShrink.{0} α)
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : ObjAsType α} : Countable (i ⟶ j) :=
  Countable.of_equiv _ InducedCategory.homEquiv.symm
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CountableCategory (ObjAsType α) where

/-- The constructed category is indeed equivalent to `α`. -/
/-
**CategoryTheory.CountableCategory.objAsTypeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.CountableCategory`。
形式化陈述：objAsTypeEquiv : ObjAsType α ≌ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The constructed category is indeed equivalent to `α`.
-/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

/-- A countable category `α` is equivalent to a *small* category with objects in `Type`. -/
/-
**CategoryTheory.CountableCategory.HomAsType** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.CountableCategory`。
形式化陈述：HomAsType
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A countable category `α` is equivalent to a *small* category with objects in `Ty
pe`.
-/
def HomAsType := ShrinkHoms (ObjAsType α)
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallySmall.{0} (ObjAsType α) where
  hom_small _ _ := inferInstance
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SmallCategory (HomAsType α) := inferInstanceAs <| SmallCategory (ShrinkHoms _)
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable (HomAsType α) := Countable.of_equiv α (equivShrink.{0} α)
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : HomAsType α} : Countable (i ⟶ j) :=
  Countable.of_equiv ((ShrinkHoms.equivalence _).inverse.obj i ⟶
    (ShrinkHoms.equivalence _).inverse.obj j)
    (Functor.FullyFaithful.ofFullyFaithful _).homEquiv.symm
/-
**CategoryTheory.CountableCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
untableCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CountableCategory (HomAsType α) where

/-- The constructed category is indeed equivalent to `α`. -/
/-
**CategoryTheory.CountableCategory.homAsTypeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.CountableCategory`。
形式化陈述：homAsTypeEquiv : HomAsType α ≌ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.CountableCategory.instLocallySmallObjAsType`：∀ (α : Type 
u) [inst : CategoryTheory.Category.{v, u} α] [inst_1 : CategoryTheory.CountableC
ategory α],   CategoryTheory.LocallySmall.{0, v,…

--- 原说明 ---
The constructed category is indeed equivalent to `α`.
-/
noncomputable def homAsTypeEquiv : HomAsType α ≌ α :=
  (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)

end CountableCategory

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [SmallCategory α] [FinCategory α] : CountableCategory α where

open Opposite

/-- The opposite of a countable category is countable. -/
/-
**CategoryTheory.countableCategoryOpposite** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：countableCategoryOpposite {J : Type*} [Category* J] [CountableCategory J] 
: CountableCategory Jᵒᵖ where countableObj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `CategoryTheory.CountableCategory.countableObj`：∀ {J : Type u_1} {inst : 
CategoryTheory.Category.{v_1, u_1} J} [self : CategoryTheory.CountableCategory J
], Countable J
· 使用定理 `CategoryTheory.CountableCategory.countableHom`：∀ {J : Type u_1} {inst : 
CategoryTheory.Category.{v_1, u_1} J} [self : CategoryTheory.CountableCategory J
] (j j' : J),   Countable (j ⟶ j')
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The opposite of a countable category is countable.
-/
instance countableCategoryOpposite {J : Type*} [Category* J] [CountableCategory J] :
    CountableCategory Jᵒᵖ where
  countableObj := Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm

attribute [local instance] uliftCategory in
/-- Applying `ULift` to morphisms and objects of a category preserves countability. -/
/-
**CategoryTheory.countableCategoryUlift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y`。
形式化陈述：countableCategoryUlift {J : Type v} [Category.{v} J] [CountableCategory J]
 : CountableCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where co
untableObj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableULift`：∀ {β : Type v} [Countable β], Countable (ULift.{u, v
} β)
· 使用定理 `CategoryTheory.CountableCategory.countableObj`：∀ {J : Type u_1} {inst : 
CategoryTheory.Category.{v_1, u_1} J} [self : CategoryTheory.CountableCategory J
], Countable J
· 使用定理 `CategoryTheory.CountableCategory.countableHom`：∀ {J : Type u_1} {inst : 
CategoryTheory.Category.{v_1, u_1} J} [self : CategoryTheory.CountableCategory J
] (j j' : J),   Countable (j ⟶ j')

--- 原说明 ---
Applying `ULift` to morphisms and objects of a category preserves countability.
-/
instance countableCategoryUlift {J : Type v} [Category.{v} J] [CountableCategory J] :
    CountableCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  countableObj := instCountableULift
  countableHom := fun i j =>
    have : Countable ((ULiftHom.objDown i).down ⟶ (ULiftHom.objDown j).down) := inferInstance
    instCountableULift

end CategoryTheory

