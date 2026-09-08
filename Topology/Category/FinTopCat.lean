/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Category of finite topological spaces

Definition of the category of finite topological spaces with the canonical
forgetful functors.

-/

@[expose] public section


universe u

open CategoryTheory

/-- A bundled finite topological space. -/
/-
**FinTopCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled finite topological space.
-/
structure FinTopCat where
  /-- carrier of a finite topological space. -/
  toTop : TopCat.{u} -- TODO: turn this into an `extends`?
  [fintype : Fintype toTop]

namespace FinTopCat

/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited FinTopCat :=
  ⟨{ toTop := TopCat.of PEmpty }⟩
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort FinTopCat (Type u) :=
  ⟨fun X => X.toTop⟩

attribute [instance] fintype
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category FinTopCat :=
  inferInstanceAs <| Category (InducedCategory _ toTop)
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory FinTopCat (C(·, ·)) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toTop) _

/-- Construct a bundled `FinTopCat` from the underlying type and the appropriate typeclasses. -/
/-
**FinTopCat.of** 是 Mathlib 中的一个定义，位于命名空间 `FinTopCat`。
形式化陈述：of (X : Type u) [Fintype X] [TopologicalSpace X] : FinTopCat where toTop
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `FinTopCat` from the underlying type and the appropriate typ
eclasses.
-/
def of (X : Type u) [Fintype X] [TopologicalSpace X] : FinTopCat where
  toTop := TopCat.of X
  fintype := ‹_›

@[simp]
/-
**FinTopCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `FinTopCat`。
形式化陈述：coe_of (X : Type u) [Fintype X] [TopologicalSpace X] : (of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [Fintype X] [TopologicalSpace X] :
    (of X : Type u) = X :=
  rfl

/-- The forgetful functor to `FintypeCat`. -/
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor to `FintypeCat`.
-/
instance : HasForget₂ FinTopCat FintypeCat :=
  HasForget₂.mk' (fun X ↦ .of X) (fun _ ↦ rfl)
    (fun f ↦ FintypeCat.homMk f) HEq.rfl
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FinTopCat) : TopologicalSpace ((forget₂ FinTopCat FintypeCat).obj X) :=
  inferInstanceAs <| TopologicalSpace X

/-- The forgetful functor to `TopCat`. -/
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor to `TopCat`.
-/
instance : HasForget₂ FinTopCat TopCat :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toTop) _
/-
**FinTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `FinTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FinTopCat) : Fintype ((forget₂ FinTopCat TopCat).obj X) :=
  X.fintype

end FinTopCat

namespace FintypeCatDiscrete

/-- Scoped topological space instance on objects of the category of finite types, assigning
the discrete topology. -/
/-
**FintypeCatDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCatDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scoped topological space instance on objects of the category of finite types, as
signing
the discrete topology.
-/
scoped instance (X : FintypeCat) : TopologicalSpace X := ⊥
/-
**FintypeCatDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCatDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (X : FintypeCat) : DiscreteTopology X := ⟨rfl⟩

/-- The forgetful functor from finite types to topological spaces, forgetting discreteness.
This is a scoped instance. -/
/-
**FintypeCatDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCatDiscrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from finite types to topological spaces, forgetting discre
teness.
This is a scoped instance.
-/
scoped instance : HasForget₂ FintypeCat TopCat where
  forget₂.obj X := TopCat.of X
  forget₂.map f := TopCat.ofHom ⟨f, continuous_of_discreteTopology⟩

end FintypeCatDiscrete

