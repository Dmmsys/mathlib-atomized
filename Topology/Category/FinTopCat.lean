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

/--
Definition of `FinTopCat` / `FinTopCat` 的定义

English:
structure FinTopCat
  parameters: where
  axioms and operations (2):
    - toTop : TopCat.{u} -- TODO: turn this into an `extends`?
    - [fintype : Fintype toTop]

中文:
结构 FinTopCat
  参数: where
  公理与运算 (2 个):
    - toTop : TopCat.{u} -- TODO: turn this into an `extends`?
    - [fintype : Fintype toTop]
-/
structure FinTopCat where
  /-- carrier of a finite topological space. -/
  toTop : TopCat.{u} -- TODO: turn this into an `extends`?
  [fintype : Fintype toTop]

namespace FinTopCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited FinTopCat
  body: ⟨{ toTop := TopCat.of PEmpty }⟩

中文:
实例 :
  签名: Inhabited FinTopCat
  定义体: ⟨{ toTop := TopCat.of PEmpty }⟩

Depends on / 依赖: PEmpty, TopCat, TopCat.of
-/
instance : Inhabited FinTopCat :=
  ⟨{ toTop := TopCat.of PEmpty }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort FinTopCat (Type u)
  body: ⟨fun X => X.toTop⟩

中文:
实例 :
  签名: CoeSort FinTopCat (类型u)
  定义体: ⟨fun X => X.toTop⟩

Depends on / 依赖: X.toTop
-/
instance : CoeSort FinTopCat (Type u) :=
  ⟨fun X => X.toTop⟩

attribute [instance] fintype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category FinTopCat
  body: inferInstanceAs Category (InducedCategory _ toTop)

中文:
实例 :
  签名: Category FinTopCat
  定义体: inferInstanceAs Category (InducedCategory _ toTop)

Depends on / 依赖: Category, InducedCategory
-/
instance : Category FinTopCat :=
inferInstanceAs Category (InducedCategory _ toTop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory FinTopCat (C(·, ·))
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

中文:
实例 :
  签名: ConcreteCategory FinTopCat (C(·, ·))
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

Depends on / 依赖: ConcreteCategory, InducedCategory
-/
instance : ConcreteCategory FinTopCat (C(·, ·)) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (X : Type u) [Fintype X] [TopologicalSpace X]
  body: TopCat.of X
  fintype := ‹_›

@[simp]

中文:
定义 of
  签名: (X : 类型u) [Fintype X] [TopologicalSpace X]
  定义体: TopCat.of X
  fintype := ‹_›

@[simp]

Depends on / 依赖: TopCat, TopCat.of
-/
def of (X : Type u) [Fintype X] [TopologicalSpace X] : FinTopCat where
  toTop := TopCat.of X
  fintype := ‹_›

@[simp]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [Fintype X] [TopologicalSpace X]
  proof: rfl

中文:
定理 coe_of
  条件: (X : 类型u) [Fintype X] [TopologicalSpace X]
  证明: rfl
-/
theorem coe_of (X : Type u) [Fintype X] [TopologicalSpace X] :
    (of X : Type u) = X :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ FinTopCat FintypeCat
  body: HasForget₂.mk' (fun X => .of X) (fun _ => rfl)
    (fun f => FintypeCat.homMk f) HEq.rfl

中文:
实例 :
  签名: HasForget₂ FinTopCat FintypeCat
  定义体: HasForget₂.mk' (fun X => .of X) (fun _ => rfl)
    (fun f => FintypeCat.homMk f) HEq.rfl

Depends on / 依赖: FintypeCat, FintypeCat.homMk, HEq.rfl
-/
instance : HasForget₂ FinTopCat FintypeCat :=
  HasForget₂.mk' (fun X => .of X) (fun _ => rfl)
    (fun f => FintypeCat.homMk f) HEq.rfl

instance (X : FinTopCat) : TopologicalSpace ((forget₂ FinTopCat FintypeCat).obj X) :=
inferInstanceAs TopologicalSpace X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ FinTopCat TopCat
  body: inferInstanceAs HasForget₂ (InducedCategory _ toTop) _

中文:
实例 :
  签名: HasForget₂ FinTopCat TopCat
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toTop) _

Depends on / 依赖: InducedCategory
-/
instance : HasForget₂ FinTopCat TopCat :=
inferInstanceAs HasForget₂ (InducedCategory _ toTop) _

instance (X : FinTopCat) : Fintype ((forget₂ FinTopCat TopCat).obj X) :=
  X.fintype

end FinTopCat

namespace FintypeCatDiscrete

/-- Scoped topological space instance on objects of the category of finite types, assigning
the discrete topology. -/
scoped instance (X : FintypeCat) : TopologicalSpace X := ⊥
scoped instance (X : FintypeCat) : DiscreteTopology X := ⟨rfl⟩

/-- The forgetful functor from finite types to topological spaces, forgetting discreteness.
This is a scoped instance. -/
scoped instance : HasForget₂ FintypeCat TopCat where
  forget₂.obj X := TopCat.of X
  forget₂.map f := TopCat.ofHom ⟨f, continuous_of_discreteTopology⟩

end FintypeCatDiscrete
