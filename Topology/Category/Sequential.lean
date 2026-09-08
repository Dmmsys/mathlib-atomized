/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Category.TopCat.Basic
/-!

# The category of sequential topological spaces

We define the category `Sequential` of sequential topological spaces. We follow the usual template
for defining categories of topological spaces, by giving it the induced category structure from
`TopCat`.
-/

@[expose] public section

open CategoryTheory

universe u

/-- The type sequential topological spaces. -/
/-
**Sequential** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type sequential topological spaces.
-/
structure Sequential where
  /-- The underlying topological space of an object of `Sequential`. -/
  toTop : TopCat.{u} -- TODO: turn this into `extends`
  /-- The underlying topological space is sequential. -/
  [is_sequential : SequentialSpace toTop]

namespace Sequential

/-
**Sequential.** 是 Mathlib 中的一个实例，位于命名空间 `Sequential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Sequential.{u} :=
  ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩
/-
**Sequential.** 是 Mathlib 中的一个实例，位于命名空间 `Sequential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Sequential Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_sequential
/-
**Sequential.** 是 Mathlib 中的一个实例，位于命名空间 `Sequential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category.{u, u + 1} Sequential.{u} :=
  inferInstanceAs <| Category (InducedCategory _ toTop)
/-
**Sequential.** 是 Mathlib 中的一个实例，位于命名空间 `Sequential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{u} Sequential.{u} (C(·, ·)) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toTop) _

variable (X : Type u) [TopologicalSpace X] [SequentialSpace X]

/-- Constructor for objects of the category `Sequential`. -/
/-
**Sequential.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Sequential`。
形式化陈述：of : Sequential.{u} where toTop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects of the category `Sequential`.
-/
abbrev of : Sequential.{u} where
  toTop := TopCat.of X
  is_sequential := ‹_›

/-- The fully faithful embedding of `Sequential` in `TopCat`. -/
@[simps!]
/-
**Sequential.sequentialToTop** 是 Mathlib 中的一个定义，位于命名空间 `Sequential`。
形式化陈述：sequentialToTop : Sequential.{u} ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful embedding of `Sequential` in `TopCat`.
-/
def sequentialToTop : Sequential.{u} ⥤ TopCat.{u} :=
  inducedFunctor _

/-- The functor to `TopCat` is indeed fully faithful. -/
/-
**Sequential.fullyFaithfulSequentialToTop** 是 Mathlib 中的一个定义，位于命名空间 `Sequential`
。
形式化陈述：fullyFaithfulSequentialToTop : sequentialToTop.FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to `TopCat` is indeed fully faithful.
-/
def fullyFaithfulSequentialToTop : sequentialToTop.FullyFaithful :=
  fullyFaithfulInducedFunctor _
/-
**Sequential.** 是 Mathlib 中的一个实例，位于命名空间 `Sequential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : sequentialToTop.{u}.Full :=
  inferInstanceAs (inducedFunctor _).Full
/-
**Sequential.** 是 Mathlib 中的一个实例，位于命名空间 `Sequential`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : sequentialToTop.{u}.Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
/-
**Sequential.isoOfHomeo** 是 Mathlib 中的一个定义，位于命名空间 `Sequential`。
形式化陈述：isoOfHomeo {X Y : Sequential.{u}} (f : X ≃ₜ Y) : X ≅ Y where hom
参数：f : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism from a homeomorphism.
-/
def isoOfHomeo {X Y : Sequential.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := InducedCategory.homMk (TopCat.ofHom ⟨f, f.continuous⟩)
  inv := InducedCategory.homMk (TopCat.ofHom ⟨f.symm, f.symm.continuous⟩)
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
/-
**Sequential.homeoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Sequential`。
形式化陈述：homeoOfIso {X Y : Sequential.{u}} (f : X ≅ Y) : X ≃ₜ Y where toFun
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a homeomorphism from an isomorphism.
-/
def homeoOfIso {X Y : Sequential.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

/-- The equivalence between isomorphisms in `Sequential` and homeomorphisms
of topological spaces. -/
@[simps]
/-
**Sequential.isoEquivHomeo** 是 Mathlib 中的一个定义，位于命名空间 `Sequential`。
形式化陈述：isoEquivHomeo {X Y : Sequential.{u}} : (X ≅ Y) ≃ (X ≃ₜ Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between isomorphisms in `Sequential` and homeomorphisms
of topological spaces.
-/
def isoEquivHomeo {X Y : Sequential.{u}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

end Sequential

