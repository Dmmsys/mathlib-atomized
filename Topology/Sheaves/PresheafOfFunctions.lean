/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheafToTypes X T`, where `T : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheafToType X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheafToTop X T`, where `T : TopCat`,
  is the presheaf of continuous functions into a topological space `T`
* `presheafToTopCommRing X R`, where `R : TopCommRingCat`
  is the presheaf valued in `CommRing` of functions into a topological ring `R`
* as an example of the previous construction,
  `presheafToTopCommRing X (TopCommRingCat.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace TopCat

variable (X : TopCat)

/-- The presheaf of dependently typed functions on `X`, with fibres given by a type family `T`.
There is no requirement that the functions are continuous, here.
-/
/-
**TopCat.presheafToTypes** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：presheafToTypes (T : X -> Type*) : X.Presheaf (Type _) where obj U
参数：T : X -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf of dependently typed functions on `X`, with fibres given by a type 
family `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToTypes (T : X → Type*) : X.Presheaf (Type _) where
  obj U := ∀ x : U.unop, T x
  map {_ V} i := ↾fun (g) (x : V.unop) => g (i.unop x)

@[simp]
/-
**TopCat.presheafToTypes_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：presheafToTypes_obj {T : X -> Type*} {U : (Opens X)ᵒᵖ} : (presheafToTypes 
X T).obj U = forall x : U.unop, T x
参数：Opens X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem presheafToTypes_obj {T : X → Type*} {U : (Opens X)ᵒᵖ} :
    (presheafToTypes X T).obj U = ∀ x : U.unop, T x :=
  rfl

@[simp]
/-
**TopCat.presheafToTypes_map** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：presheafToTypes_map {T : X -> Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
 dsimp% (presheafToTypes X T).map i f = fun x => f (i.unop x)
参数：Opens X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem presheafToTypes_map {T : X → Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    dsimp% (presheafToTypes X T).map i f = fun x => f (i.unop x) :=
  rfl

-- We don't just define this in terms of `presheafToTypes`,
-- as it's helpful later to see (at a syntactic level) that `(presheafToType X T).obj U`
-- is a non-dependent function.
-- We don't use `@[simps]` to generate the projection lemmas here,
-- as it turns out to be useful to have `presheafToType_map`
-- written as an equality of functions (rather than being applied to some argument).
/-- The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
/-
**TopCat.presheafToType** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：presheafToType (T : Type*) : X.Presheaf (Type _) where obj U
参数：T : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToType (T : Type*) : X.Presheaf (Type _) where
  obj U := U.unop → T
  map {_ _} i := ↾fun g ↦ g ∘ i.unop

@[simp]
/-
**TopCat.presheafToType_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：presheafToType_obj {T : Type*} {U : (Opens X)ᵒᵖ} : (presheafToType X T).ob
j U = (U.unop -> T)
参数：Opens X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem presheafToType_obj {T : Type*} {U : (Opens X)ᵒᵖ} :
    (presheafToType X T).obj U = (U.unop → T) :=
  rfl

@[simp]
/-
**TopCat.presheafToType_map** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：presheafToType_map {T : Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} : dsimp
% (presheafToType X T).map i f = f ∘ i.unop
参数：Opens X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem presheafToType_map {T : Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    dsimp% (presheafToType X T).map i f = f ∘ i.unop :=
  rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space
`T`. -/
/-
**TopCat.presheafToTop** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：presheafToTop (T : TopCat) : X.Presheaf (Type _)
参数：T : TopCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf of continuous functions on `X` with values in fixed target topologi
cal space
`T`.
-/
def presheafToTop (T : TopCat) : X.Presheaf (Type _) :=
  (Opens.toTopCat X).op ⋙ yoneda.obj T

@[simp]
/-
**TopCat.presheafToTop_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：presheafToTop_obj (T : TopCat) (U : (Opens X)ᵒᵖ) : (presheafToTop X T).obj
 U = ((Opens.toTopCat X).obj (unop U) ⟶ T)
参数：T : TopCat；U : (Opens X)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem presheafToTop_obj (T : TopCat) (U : (Opens X)ᵒᵖ) :
    (presheafToTop X T).obj U = ((Opens.toTopCat X).obj (unop U) ⟶ T) :=
  rfl

end TopCat

