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

/--
Definition of `presheafToTypes` / `presheafToTypes` 的定义

English:
definition presheafToTypes
  signature: (T : X -> Type*)
  body: forall x : U.unop, T x
  map {_ V} i := ↾fun (g) (x : V.unop) => g (i.unop x)

@[simp]

中文:
定义 presheafToTypes
  签名: (T : X -> 类型)
  定义体: forall x : U.unop, T x
  map {_ V} i := ↾fun (g) (x : V.unop) => g (i.unop x)

@[simp]

Depends on / 依赖: U.unop
-/
def presheafToTypes (T : X -> Type*) : X.Presheaf (Type _) where
  obj U := forall x : U.unop, T x
  map {_ V} i := ↾fun (g) (x : V.unop) => g (i.unop x)

@[simp]
/--
theorem `presheafToTypes_obj` / 定理 `presheafToTypes_obj`

English:
theorem presheafToTypes_obj
  given: {T : X -> Type*} {U : (Opens X)ᵒᵖ}
  proof: rfl

@[simp]

中文:
定理 presheafToTypes_obj
  条件: {T : X -> 类型} {U : (Opens X)ᵒᵖ}
  证明: rfl

@[simp]
-/
theorem presheafToTypes_obj {T : X -> Type*} {U : (Opens X)ᵒᵖ} :
    (presheafToTypes X T).obj U = forall x : U.unop, T x :=
  rfl

@[simp]
/--
theorem `presheafToTypes_map` / 定理 `presheafToTypes_map`

English:
theorem presheafToTypes_map
  given: {T : X -> Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f}
  proof: rfl

中文:
定理 presheafToTypes_map
  条件: {T : X -> 类型} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f}
  证明: rfl
-/
theorem presheafToTypes_map {T : X -> Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    dsimp% (presheafToTypes X T).map i f = fun x => f (i.unop x) :=
  rfl

-- We don't just define this in terms of `presheafToTypes`,
-- as it's helpful later to see (at a syntactic level) that `(presheafToType X T).obj U`
-- is a non-dependent function.
-- We don't use `@[simps]` to generate the projection lemmas here,
-- as it turns out to be useful to have `presheafToType_map`
-- written as an equality of functions (rather than being applied to some argument).
/--
Definition of `presheafToType` / `presheafToType` 的定义

English:
definition presheafToType
  signature: (T : Type*)
  body: U.unop -> T
  map {_ _} i := ↾fun g => g ∘ i.unop

@[simp]

中文:
定义 presheafToType
  签名: (T : 类型)
  定义体: U.unop -> T
  map {_ _} i := ↾fun g => g ∘ i.unop

@[simp]

Depends on / 依赖: U.unop
-/
def presheafToType (T : Type*) : X.Presheaf (Type _) where
  obj U := U.unop -> T
  map {_ _} i := ↾fun g => g ∘ i.unop

@[simp]
/--
theorem `presheafToType_obj` / 定理 `presheafToType_obj`

English:
theorem presheafToType_obj
  given: {T : Type*} {U : (Opens X)ᵒᵖ}
  proof: rfl

@[simp]

中文:
定理 presheafToType_obj
  条件: {T : 类型} {U : (Opens X)ᵒᵖ}
  证明: rfl

@[simp]
-/
theorem presheafToType_obj {T : Type*} {U : (Opens X)ᵒᵖ} :
    (presheafToType X T).obj U = (U.unop -> T) :=
  rfl

@[simp]
/--
theorem `presheafToType_map` / 定理 `presheafToType_map`

English:
theorem presheafToType_map
  given: {T : Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f}
  proof: rfl

中文:
定理 presheafToType_map
  条件: {T : 类型} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f}
  证明: rfl
-/
theorem presheafToType_map {T : Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    dsimp% (presheafToType X T).map i f = f ∘ i.unop :=
  rfl

/--
Definition of `presheafToTop` / `presheafToTop` 的定义

English:
definition presheafToTop
  signature: (T : TopCat)
  body: (Opens.toTopCat X).op ⋙ yoneda.obj T

@[simp]

中文:
定义 presheafToTop
  签名: (T : TopCat)
  定义体: (Opens.toTopCat X).op ⋙ yoneda.obj T

@[simp]

Depends on / 依赖: Opens.toTopCat, toTopCat, yoneda, yoneda.obj
-/
def presheafToTop (T : TopCat) : X.Presheaf (Type _) :=
  (Opens.toTopCat X).op ⋙ yoneda.obj T

@[simp]
/--
theorem `presheafToTop_obj` / 定理 `presheafToTop_obj`

English:
theorem presheafToTop_obj
  given: (T : TopCat) (U : (Opens X)ᵒᵖ)
  proof: rfl

中文:
定理 presheafToTop_obj
  条件: (T : TopCat) (U : (Opens X)ᵒᵖ)
  证明: rfl
-/
theorem presheafToTop_obj (T : TopCat) (U : (Opens X)ᵒᵖ) :
    (presheafToTop X T).obj U = ((Opens.toTopCat X).obj (unop U) ⟶ T) :=
  rfl

end TopCat
