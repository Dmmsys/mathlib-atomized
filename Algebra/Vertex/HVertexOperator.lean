/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Vertex operators

In this file we introduce heterogeneous vertex operators using Hahn series. When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field". The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.

## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.

## Main results
* Ext

## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.

## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

@[expose] public section

assert_not_exists Cardinal

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/--
Definition of `HVertexOperator` / `HVertexOperator` 的定义

English:
abbreviation HVertexOperator
  signature: (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
  body: V ->ₗ[R] (HahnModule Γ R W)

中文:
缩写 HVertexOperator
  签名: (Γ : 类型) [偏序 Γ] (R : 类型) [交换环 R]
  定义体: V ->ₗ[R] (HahnModule Γ R W)

Depends on / 依赖: HahnModule
-/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V ->ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (A B : HVertexOperator Γ R V W) (h : forall v : V, A v = B v)
  proof: LinearMap.ext h

中文:
定理 ext
  条件: (A B : HVertexOperator Γ R V W) (h : 对任意 v : V, A v = B v)
  证明: LinearMap.ext h

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem ext (A B : HVertexOperator Γ R V W) (h : forall v : V, A v = B v) :
    A = B := LinearMap.ext h

set_option backward.isDefEq.respectTransparency false in
/-- The coefficients of a heterogeneous vertex operator, viewed as a linear map to formal power
series with coefficients in linear maps. -/
@[simps]
/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: : HVertexOperator Γ R V W ->ₗ[R] Γ -> V ->ₗ[R] W where
  body: {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

中文:
定义 coeff
  签名: : HVertexOperator Γ R V W ->ₗ[R] Γ -> V ->ₗ[R] W where
  定义体: {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
-/
def coeff : HVertexOperator Γ R V W ->ₗ[R] Γ -> V ->ₗ[R] W where
  toFun A n := {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
theorem `coeff_isPWOsupport` / 定理 `coeff_isPWOsupport`

English:
theorem coeff_isPWOsupport
  given: (A : HVertexOperator Γ R V W) (v : V)
  proof: ((of R).symm (A v)).isPWO_support'

@[ext]

中文:
定理 coeff_isPWOsupport
  条件: (A : HVertexOperator Γ R V W) (v : V)
  证明: ((of R).symm (A v)).isPWO_support'

@[ext]

Depends on / 依赖: IsFinite, IsProper, isPWO_support
-/
theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

@[ext]
/--
theorem `coeff_inj` / 定理 `coeff_inj`

English:
theorem coeff_inj
  statement: Function.Injective (coeff : HVertexOperator Γ R V W ->ₗ[R] Γ -> (V ->ₗ[R] W))
  proof: by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

中文:
定理 coeff_inj
  结论: 函数.单射 (coeff : HVertexOperator Γ R V W ->ₗ[R] Γ -> (V ->ₗ[R] W))
  证明: by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

Depends on / 依赖: DFunLike, DFunLike.coe
-/
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W ->ₗ[R] Γ -> (V ->ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

set_option backward.isDefEq.respectTransparency false in
/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
/--
Definition of `of_coeff` / `of_coeff` 的定义

English:
definition of_coeff
  signature: (f : Γ -> V ->ₗ[R] W) (hf : forall (x : V), (Function.support (f · x)).IsPWO)
  body: (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

中文:
定义 of_coeff
  签名: (f : Γ -> V ->ₗ[R] W) (hf : 对任意 (x : V), (函数.support (f · x)).IsPWO)
  定义体: (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

Depends on / 依赖: isPWO_support
-/
def of_coeff (f : Γ -> V ->ₗ[R] W) (hf : forall (x : V), (Function.support (f · x)).IsPWO) :
    HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/--
theorem `coeff_of_coeff` / 定理 `coeff_of_coeff`

English:
theorem coeff_of_coeff
  statement: (f : Γ -> V ->ₗ[R] W)
  proof: rfl

@[simp]

中文:
定理 coeff_of_coeff
  结论: (f : Γ -> V ->ₗ[R] W)
  证明: rfl

@[simp]
-/
theorem coeff_of_coeff (f : Γ -> V ->ₗ[R] W)
    (hf : forall (x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

@[simp]
/--
theorem `of_coeff_coeff` / 定理 `of_coeff_coeff`

English:
theorem of_coeff_coeff
  given: (A : HVertexOperator Γ R V W)
  statement: of_coeff A.coeff A.coeff_isPWOsupport = A
  proof: rfl

中文:
定理 of_coeff_coeff
  条件: (A : HVertexOperator Γ R V W)
  结论: of_coeff A.coeff A.coeff_isPWOsupport = A
  证明: rfl
-/
theorem of_coeff_coeff (A : HVertexOperator Γ R V W) : of_coeff A.coeff A.coeff_isPWOsupport = A :=
  rfl

end Coeff

section Products

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

open HahnModule

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
series. -/
@[simps]
/--
Definition of `compHahnSeries` / `compHahnSeries` 的定义

English:
definition compHahnSeries
  signature: (u : U)
  body: A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [coeff_apply_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    exact hg' (by simp [hAB])

中文:
定义 compHahnSeries
  签名: (u : U)
  定义体: A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [coeff_apply_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    exact hg' (by simp [hAB])

Depends on / 依赖: IsFinite, IsProper
-/
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [coeff_apply_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    exact hg' (by simp [hAB])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `compHahnSeries_add` / 定理 `compHahnSeries_add`

English:
theorem compHahnSeries_add
  given: (u v : U)
  proof: by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

中文:
定理 compHahnSeries_add
  条件: (u v : U)
  证明: by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

Depends on / 依赖: HahnSeries, HahnSeries.coeff_add, Pi.add_apply, add_apply, coeff_add, coeff_apply_apply, compHahnSeries_coeff, map_add
-/
theorem compHahnSeries_add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `compHahnSeries_smul` / 定理 `compHahnSeries_smul`

English:
theorem compHahnSeries_smul
  given: (r : R) (u : U)
  proof: by
  ext
  simp only [compHahnSeries_coeff, map_smul, coeff_apply_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

中文:
定理 compHahnSeries_smul
  条件: (r : R) (u : U)
  证明: by
  ext
  simp only [compHahnSeries_coeff, map_smul, coeff_apply_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

Depends on / 依赖: HahnSeries, HahnSeries.coeff_smul, coeff_apply_apply, coeff_smul, compHahnSeries_coeff, map_smul
-/
theorem compHahnSeries_smul (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  simp only [compHahnSeries_coeff, map_smul, coeff_apply_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : HVertexOperator (Γ' ×ₗ Γ) R U W where
  body: HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp [HahnSeries.ofIterate]
  map_smul' := by
    intro r x
    ext g
    simp [HahnSeries.ofIterate]

@[simp]

中文:
定义 comp
  签名: : HVertexOperator (Γ' ×ₗ Γ) R U W where
  定义体: HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp [HahnSeries.ofIterate]
  map_smul' := by
    intro r x
    ext g
    simp [HahnSeries.ofIterate]

@[simp]

Depends on / 依赖: HahnModule, HahnModule.of, HahnSeries, HahnSeries.ofIterate, compHahnSeries, ofIterate
-/
def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp [HahnSeries.ofIterate]
  map_smul' := by
    intro r x
    ext g
    simp [HahnSeries.ofIterate]

@[simp]
/--
theorem `coeff_comp` / 定理 `coeff_comp`

English:
theorem coeff_comp
  given: (g : Γ' ×ₗ Γ)
  proof: by
  rfl

中文:
定理 coeff_comp
  条件: (g : Γ' ×ₗ Γ)
  证明: by
  rfl
-/
theorem coeff_comp (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

end Products

end HVertexOperator
