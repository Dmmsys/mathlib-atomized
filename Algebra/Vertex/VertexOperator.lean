/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Vertex.HVertexOperator
public import Mathlib.Data.Int.Interval

/-!
# Vertex operators

In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
* `VertexOperator` is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* `VertexOperator.ncoeff` is the coefficient of a vertex operator under normalized indexing.

## TODO
* `HasseDerivative` : A divided-power derivative.
* `Locality` : A weak form of commutativity.
* `Residue products` : A family of products on `VertexOperator R V` parametrized by integers.

## References
* [G. Mason, *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
-/

@[expose] public section

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/--
Definition of `VertexOperator` / `VertexOperator` 的定义

English:
abbreviation VertexOperator
  signature: (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
  body: HVertexOperator Int R V V

中文:
缩写 VertexOperator
  签名: (R : 类型) (V : 类型) [交换环 R] [加法交换群 V]
  定义体: HVertexOperator Int R V V

Depends on / 依赖: HVertexOperator
-/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := HVertexOperator Int R V V

namespace VertexOperator

open HVertexOperator

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (A B : VertexOperator R V) (h : forall v : V, A v = B v)
  proof: LinearMap.ext h

中文:
定理 ext
  条件: (A B : VertexOperator R V) (h : 对任意 v : V, A v = B v)
  证明: LinearMap.ext h

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem ext (A B : VertexOperator R V) (h : forall v : V, A v = B v) :
    A = B := LinearMap.ext h

/--
Definition of `ncoeff` / `ncoeff` 的定义

English:
definition ncoeff
  signature: : VertexOperator R V ->ₗ[R] Int -> Module.End R V where
  body: HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

中文:
定义 ncoeff
  签名: : VertexOperator R V ->ₗ[R] 整数 -> 模.End R V where
  定义体: HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

Depends on / 依赖: HVertexOperator, HVertexOperator.coeff
-/
def ncoeff : VertexOperator R V ->ₗ[R] Int -> Module.End R V where
  toFun A n := HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
theorem `ncoeff_apply` / 定理 `ncoeff_apply`

English:
theorem ncoeff_apply
  given: (A : VertexOperator R V) (n : Int)
  statement: ncoeff A n = coeff A (-n - 1)
  proof: rfl

中文:
定理 ncoeff_apply
  条件: (A : VertexOperator R V) (n : 整数)
  结论: ncoeff A n = coeff A (-n - 1)
  证明: rfl
-/
theorem ncoeff_apply (A : VertexOperator R V) (n : Int) : ncoeff A n = coeff A (-n - 1) :=
  rfl

/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

@[simp]
/--
theorem `coeff_eq_ncoeff` / 定理 `coeff_eq_ncoeff`

English:
theorem coeff_eq_ncoeff
  statement: (A : VertexOperator R V)
  proof: by
  rw [ncoeff_apply]; rw [neg_sub]; rw [Int.sub_neg]; rw [add_sub_cancel_left]

中文:
定理 coeff_eq_ncoeff
  结论: (A : VertexOperator R V)
  证明: by
  rw [ncoeff_apply]; rw [neg_sub]; rw [Int.sub_neg]; rw [add_sub_cancel_left]

Depends on / 依赖: Int.sub_neg, add_sub_cancel_left, ncoeff_apply, neg_sub, sub_neg
-/
theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : Int) : HVertexOperator.coeff A n = A[[-n - 1]] := by
  rw [ncoeff_apply]; rw [neg_sub]; rw [Int.sub_neg]; rw [add_sub_cancel_left]

/--
theorem `ncoeff_eq_zero_of_lt_order` / 定理 `ncoeff_eq_zero_of_lt_order`

English:
theorem ncoeff_eq_zero_of_lt_order
  statement: (A : VertexOperator R V) (n : Int) (x : V)
  proof: by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

中文:
定理 ncoeff_eq_zero_of_lt_order
  结论: (A : VertexOperator R V) (n : 整数) (x : V)
  证明: by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

Depends on / 依赖: AddHom, AddHom.coe_mk, HVertexOperator, HVertexOperator.coeff, HahnSeries, HahnSeries.coeff_eq_zero_of_lt_order, LinearMap, LinearMap.coe_mk, coe_mk, coeff_eq_zero_of_lt_order, ncoeff
-/
theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : Int) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A[[n]]) x = 0 := by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

/--
theorem `coeff_eq_zero_of_lt_order` / 定理 `coeff_eq_zero_of_lt_order`

English:
theorem coeff_eq_zero_of_lt_order
  statement: (A : VertexOperator R V) (n : Int) (x : V)
  proof: by
  rw [coeff_eq_ncoeff]; rw [ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  lia

中文:
定理 coeff_eq_zero_of_lt_order
  结论: (A : VertexOperator R V) (n : 整数) (x : V)
  证明: by
  rw [coeff_eq_ncoeff]; rw [ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  lia

Depends on / 依赖: coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order
-/
theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : Int) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0 := by
  rw [coeff_eq_ncoeff]; rw [ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  lia

/--
Definition of `of_coeff` / `of_coeff` 的定义

English:
definition of_coeff
  signature: (f : Int -> Module.End R V)
  body: HVertexOperator.of_coeff f fun x => (BddBelow.isWF (hf x)).isPWO

@[simp]

中文:
定义 of_coeff
  签名: (f : 整数 -> 模.End R V)
  定义体: HVertexOperator.of_coeff f fun x => (BddBelow.isWF (hf x)).isPWO

@[simp]

Depends on / 依赖: BddBelow, BddBelow.isWF, HVertexOperator, HVertexOperator.of_coeff, of_coeff
-/
noncomputable def of_coeff (f : Int -> Module.End R V)
    (hf : forall x, BddBelow (Function.support fun y => f y x)) : VertexOperator R V :=
  HVertexOperator.of_coeff f fun x => (BddBelow.isWF (hf x)).isPWO

@[simp]
/--
theorem `of_coeff_apply_coeff` / 定理 `of_coeff_apply_coeff`

English:
theorem of_coeff_apply_coeff
  statement: (f : Int -> Module.End R V)
  proof: by
  rfl

@[simp]

中文:
定理 of_coeff_apply_coeff
  结论: (f : 整数 -> 模.End R V)
  证明: by
  rfl

@[simp]

Depends on / 依赖: Scheme, quasiCompact_of_isIso
-/
theorem of_coeff_apply_coeff (f : Int -> Module.End R V)
    (hf : forall x, BddBelow (Function.support fun y => f y x)) (x : V) (n : Int) :
    ((HahnModule.of R).symm ((of_coeff f hf) x)).coeff n = (f n) x := by
  rfl

@[simp]
/--
theorem `ncoeff_of_coeff` / 定理 `ncoeff_of_coeff`

English:
theorem ncoeff_of_coeff
  statement: (f : Int -> Module.End R V)
  proof: by
  ext v
  rw [ncoeff_apply]; rw [coeff_apply_apply]; rw [of_coeff_apply_coeff]

中文:
定理 ncoeff_of_coeff
  结论: (f : 整数 -> 模.End R V)
  证明: by
  ext v
  rw [ncoeff_apply]; rw [coeff_apply_apply]; rw [of_coeff_apply_coeff]

Depends on / 依赖: coeff_apply_apply, ncoeff_apply, of_coeff_apply_coeff
-/
theorem ncoeff_of_coeff (f : Int -> Module.End R V)
    (hf : forall x, BddBelow (Function.support fun y => f y x)) (n : Int) :
    (of_coeff f hf)[[n]] = f (-n - 1) := by
  ext v
  rw [ncoeff_apply]; rw [coeff_apply_apply]; rw [of_coeff_apply_coeff]

end VertexOperator
