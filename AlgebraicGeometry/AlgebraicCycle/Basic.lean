/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.LocallyFinsupp.Pushforward
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

## Implementation notes

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in `Function.locallyFinsupp`, hence the slightly
nonstandard definition.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u v
variable {X Y : Scheme.{u}} {R : Type*}

/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support (see the module docstring for more details).

Note: currently this is an abbrev to save some effort in duplicating API. This seems fine for now,
but be aware of this if there is ever an instance clash involving algebraic cycles.
-/
@[stacks 02QR]
/--
Definition of `AlgebraicCycle` / `AlgebraicCycle` 的定义

English:
abbreviation AlgebraicCycle
  signature: (X : Scheme.{u}) (R : Type*) [Zero R]
  body: Function.locallyFinsupp X R

中文:
缩写 AlgebraicCycle
  签名: (X : 概形.{u}) (R : 类型) [零 R]
  定义体: Function.locallyFinsupp X R

Depends on / 依赖: Function, Function.locallyFinsupp, locallyFinsupp
-/
abbrev AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R] :=
  Function.locallyFinsupp X R

variable (f : X ⟶ Y) [Semiring R] (c : AlgebraicCycle X R) (x : X) (z : Y)
namespace AlgebraicCycle

/--
Implementation detail for `AlgebraicCycle.map`: function used to define the coefficient of the
pushforward of a cycle `c` at a point `z = f x`.
-/
@[stacks 02R3]
/--
Definition of `mapCoeff` / `mapCoeff` 的定义

English:
definition mapCoeff
  signature: {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X -> N)
  body: if wx x = wy (f.base x) then f.residueDegree x else 0

中文:
定义 mapCoeff
  签名: {N : 类型} [DecidableEq N] {Y : 概形} (f : X ⟶ Y) (wx : X -> N)
  定义体: if wx x = wy (f.base x) then f.residueDegree x else 0

Depends on / 依赖: f.base, f.residueDegree, residueDegree
-/
noncomputable def mapCoeff {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X -> N)
    (wy : Y -> N) (x : X) : Nat := if wx x = wy (f.base x) then f.residueDegree x else 0

/--
The pushforward of algebraic cycles with respect to a quasicompact morphism of schemes. The
arguments `wx` and `wy` are certain weight functions used to calculate how the weights of the
algebraic cycle should be adjusted to make the pushforward operation functorial. Typically in
applications these will be some notions of dimension or codimension. The most common notion of
dimension is `Order.height`, and the most common notion of codimension is `Order.coheight`, though
more sophisticated notions exist in the literature which are useful when sufficient
equidimensionality hypotheses cannot be assumed.
-/
@[stacks 02R3]
noncomputable
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X -> N) (wy : Y -> N)
  body: Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapCoeff f wx wy ·) f.isSpectralMap c

@[simp]

中文:
定义 map
  签名: [拟紧 f] {N : 类型} [DecidableEq N] (wx : X -> N) (wy : Y -> N)
  定义体: Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapCoeff f wx wy ·) f.isSpectralMap c

@[simp]

Depends on / 依赖: Function, Function.locallyFinsupp.map, Nat.cast, f.isSpectralMap, isSpectralMap, locallyFinsupp, mapCoeff
-/
def map [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X -> N) (wy : Y -> N)
    (c : AlgebraicCycle X R) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapCoeff f wx wy ·) f.isSpectralMap c

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: {N : Type*} [DecidableEq N] (wx : X -> N) (c : AlgebraicCycle X R)
  proof: by
  apply Function.locallyFinsupp.map_id
  simp [mapCoeff]

中文:
引理 map_id
  条件: {N : 类型} [DecidableEq N] (wx : X -> N) (c : AlgebraicCycle X R)
  证明: by
  apply Function.locallyFinsupp.map_id
  simp [mapCoeff]

Depends on / 依赖: Function, Function.locallyFinsupp.map_id, locallyFinsupp, mapCoeff, map_id
-/
lemma map_id {N : Type*} [DecidableEq N] (wx : X -> N) (c : AlgebraicCycle X R) :
    map (𝟙 _) wx wx c = c := by
  apply Function.locallyFinsupp.map_id
  simp [mapCoeff]

end AlgebraicGeometry.AlgebraicCycle
