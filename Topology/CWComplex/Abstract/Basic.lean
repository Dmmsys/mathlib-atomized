/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young, Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# CW-complexes

This file defines (relative) CW-complexes using a categorical approach.

## Main definitions

* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
  `sk i` (called the $(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an
  arbitrary topological space, and each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from
  `sk n` (i.e., the $(n-1)$-skeleton) by attaching `n`-disks.

* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty.

## Implementation Notes

This file provides a categorical approach to CW complexes,
defining them via colimits and transfinite compositions.
For a classical approach that defines CW complexes via explicit cells and attaching maps,
see `Mathlib/Topology/CWComplex/Classical/Basic.lean`.
The two approaches are equivalent but serve different purposes:
* This approach is more suitable for categorical arguments and generalizations
* The classical approach is more convenient for concrete geometric arguments

## References

* [R. Fritsch and R. Piccinini, *Cellular Structures in Topology*][fritsch-piccinini1990]

## TODO

* Prove the equivalence between this categorical approach and the classical approach in
  `Mathlib/Topology/CWComplex/Classical/Basic.lean`.
  Currently there is no way to move between the two definitions.
-/

public section

open TopCat


universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace TopCat

namespace RelativeCWComplex

/-- For each `n : ℕ`, this is the family of morphisms which sends the unique
element of `Unit` to `diskBoundaryInclusion n : ∂𝔻 n ⟶ 𝔻 n`. -/
@[nolint unusedArguments]
/--
Definition of `basicCell` / `basicCell` 的定义

English:
abbreviation basicCell
  signature: (n : Nat) (_ : Unit)
  body: diskBoundaryInclusion n

中文:
缩写 basicCell
  签名: (n : 自然数) (_ : Unit)
  定义体: diskBoundaryInclusion n

Depends on / 依赖: diskBoundaryInclusion
-/
abbrev basicCell (n : Nat) (_ : Unit) : ∂𝔻 n ⟶ 𝔻 n := diskBoundaryInclusion n

end RelativeCWComplex

open RelativeCWComplex in
/--
Definition of `RelativeCWComplex` / `RelativeCWComplex` 的定义

English:
abbreviation RelativeCWComplex
  signature: {X Y : TopCat.{u}} (f : X ⟶ Y)
  body: RelativeCellComplex.{u} basicCell f

中文:
缩写 RelativeCWComplex
  签名: {X Y : TopCat.{u}} (f : X ⟶ Y)
  定义体: RelativeCellComplex.{u} basicCell f

Depends on / 依赖: RelativeCellComplex, basicCell
-/
abbrev RelativeCWComplex {X Y : TopCat.{u}} (f : X ⟶ Y) := RelativeCellComplex.{u} basicCell f

/--
Definition of `CWComplex` / `CWComplex` 的定义

English:
abbreviation CWComplex
  signature: (X : TopCat.{u})
  body: RelativeCWComplex (initial.to X)

中文:
缩写 CWComplex
  签名: (X : TopCat.{u})
  定义体: RelativeCWComplex (initial.to X)

Depends on / 依赖: RelativeCWComplex, initial, initial.to
-/
abbrev CWComplex (X : TopCat.{u}) := RelativeCWComplex (initial.to X)

end TopCat
