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
/-
**TopCat.RelativeCWComplex.basicCell** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Relativ
eCWComplex`。
形式化陈述：basicCell (n : Nat) (_ : Unit) : ∂𝔻 n ⟶ 𝔻 n
参数：n : Nat；_ : Unit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `n : ℕ`, this is the family of morphisms which sends the unique
element of `Unit` to `diskBoundaryInclusion n : ∂𝔻 n ⟶ 𝔻 n`.
-/
abbrev basicCell (n : ℕ) (_ : Unit) : ∂𝔻 n ⟶ 𝔻 n := diskBoundaryInclusion n

end RelativeCWComplex

open RelativeCWComplex in
/-- A relative CW-complex is a morphism `f : X ⟶ Y` equipped with data expressing
that `Y` identifies to the colimit of a functor `F : ℕ ⥤ TopCat` with that
`F.obj 0 ≅ X` and for any `n : ℕ`, `F.obj (n + 1)` is obtained from `F.obj n`
by attaching `n`-disks. -/
/-
**TopCat.RelativeCWComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：RelativeCWComplex {X Y : TopCat.{u}} (f : X ⟶ Y)
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ

--- 原说明 ---
A relative CW-complex is a morphism `f : X ⟶ Y` equipped with data expressing
that `Y` identifies to the colimit of a functor `F : ℕ ⥤ TopCat` with that
`F.obj 0 ≅ X` and for any `n : ℕ`, `F.obj (n + 1)` is obtained from `F.obj n`
by attaching `n`-disks.
-/
abbrev RelativeCWComplex {X Y : TopCat.{u}} (f : X ⟶ Y) := RelativeCellComplex.{u} basicCell f

/-- A CW-complex is a topological space such that `⊥_ _ ⟶ X` is a relative CW-complex. -/
/-
**TopCat.CWComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：CWComplex (X : TopCat.{u})
参数：X : TopCat.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW-complex is a topological space such that `⊥_ _ ⟶ X` is a relative CW-comple
x.
-/
abbrev CWComplex (X : TopCat.{u}) := RelativeCWComplex (initial.to X)

end TopCat

