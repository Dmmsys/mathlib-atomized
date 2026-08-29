/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Ring.Associator
public import Mathlib.GroupTheory.GroupAction.Ring
/-!
# Pre-Lie rings and algebras

In this file we introduce left and right pre-Lie rings, defined as a `NonUnitalNonAssocRing` where
the associator `associator x y z := (x * y) * z - x * (y * z)` is left or right symmetric,
respectively.

We prove that every `Left(Right)PreLieRing L` is a `Right(Left)PreLieRing L` with
the opposite `mul`. The equivalence is simple given by `op : L ≃* Lᵐᵒᵖ`.

Everything holds for the algebra versions where `L` is also an `R`-Module over a commutative ring
`R`.

## Main definitions
  All are a defined as a `NonUnitalNonAssocRing` whose `associator` satisfies an identity.
  * `LeftPreLieRing`
  * `RightPreLieRing`
  * `LeftPreLieAlgebra`
  * `RightPreLieAlgebra`

## Main results
  * Every `LeftPreLieRing` is a `RightPreLieRing` with the opposite multiplication.

## Implementation notes
There are left and right versions of the structures, equivalent via `ᵐᵒᵖ`.
Perhaps one could be favored but there is no real reason to.

## References
[F. Chapoton, M. Livernet, *Pre-Lie algebras and the rooted trees operad*][chapoton_livernet_2001]
[D. Manchon, *A short survey on pre-Lie algebras*][manchon_2011]
[J.-M. Oudom, D. Guin, *On the Lie enveloping algebra of a pre-Lie algebra*][oudom_guin_2008]
<https://ncatlab.org/nlab/show/pre-Lie+algebra>
-/

public section

/-- `LeftPreLieRing`s are `NonUnitalNonAssocRing`s such that the `associator` is symmetric in the
first two variables. -/
@[ext]
/--
Definition of `LeftPreLieRing` / `LeftPreLieRing` 的定义

English:
class LeftPreLieRing
  parameters: (L : Type*)
  extends: NonUnitalNonAssocRing L
  axioms and operations (1):
    - assoc_symm'((x y z : L)) : associator x y z = associator y x z

中文:
类 LeftPreLie环
  参数: (L : 类型)
  继承: 非幺非结合环 L
  公理与运算 (1 个):
    - assoc_symm'((x y z : L)) : associator x y z = associator y x z
-/
class LeftPreLieRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_symm' (x y z : L) : associator x y z = associator y x z

/-- `RightPreLieRing`s are `NonUnitalNonAssocRing`s such that the `associator` is symmetric in the
last two variables. -/
@[ext]
/--
Definition of `RightPreLieRing` / `RightPreLieRing` 的定义

English:
class RightPreLieRing
  parameters: (L : Type*)
  extends: NonUnitalNonAssocRing L
  axioms and operations (1):
    - assoc_symm'((x y z : L)) : associator x y z = associator x z y

中文:
类 RightPreLie环
  参数: (L : 类型)
  继承: 非幺非结合环 L
  公理与运算 (1 个):
    - assoc_symm'((x y z : L)) : associator x y z = associator x z y
-/
class RightPreLieRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_symm' (x y z : L) : associator x y z = associator x z y

section algebras

variable (R : Type*) [CommRing R]

/-- A `LeftPreLieAlgebra` is a `LeftPreLieRing` with an action of a `CommRing` satisfying
`r • x * y = r • (x * y)` and ` x * (r • y) = r • (x * y)`. -/
@[ext]
/--
Definition of `LeftPreLieAlgebra` / `LeftPreLieAlgebra` 的定义

English:
class LeftPreLieAlgebra
  parameters: (L : Type*) [LeftPreLieRing L]
  (no additional axioms)

中文:
类 LeftPreLie代数
  参数: (L : 类型) [LeftPreLie环 L]
  (无附加公理)
-/
class LeftPreLieAlgebra (L : Type*) [LeftPreLieRing L] : Type _ extends
  Module R L, IsScalarTower R L L, SMulCommClass R L L

/-- A `RightPreLieAlgebra` is a `RightPreLieRing` with an action of a `CommRing` satisfying
`r • x * y = r • (x * y)` and ` x * (r • y) = r • (x * y)`. -/
@[ext]
/--
Definition of `RightPreLieAlgebra` / `RightPreLieAlgebra` 的定义

English:
class RightPreLieAlgebra
  parameters: (L : Type*) [RightPreLieRing L]
  (no additional axioms)

中文:
类 RightPreLie代数
  参数: (L : 类型) [RightPreLie环 L]
  (无附加公理)
-/
class RightPreLieAlgebra (L : Type*) [RightPreLieRing L] : Type _ extends
  Module R L, IsScalarTower R L L, SMulCommClass R L L

end algebras

variable {R L : Type*} [CommRing R]

namespace LeftPreLieRing

variable [LeftPreLieRing L]

/--
theorem `assoc_symm` / 定理 `assoc_symm`

English:
theorem assoc_symm
  given: (x y z : L)
  proof: LeftPreLieRing.assoc_symm' x y z

中文:
定理 assoc_symm
  条件: (x y z : L)
  证明: LeftPreLieRing.assoc_symm' x y z

Depends on / 依赖: LeftPreLieRing, LeftPreLieRing.assoc_symm, assoc_symm
-/
theorem assoc_symm (x y z : L) :
    associator x y z = associator y x z := LeftPreLieRing.assoc_symm' x y z

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RightPreLieRing Lᵐᵒᵖ
  body: by
    simp [assoc_symm]

中文:
实例 :
  签名: RightPreLie环 Lᵐᵒᵖ
  定义体: by
    simp [assoc_symm]

Depends on / 依赖: assoc_symm
-/
instance : RightPreLieRing Lᵐᵒᵖ where
  assoc_symm' x y z := by
    simp [assoc_symm]

end LeftPreLieRing

namespace LeftPreLieAlgebra

variable [LeftPreLieRing L] [LeftPreLieAlgebra R L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RightPreLieAlgebra R Lᵐᵒᵖ

中文:
实例 :
  签名: RightPreLie代数 R Lᵐᵒᵖ
-/
instance : RightPreLieAlgebra R Lᵐᵒᵖ where

end LeftPreLieAlgebra

namespace RightPreLieRing

variable [RightPreLieRing L]

/--
theorem `assoc_symm` / 定理 `assoc_symm`

English:
theorem assoc_symm
  given: (x y z : L)
  proof: RightPreLieRing.assoc_symm' x y z

中文:
定理 assoc_symm
  条件: (x y z : L)
  证明: RightPreLieRing.assoc_symm' x y z

Depends on / 依赖: RightPreLieRing, RightPreLieRing.assoc_symm, assoc_symm
-/
theorem assoc_symm (x y z : L) :
    associator x y z = associator x z y := RightPreLieRing.assoc_symm' x y z

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LeftPreLieRing Lᵐᵒᵖ
  body: by
    simp [assoc_symm]

中文:
实例 :
  签名: LeftPreLie环 Lᵐᵒᵖ
  定义体: by
    simp [assoc_symm]

Depends on / 依赖: assoc_symm
-/
instance : LeftPreLieRing Lᵐᵒᵖ where
  assoc_symm' x y z := by
    simp [assoc_symm]

end RightPreLieRing

namespace RightPreLieAlgebra

variable [RightPreLieRing L] [RightPreLieAlgebra R L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LeftPreLieAlgebra R Lᵐᵒᵖ

中文:
实例 :
  签名: LeftPreLie代数 R Lᵐᵒᵖ
-/
instance : LeftPreLieAlgebra R Lᵐᵒᵖ where

end RightPreLieAlgebra
