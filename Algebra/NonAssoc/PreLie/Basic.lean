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
/-
**LeftPreLieRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LeftPreLieRing`s are `NonUnitalNonAssocRing`s such that the `associator` is sym
metric in the
first two variables.
-/
class LeftPreLieRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_symm' (x y z : L) : associator x y z = associator y x z

/-- `RightPreLieRing`s are `NonUnitalNonAssocRing`s such that the `associator` is symmetric in the
last two variables. -/
@[ext]
/-
**RightPreLieRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RightPreLieRing`s are `NonUnitalNonAssocRing`s such that the `associator` is sy
mmetric in the
last two variables.
-/
class RightPreLieRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_symm' (x y z : L) : associator x y z = associator x z y

section algebras

variable (R : Type*) [CommRing R]

/-- A `LeftPreLieAlgebra` is a `LeftPreLieRing` with an action of a `CommRing` satisfying
`r • x * y = r • (x * y)` and ` x * (r • y) = r • (x * y)`. -/
@[ext]
/-
**LeftPreLieAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommRing R] → (L : Type u_2) → [LeftPreLieRing L] → Type
 (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LeftPreLieAlgebra` is a `LeftPreLieRing` with an action of a `CommRing` satis
fying
`r • x * y = r • (x * y)` and ` x * (r • y) = r • (x * y)`.
-/
class LeftPreLieAlgebra (L : Type*) [LeftPreLieRing L] : Type _ extends
  Module R L, IsScalarTower R L L, SMulCommClass R L L

/-- A `RightPreLieAlgebra` is a `RightPreLieRing` with an action of a `CommRing` satisfying
`r • x * y = r • (x * y)` and ` x * (r • y) = r • (x * y)`. -/
@[ext]
/-
**RightPreLieAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommRing R] → (L : Type u_2) → [RightPreLieRing L] → Typ
e (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `RightPreLieAlgebra` is a `RightPreLieRing` with an action of a `CommRing` sat
isfying
`r • x * y = r • (x * y)` and ` x * (r • y) = r • (x * y)`.
-/
class RightPreLieAlgebra (L : Type*) [RightPreLieRing L] : Type _ extends
  Module R L, IsScalarTower R L L, SMulCommClass R L L

end algebras

variable {R L : Type*} [CommRing R]

namespace LeftPreLieRing

variable [LeftPreLieRing L]

/-
**LeftPreLieRing.assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `LeftPreLieRing`。
形式化陈述：assoc_symm (x y z : L) : associator x y z = associator y x z
参数：x y z : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftPreLieRing.assoc_symm'`：∀ {L : Type u_1} [self : LeftPreLieRing L] (
x y z : L), associator x y z = associator y x z
-/
theorem assoc_symm (x y z : L) :
    associator x y z = associator y x z := LeftPreLieRing.assoc_symm' x y z

/-- Every left pre-Lie ring is a right pre-Lie ring with the opposite multiplication -/
/-
**LeftPreLieRing.** 是 Mathlib 中的一个实例，位于命名空间 `LeftPreLieRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every left pre-Lie ring is a right pre-Lie ring with the opposite multiplication
-/
instance : RightPreLieRing Lᵐᵒᵖ where
  assoc_symm' x y z := by
    simp [assoc_symm]

end LeftPreLieRing

namespace LeftPreLieAlgebra

variable [LeftPreLieRing L] [LeftPreLieAlgebra R L]

/-- Every left pre-Lie algebra is a right pre-Lie algebra with the opposite multiplication -/
/-
**LeftPreLieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LeftPreLieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every left pre-Lie algebra is a right pre-Lie algebra with the opposite multipli
cation
-/
instance : RightPreLieAlgebra R Lᵐᵒᵖ where

end LeftPreLieAlgebra

namespace RightPreLieRing

variable [RightPreLieRing L]

/-
**RightPreLieRing.assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `RightPreLieRing`。
形式化陈述：assoc_symm (x y z : L) : associator x y z = associator x z y
参数：x y z : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightPreLieRing.assoc_symm'`：∀ {L : Type u_1} [self : RightPreLieRing L]
 (x y z : L), associator x y z = associator x z y
-/
theorem assoc_symm (x y z : L) :
    associator x y z = associator x z y := RightPreLieRing.assoc_symm' x y z

/-- Every left pre-Lie ring is a right pre-Lie ring with the opposite multiplication -/
/-
**RightPreLieRing.** 是 Mathlib 中的一个实例，位于命名空间 `RightPreLieRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every left pre-Lie ring is a right pre-Lie ring with the opposite multiplication
-/
instance : LeftPreLieRing Lᵐᵒᵖ where
  assoc_symm' x y z := by
    simp [assoc_symm]

end RightPreLieRing

namespace RightPreLieAlgebra

variable [RightPreLieRing L] [RightPreLieAlgebra R L]

/-- Every left pre-Lie algebra is a right pre-Lie algebra with the opposite multiplication -/
/-
**RightPreLieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `RightPreLieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every left pre-Lie algebra is a right pre-Lie algebra with the opposite multipli
cation
-/
instance : LeftPreLieAlgebra R Lᵐᵒᵖ where

end RightPreLieAlgebra

