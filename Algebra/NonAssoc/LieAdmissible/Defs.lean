/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.NonAssoc.PreLie.Basic
/-!
# Lie admissible rings and algebras

We define a Lie-admissible ring as a nonunital nonassociative ring such that the associator
satisfies the identity
```
associator x y z + associator z x y + associator y z x =
  associator y x z + associator z y x + associator x z y
```

## Main definitions:
  * `LieAdmissibleRing`
  * `LieAdmissibleAlgebra`

## Main results
  * `LieAdmissibleRing.instLieRing`: a Lie-admissible ring as a Lie ring
  * `LeftPreLieRing.instLieAdmissibleRing`: a left pre-Lie ring as a Lie admissible ring
  * `RightPreLieRing.instLieAdmissibleRing`: a right pre-Lie ring as a Lie admissible ring
  * `LieAdmissibleAlgebra.instLieAlgebra`: a Lie-admissible algebra as a Lie algebra
  * `LeftPreLieAlgebra.instLieAdmissibleAlgebra`: a left pre-Lie ring as a Lie admissible algebra
  * `RightPreLieAlgebra.instLieAdmissibleAlgebra`: a right pre-Lie ring as a Lie admissible algebra

## Implementation Notes
Algebras are implemented as extending `Module`, `IsScalarTower` and `SMulCommClass` following the
documentation of `Algebra`.

## References
[Munthe-Kaas, H.Z., Lundervold, A. **On Post-Lie Algebras, Lie–Butcher Series and Moving
Frames.**][munthe-kaas_lundervold_2013]
-/

@[expose] public section

/-- A `LieAdmissibleRing` is a `NonUnitalNonAssocRing` such that the canonical bracket
`⁅x, y⁆ := x * y - y * x` turns it into a `LieRing`. This is expressed by an associator identity. -/
@[ext]
/--
Definition of `LieAdmissibleRing` / `LieAdmissibleRing` 的定义

English:
class LieAdmissibleRing
  parameters: (L : Type*)
  extends: NonUnitalNonAssocRing L
  axioms and operations (1):
    - assoc_def((x y z : L)) : associator x y z + associator z x y + associator y z x = associator y x z + associator z y x + associator x z y

中文:
类 LieAdmissible环
  参数: (L : 类型)
  继承: 非幺非结合环 L
  公理与运算 (1 个):
    - assoc_def((x y z : L)) : associator x y z + associator z x y + associator y z x = associator y x z + associator z y x + associator x z y
-/
class LieAdmissibleRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_def (x y z : L) : associator x y z + associator z x y + associator y z x =
    associator y x z + associator z y x + associator x z y

/-- A `LieAdmissibleAlgebra` is a `LieAdmissibleRing` equipped with a compatible action by scalars
from a commutative ring. -/
@[ext]
/--
Definition of `LieAdmissibleAlgebra` / `LieAdmissibleAlgebra` 的定义

English:
class LieAdmissibleAlgebra
  parameters: (R L : Type*) [CommRing R] [LieAdmissibleRing L]
  extends: Module R L, IsScalarTower R L L, SMulCommClass R L L
  (no additional axioms)

中文:
类 LieAdmissible代数
  参数: (R L : 类型) [交换环 R] [LieAdmissible环 L]
  继承: 模 R L, 标量塔 R L L, 标量交换类 R L L
  (无附加公理)
-/
class LieAdmissibleAlgebra (R L : Type*) [CommRing R] [LieAdmissibleRing L]
  extends Module R L, IsScalarTower R L L, SMulCommClass R L L

section instances

variable {R L : Type*} [CommRing R]

namespace LieAdmissibleRing

/--
Instance `instLieRing` / 实例 `instLieRing`

English:
instance instLieRing
  signature: [LieAdmissibleRing L]
  body: by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_add x y z := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_self := by simp [Ring.lie_def]
  leibniz_lie x y z := by
    have := LieAdmissibleRing.assoc_def x y z
    simp only [associator_apply] at this
    grind [Ring.lie_def, mul_sub, sub_mul]

中文:
实例 instLieRing
  签名: [LieAdmissible环 L]
  定义体: by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_add x y z := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_self := by simp [Ring.lie_def]
  leibniz_lie x y z := by
    have := LieAdmissibleRing.assoc_def x y z
    simp only [associator_apply] at this
    grind [Ring.lie_def, mul_sub, sub_mul]

Depends on / 依赖: LieAdmissibleRing, LieAdmissibleRing.assoc_def, Ring.lie_def, add_mul, assoc_def, associator_apply, leibniz_lie, lie_add, lie_def, lie_self, mul_add, mul_sub, sub_mul
-/
instance instLieRing [LieAdmissibleRing L] : LieRing L where
  add_lie x y z := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_add x y z := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_self := by simp [Ring.lie_def]
  leibniz_lie x y z := by
    have := LieAdmissibleRing.assoc_def x y z
    simp only [associator_apply] at this
    grind [Ring.lie_def, mul_sub, sub_mul]

end LieAdmissibleRing

namespace LieAdmissibleAlgebra

/--
Instance `instLieAlgebra` / 实例 `instLieAlgebra`

English:
instance instLieAlgebra
  signature: [LieAdmissibleRing L] [LieAdmissibleAlgebra R L]
  body: by
    simp [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]

中文:
实例 instLieAlgebra
  签名: [LieAdmissible环 L] [LieAdmissible代数 R L]
  定义体: by
    simp [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]

Depends on / 依赖: Ring.lie_def, lie_def, mul_smul_comm, smul_mul_assoc, smul_sub
-/
instance instLieAlgebra [LieAdmissibleRing L] [LieAdmissibleAlgebra R L] : LieAlgebra R L where
  lie_smul r x y := by
    simp [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]

end LieAdmissibleAlgebra

namespace LeftPreLieRing

variable [LeftPreLieRing L]

/--
Instance `instLieAdmissibleRing` / 实例 `instLieAdmissibleRing`

English:
instance instLieAdmissibleRing
  signature: : LieAdmissibleRing L where
  body: by
    have assoc_xyz := LeftPreLieRing.assoc_symm' x y z
    have assoc_zxy := LeftPreLieRing.assoc_symm' z x y
    have assoc_yzx := LeftPreLieRing.assoc_symm' y z x
    grind

中文:
实例 instLieAdmissibleRing
  签名: : LieAdmissible环 L where
  定义体: by
    have assoc_xyz := LeftPreLieRing.assoc_symm' x y z
    have assoc_zxy := LeftPreLieRing.assoc_symm' z x y
    have assoc_yzx := LeftPreLieRing.assoc_symm' y z x
    grind

Depends on / 依赖: LeftPreLieRing, LeftPreLieRing.assoc_symm, assoc_symm, assoc_xyz, assoc_yzx, assoc_zxy
-/
instance instLieAdmissibleRing : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := LeftPreLieRing.assoc_symm' x y z
    have assoc_zxy := LeftPreLieRing.assoc_symm' z x y
    have assoc_yzx := LeftPreLieRing.assoc_symm' y z x
    grind

end LeftPreLieRing

namespace LeftPreLieAlgebra

variable [LeftPreLieRing L] [LeftPreLieAlgebra R L]

/--
Instance `instLieAdmissibleAlgebra` / 实例 `instLieAdmissibleAlgebra`

English:
instance instLieAdmissibleAlgebra
  signature: : LieAdmissibleAlgebra R L where

中文:
实例 instLieAdmissibleAlgebra
  签名: : LieAdmissible代数 R L where
-/
instance instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where

end LeftPreLieAlgebra

namespace RightPreLieRing

variable [RightPreLieRing L]

/--
Instance `instLieAdmissibleRing` / 实例 `instLieAdmissibleRing`

English:
instance instLieAdmissibleRing
  signature: : LieAdmissibleRing L where
  body: by
    have assoc_xyz := RightPreLieRing.assoc_symm' x y z
    have assoc_zxy := RightPreLieRing.assoc_symm' z x y
    have assoc_yzx := RightPreLieRing.assoc_symm' y z x
    grind

中文:
实例 instLieAdmissibleRing
  签名: : LieAdmissible环 L where
  定义体: by
    have assoc_xyz := RightPreLieRing.assoc_symm' x y z
    have assoc_zxy := RightPreLieRing.assoc_symm' z x y
    have assoc_yzx := RightPreLieRing.assoc_symm' y z x
    grind

Depends on / 依赖: RightPreLieRing, RightPreLieRing.assoc_symm, assoc_symm, assoc_xyz, assoc_yzx, assoc_zxy
-/
instance instLieAdmissibleRing : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := RightPreLieRing.assoc_symm' x y z
    have assoc_zxy := RightPreLieRing.assoc_symm' z x y
    have assoc_yzx := RightPreLieRing.assoc_symm' y z x
    grind

end RightPreLieRing

namespace RightPreLieAlgebra

variable [RightPreLieRing L] [RightPreLieAlgebra R L]

/--
Instance `instLieAdmissibleAlgebra` / 实例 `instLieAdmissibleAlgebra`

English:
instance instLieAdmissibleAlgebra
  signature: : LieAdmissibleAlgebra R L where

中文:
实例 instLieAdmissibleAlgebra
  签名: : LieAdmissible代数 R L where
-/
instance instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where

end RightPreLieAlgebra

namespace Ring

variable [Ring L]

/--
Definition of `instLieAdmissibleRing` / `instLieAdmissibleRing` 的定义

English:
abbreviation instLieAdmissibleRing
  signature: : LieAdmissibleRing L where
  body: by
    suffices forall a b c : L, associator a b c = 0 by simp
    simp

中文:
缩写 instLieAdmissibleRing
  签名: : LieAdmissible环 L where
  定义体: by
    suffices forall a b c : L, associator a b c = 0 by simp
    simp

Depends on / 依赖: associator
-/
abbrev instLieAdmissibleRing : LieAdmissibleRing L where
  assoc_def := by
    suffices forall a b c : L, associator a b c = 0 by simp
    simp

end Ring

namespace Algebra

variable [Ring L] [Algebra R L]
attribute [local instance] Ring.instLieAdmissibleRing

/--
Definition of `instLieAdmissibleAlgebra` / `instLieAdmissibleAlgebra` 的定义

English:
abbreviation instLieAdmissibleAlgebra
  signature: : LieAdmissibleAlgebra R L where
  body: by simp

中文:
缩写 instLieAdmissibleAlgebra
  签名: : LieAdmissible代数 R L where
  定义体: by simp
-/
abbrev instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where
  smul_comm := by simp

end Algebra

end instances
