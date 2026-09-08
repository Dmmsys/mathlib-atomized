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
/-
**LieAdmissibleRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LieAdmissibleRing` is a `NonUnitalNonAssocRing` such that the canonical brack
et
`⁅x, y⁆ := x * y - y * x` turns it into a `LieRing`. This is expressed by an ass
ociator identity.
-/
class LieAdmissibleRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_def (x y z : L) : associator x y z + associator z x y + associator y z x =
    associator y x z + associator z y x + associator x z y

/-- A `LieAdmissibleAlgebra` is a `LieAdmissibleRing` equipped with a compatible action by scalars
from a commutative ring. -/
@[ext]
/-
**LieAdmissibleAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → (L : Type u_2) → [CommRing R] → [LieAdmissibleRing L] → T
ype (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LieAdmissibleAlgebra` is a `LieAdmissibleRing` equipped with a compatible act
ion by scalars
from a commutative ring.
-/
class LieAdmissibleAlgebra (R L : Type*) [CommRing R] [LieAdmissibleRing L]
  extends Module R L, IsScalarTower R L L, SMulCommClass R L L

section instances

variable {R L : Type*} [CommRing R]

namespace LieAdmissibleRing

/-- By definition, every `LieAdmissibleRing` yields a `LieRing` with the commutator bracket. -/
/-
**LieAdmissibleRing.instLieRing** 是 Mathlib 中的一个实例，位于命名空间 `LieAdmissibleRing`。
形式化陈述：instLieRing [LieAdmissibleRing L] : LieRing L where add_lie x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By definition, every `LieAdmissibleRing` yields a `LieRing` with the commutator 
bracket.
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

/-- Every `LieAdmissibleAlgebra` is a `LieAlgebra` with the commutator bracket. -/
/-
**LieAdmissibleAlgebra.instLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieAdmissibleAl
gebra`。
形式化陈述：instLieAlgebra [LieAdmissibleRing L] [LieAdmissibleAlgebra R L] : LieAlgeb
ra R L where lie_smul r x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `LieAdmissibleAlgebra` is a `LieAlgebra` with the commutator bracket.
-/
instance instLieAlgebra [LieAdmissibleRing L] [LieAdmissibleAlgebra R L] : LieAlgebra R L where
  lie_smul r x y := by
    simp [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]

end LieAdmissibleAlgebra

namespace LeftPreLieRing

variable [LeftPreLieRing L]

/-- `LeftPreLieRings` are examples of `LieAdmissibleRings` by the commutativity assumption on the
associator. -/
/-
**LeftPreLieRing.instLieAdmissibleRing** 是 Mathlib 中的一个实例，位于命名空间 `LeftPreLieRing
`。
形式化陈述：instLieAdmissibleRing : LieAdmissibleRing L where assoc_def x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LeftPreLieRings` are examples of `LieAdmissibleRings` by the commutativity assu
mption on the
associator.
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

/-
**LeftPreLieAlgebra.instLieAdmissibleAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `LeftPreL
ieAlgebra`。
形式化陈述：{R : Type u_1} →   {L : Type u_2} →     [inst : CommRing R] → [inst_1 : Le
ftPreLieRing L] → [LeftPreLieAlgebra R L] → LieAdmissibleAlgebra R L
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LeftPreLieAlgebra.toIsScalarTower`：∀ {R : Type u_1} {inst : CommRing R} 
{L : Type u_2} {inst_1 : LeftPreLieRing L} [self : LeftPreLieAlgebra R L],   IsS
calarTower R L L
· 使用定理 `LeftPreLieAlgebra.toSMulCommClass`：∀ {R : Type u_1} {inst : CommRing R} 
{L : Type u_2} {inst_1 : LeftPreLieRing L} [self : LeftPreLieAlgebra R L],   SMu
lCommClass R L L
-/
instance instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where

end LeftPreLieAlgebra

namespace RightPreLieRing

variable [RightPreLieRing L]

/-- `RightPreLieRings` are examples of `LieAdmissibleRings` by the commutativity assumption on
the associator. -/
/-
**RightPreLieRing.instLieAdmissibleRing** 是 Mathlib 中的一个实例，位于命名空间 `RightPreLieRi
ng`。
形式化陈述：instLieAdmissibleRing : LieAdmissibleRing L where assoc_def x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RightPreLieRings` are examples of `LieAdmissibleRings` by the commutativity ass
umption on
the associator.
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

/-
**RightPreLieAlgebra.instLieAdmissibleAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `RightPr
eLieAlgebra`。
形式化陈述：{R : Type u_1} →   {L : Type u_2} →     [inst : CommRing R] → [inst_1 : Ri
ghtPreLieRing L] → [RightPreLieAlgebra R L] → LieAdmissibleAlgebra R L
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RightPreLieAlgebra.toIsScalarTower`：∀ {R : Type u_1} {inst : CommRing R}
 {L : Type u_2} {inst_1 : RightPreLieRing L} [self : RightPreLieAlgebra R L],   
IsScalarTower R L L
· 使用定理 `RightPreLieAlgebra.toSMulCommClass`：∀ {R : Type u_1} {inst : CommRing R}
 {L : Type u_2} {inst_1 : RightPreLieRing L} [self : RightPreLieAlgebra R L],   
SMulCommClass R L L
-/
instance instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where

end RightPreLieAlgebra

namespace Ring

variable [Ring L]

/-- Every ring is Lie-admissible.
See note [reducible non-instances]. -/
/-
**Ring.instLieAdmissibleRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ring`。
形式化陈述：instLieAdmissibleRing : LieAdmissibleRing L where assoc_def
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every ring is Lie-admissible.
See note [reducible non-instances].
-/
abbrev instLieAdmissibleRing : LieAdmissibleRing L where
  assoc_def := by
    suffices ∀ a b c : L, associator a b c = 0 by simp
    simp

end Ring

namespace Algebra

variable [Ring L] [Algebra R L]
attribute [local instance] Ring.instLieAdmissibleRing

/-- Every algebra is Lie-admissible.
See note [reducible non-instances]. -/
/-
**Algebra.instLieAdmissibleAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where smul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every algebra is Lie-admissible.
See note [reducible non-instances].
-/
abbrev instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where
  smul_comm := by simp

end Algebra

end instances

