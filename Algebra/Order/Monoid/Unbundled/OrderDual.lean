/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/-! # Unbundled ordered monoid structures on the order dual. -/

public section

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
/--
Instance `mulLeftReflectLE` / 实例 `mulLeftReflectLE`

English:
instance mulLeftReflectLE
  signature: [LE α] [Mul α] [MulLeftReflectLE α]
  body: Contravariant.flip (μ := (· * ·)) (fun _ => ‹MulLeftReflectLE α›.le_of_mul_le_mul_left') _

@[to_additive]

中文:
实例 mulLeftReflectLE
  签名: [LE α] [Mul α] [MulLeftReflectLE α]
  定义体: Contravariant.flip (μ := (· * ·)) (fun _ => ‹MulLeftReflectLE α›.le_of_mul_le_mul_left') _

@[to_additive]

Depends on / 依赖: Contravariant, Contravariant.flip, MulLeftReflectLE, le_of_mul_le_mul_left
-/
instance mulLeftReflectLE [LE α] [Mul α] [MulLeftReflectLE α] : MulLeftReflectLE αᵒᵈ where
  le_of_mul_le_mul_left' :=
    Contravariant.flip (μ := (· * ·)) (fun _ => ‹MulLeftReflectLE α›.le_of_mul_le_mul_left') _

@[to_additive]
/--
Instance `mulLeftMono` / 实例 `mulLeftMono`

English:
instance mulLeftMono
  signature: [LE α] [Mul α] [c : MulLeftMono α]
  body: ⟨c.1.flip⟩

@[to_additive]

中文:
实例 mulLeftMono
  签名: [LE α] [Mul α] [c : MulLeftMono α]
  定义体: ⟨c.1.flip⟩

@[to_additive]
-/
instance mulLeftMono [LE α] [Mul α] [c : MulLeftMono α] : MulLeftMono αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/--
Instance `mulRightReflectLE` / 实例 `mulRightReflectLE`

English:
instance mulRightReflectLE
  signature: [LE α] [Mul α] [MulRightReflectLE α]
  body: Contravariant.flip (μ := swap (· * ·)) (fun _ => ‹MulRightReflectLE α›.le_of_mul_le_mul_right') _

@[to_additive]

中文:
实例 mulRightReflectLE
  签名: [LE α] [Mul α] [MulRightReflectLE α]
  定义体: Contravariant.flip (μ := swap (· * ·)) (fun _ => ‹MulRightReflectLE α›.le_of_mul_le_mul_right') _

@[to_additive]

Depends on / 依赖: Contravariant, Contravariant.flip, MulRightReflectLE, le_of_mul_le_mul_right
-/
instance mulRightReflectLE [LE α] [Mul α] [MulRightReflectLE α] : MulRightReflectLE αᵒᵈ where
  le_of_mul_le_mul_right' :=
    Contravariant.flip (μ := swap (· * ·)) (fun _ => ‹MulRightReflectLE α›.le_of_mul_le_mul_right') _

@[to_additive]
/--
Instance `mulRightMono` / 实例 `mulRightMono`

English:
instance mulRightMono
  signature: [LE α] [Mul α] [c : MulRightMono α]
  body: ⟨c.1.flip⟩

@[to_additive]

中文:
实例 mulRightMono
  签名: [LE α] [Mul α] [c : MulRightMono α]
  定义体: ⟨c.1.flip⟩

@[to_additive]
-/
instance mulRightMono [LE α] [Mul α] [c : MulRightMono α] : MulRightMono αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/--
Instance `mulLeftReflectLT` / 实例 `mulLeftReflectLT`

English:
instance mulLeftReflectLT
  signature: [LT α] [Mul α] [c : MulLeftReflectLT α]
  body: ⟨c.1.flip⟩

@[to_additive]

中文:
实例 mulLeftReflectLT
  签名: [LT α] [Mul α] [c : MulLeftReflectLT α]
  定义体: ⟨c.1.flip⟩

@[to_additive]
-/
instance mulLeftReflectLT [LT α] [Mul α] [c : MulLeftReflectLT α] : MulLeftReflectLT αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/--
Instance `mulLeftStrictMono` / 实例 `mulLeftStrictMono`

English:
instance mulLeftStrictMono
  signature: [LT α] [Mul α] [c : MulLeftStrictMono α]
  body: ⟨c.1.flip⟩

@[to_additive]

中文:
实例 mulLeftStrictMono
  签名: [LT α] [Mul α] [c : MulLeftStrictMono α]
  定义体: ⟨c.1.flip⟩

@[to_additive]
-/
instance mulLeftStrictMono [LT α] [Mul α] [c : MulLeftStrictMono α] : MulLeftStrictMono αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/--
Instance `mulRightReflectLT` / 实例 `mulRightReflectLT`

English:
instance mulRightReflectLT
  signature: [LT α] [Mul α] [c : MulRightReflectLT α]
  body: ⟨c.1.flip⟩

@[to_additive]

中文:
实例 mulRightReflectLT
  签名: [LT α] [Mul α] [c : MulRightReflectLT α]
  定义体: ⟨c.1.flip⟩

@[to_additive]
-/
instance mulRightReflectLT [LT α] [Mul α] [c : MulRightReflectLT α] : MulRightReflectLT αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/--
Instance `mulRightStrictMono` / 实例 `mulRightStrictMono`

English:
instance mulRightStrictMono
  signature: [LT α] [Mul α] [c : MulRightStrictMono α]
  body: ⟨c.1.flip⟩

中文:
实例 mulRightStrictMono
  签名: [LT α] [Mul α] [c : MulRightStrictMono α]
  定义体: ⟨c.1.flip⟩
-/
instance mulRightStrictMono [LT α] [Mul α] [c : MulRightStrictMono α] : MulRightStrictMono αᵒᵈ :=
  ⟨c.1.flip⟩

end OrderDual
