/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Topology.Algebra.Field

/-!
# Continuous actions related to intermediate fields

In this file we define the instances related to continuous actions of
intermediate fields. The topology on intermediate fields is already defined
in earlier file `Mathlib/Topology/Algebra/Field.lean` as the subspace topology.
-/

public section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [IsTopologicalRing L]

variable (X : Type*) [TopologicalSpace X] [MulAction L X] [ContinuousSMul L X]
variable (M : IntermediateField K L)

/--
Instance `IntermediateField.continuousSMul` / 实例 `IntermediateField.continuousSMul`

English:
instance IntermediateField.continuousSMul
  signature: (M : IntermediateField K L)
  body: M.toSubfield.continuousSMul X

中文:
实例 中间域.continuousSMul
  签名: (M : 中间域 K L)
  定义体: M.toSubfield.continuousSMul X

Depends on / 依赖: M.toSubfield.continuousSMul, continuousSMul, toSubfield
-/
instance IntermediateField.continuousSMul (M : IntermediateField K L) : ContinuousSMul M X :=
  M.toSubfield.continuousSMul X

/--
Instance `IntermediateField.botContinuousSMul` / 实例 `IntermediateField.botContinuousSMul`

English:
instance IntermediateField.botContinuousSMul
  signature: (M : IntermediateField K L)
  body: Topology.IsInducing.continuousSMul (X := L) (N := (⊥ : IntermediateField K L)) (Y := M)
    (M := (⊥ : IntermediateField K L)) Topology.IsInducing.subtypeVal continuous_id rfl

中文:
实例 中间域.botContinuousSMul
  签名: (M : 中间域 K L)
  定义体: Topology.IsInducing.continuousSMul (X := L) (N := (⊥ : IntermediateField K L)) (Y := M)
    (M := (⊥ : IntermediateField K L)) Topology.IsInducing.subtypeVal continuous_id rfl

Depends on / 依赖: IntermediateField, IsInducing, Topology, Topology.IsInducing.continuousSMul, Topology.IsInducing.subtypeVal, continuousSMul, continuous_id, subtypeVal
-/
instance IntermediateField.botContinuousSMul (M : IntermediateField K L) :
    ContinuousSMul (⊥ : IntermediateField K L) M :=
  Topology.IsInducing.continuousSMul (X := L) (N := (⊥ : IntermediateField K L)) (Y := M)
    (M := (⊥ : IntermediateField K L)) Topology.IsInducing.subtypeVal continuous_id rfl
