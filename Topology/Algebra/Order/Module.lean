/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.MulAction

/-!
# Continuous nonnegative scalar multiplication
-/

public section

variable {R α : Type*} [Semiring R] [PartialOrder R] [SMul R α] [TopologicalSpace α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousConstSMul
  signature: R α] : ContinuousConstSMul {r
  body: continuous_const_smul r.1

中文:
实例 [ContinuousConstSMul
  签名: R α] : ContinuousConstSMul {r
  定义体: continuous_const_smul r.1

Depends on / 依赖: continuous_const_smul
-/
instance [ContinuousConstSMul R α] : ContinuousConstSMul {r : R // 0 <= r} α where
  continuous_const_smul r := continuous_const_smul r.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: R] [ContinuousSMul R α] : ContinuousSMul {r
  body: continuous_smul (M := R).comp continuous_subtype_val.prodMap continuous_id

中文:
实例 [TopologicalSpace
  签名: R] [ContinuousSMul R α] : ContinuousSMul {r
  定义体: continuous_smul (M := R).comp continuous_subtype_val.prodMap continuous_id

Depends on / 依赖: continuous_id, continuous_smul, continuous_subtype_val, continuous_subtype_val.prodMap, prodMap
-/
instance [TopologicalSpace R] [ContinuousSMul R α] : ContinuousSMul {r : R // 0 <= r} α where
continuous_smul := continuous_smul (M := R).comp continuous_subtype_val.prodMap continuous_id
