/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.MetricSpace.Basic

/-!
# Transfer metric space structures across `Equiv`s

In this file, we transfer a distance and (pseudo-)metric space structure across an equivalence.

-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

-- See note [instance transfer via equivalence]
/--
Definition of `dist` / `dist` 的定义

English:
abbreviation dist
  signature: (e : α ≃ β) [Dist β]
  body: ⟨fun x y => dist (e.toFun x) (e.toFun y)⟩

中文:
缩写 dist
  签名: (e : α ≃ β) [Dist β]
  定义体: ⟨fun x y => dist (e.toFun x) (e.toFun y)⟩
-/
protected abbrev dist (e : α ≃ β) [Dist β] : Dist α := ⟨fun x y => dist (e.toFun x) (e.toFun y)⟩

/--
Definition of `pseudometricSpace` / `pseudometricSpace` 的定义

English:
abbreviation pseudometricSpace
  signature: [PseudoMetricSpace β] (e : α ≃ β)
  body: .induced e.toFun ‹_›

中文:
缩写 pseudometricSpace
  签名: [PseudoMetricSpace β] (e : α ≃ β)
  定义体: .induced e.toFun ‹_›
-/
protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ β) : PseudoMetricSpace α :=
  .induced e.toFun ‹_›

/--
Definition of `metricSpace` / `metricSpace` 的定义

English:
abbreviation metricSpace
  signature: [MetricSpace β] (e : α ≃ β)
  body: .induced e.toFun e.injective ‹_›

中文:
缩写 metricSpace
  签名: [MetricSpace β] (e : α ≃ β)
  定义体: .induced e.toFun e.injective ‹_›
-/
protected abbrev metricSpace [MetricSpace β] (e : α ≃ β) : MetricSpace α :=
  .induced e.toFun e.injective ‹_›

end Equiv
