/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric distances on pi types

This file contains results on the behavior of ultrametrics in products of ultrametric spaces.

## Main results

* `Pi.instIsUltrametricDist`: a product of ultrametric spaces is ultrametric.


ultrametric, nonarchimedean
-/

public section

/-
**Pi.instIsUltrametricDist** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsUltrametricDist {ι : Type*} {X : ι -> Type*} [Fintype ι] [(i : ι)
 -> PseudoMetricSpace (X i)] [(i : ι) -> IsUltrametricDist (X i)] : IsUltrametri
cDist ((i : ι) -> X i)
参数：i : ι；X i；i : ι；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
-/
instance Pi.instIsUltrametricDist {ι : Type*} {X : ι → Type*} [Fintype ι]
    [(i : ι) → PseudoMetricSpace (X i)] [(i : ι) → IsUltrametricDist (X i)] :
    IsUltrametricDist ((i : ι) → X i) := by
  constructor
  intro f g h
  simp only [dist_pi_def, ← NNReal.coe_max, NNReal.coe_le_coe, ← Finset.sup_sup]
  exact Finset.sup_mono_fun fun i _ ↦ IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)
