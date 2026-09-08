/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Topology.Instances.Rat

/-! # ℚ as a normed group -/

public section

namespace Rat

/-
**Rat.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instNormedAddCommGroup : NormedAddCommGroup Rat where norm r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedAddCommGroup : NormedAddCommGroup ℚ where
  norm r := ‖(r : ℝ)‖
  dist_eq r₁ r₂ := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [← abs_neg, neg_sub]
    abel_nf

@[norm_cast, simp high] -- increase priority to prevent the left-hand side from simplifying
/-
**Rat.norm_cast_real** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：norm_cast_real (r : Rat) : ‖(r : Real)‖ = ‖r‖
参数：r : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_cast_real (r : ℚ) : ‖(r : ℝ)‖ = ‖r‖ :=
  rfl

@[norm_cast, simp]
/-
**Rat._root_.Int.norm_cast_rat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Int.norm_cast_rat (m : ℤ) : ‖(m : ℚ)‖ = ‖m‖ := by
  rw [← Rat.norm_cast_real, ← Int.norm_cast_real]; congr 1

end Rat

