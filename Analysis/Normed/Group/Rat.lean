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

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: : NormedAddCommGroup Rat where
  body: ‖(r : Real)‖
  dist_eq r₁ r₂ := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [← abs_neg]; rw [neg_sub]
    abel_nf

@[norm_cast, simp high] -- increase priority to prevent the left-hand side from simplifying

中文:
实例 instNormedAddCommGroup
  签名: : 赋范交换加群 有理数 where
  定义体: ‖(r : Real)‖
  dist_eq r₁ r₂ := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [← abs_neg]; rw [neg_sub]
    abel_nf

@[norm_cast, simp high] -- increase priority to prevent the left-hand side from simplifying
-/
instance instNormedAddCommGroup : NormedAddCommGroup Rat where
  norm r := ‖(r : Real)‖
  dist_eq r₁ r₂ := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [← abs_neg]; rw [neg_sub]
    abel_nf

@[norm_cast, simp high] -- increase priority to prevent the left-hand side from simplifying
/--
theorem `norm_cast_real` / 定理 `norm_cast_real`

English:
theorem norm_cast_real
  given: (r : Rat)
  statement: ‖(r : Real)‖ = ‖r‖
  proof: rfl

@[norm_cast, simp]

中文:
定理 norm_cast_real
  条件: (r : 有理数)
  结论: ‖(r : 实数)‖ = ‖r‖
  证明: rfl

@[norm_cast, simp]
-/
theorem norm_cast_real (r : Rat) : ‖(r : Real)‖ = ‖r‖ :=
  rfl

@[norm_cast, simp]
/--
theorem `_root_.Int.norm_cast_rat` / 定理 `_root_.Int.norm_cast_rat`

English:
theorem _root_.Int.norm_cast_rat
  given: (m : Int)
  statement: ‖(m : Rat)‖ = ‖m‖
  proof: by
  rw [← Rat.norm_cast_real]; rw [← Int.norm_cast_real]; congr 1

中文:
定理 _root_.整数.norm_cast_rat
  条件: (m : 整数)
  结论: ‖(m : 有理数)‖ = ‖m‖
  证明: by
  rw [← Rat.norm_cast_real]; rw [← Int.norm_cast_real]; congr 1

Depends on / 依赖: Int.norm_cast_real, Rat.norm_cast_real, norm_cast_real
-/
theorem _root_.Int.norm_cast_rat (m : Int) : ‖(m : Rat)‖ = ‖m‖ := by
  rw [← Rat.norm_cast_real]; rw [← Int.norm_cast_real]; congr 1

end Rat
