/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Completion of a normed group

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/

public section


noncomputable section

namespace UniformSpace

namespace Completion

variable (E : Type*)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: E] [Norm E] : Norm (Completion E) where
  body: Completion.extension Norm.norm

@[simp]

中文:
实例 [一致空间
  签名: E] [范数 E] : 范数 (完备化 E) where
  定义体: Completion.extension Norm.norm

@[simp]

Depends on / 依赖: Completion, Completion.extension, Norm.norm, extension
-/
instance [UniformSpace E] [Norm E] : Norm (Completion E) where
  norm := Completion.extension Norm.norm

@[simp]
/--
theorem `norm_coe` / 定理 `norm_coe`

English:
theorem norm_coe
  given: {E} [SeminormedAddCommGroup E] (x : E)
  statement: ‖(x : Completion E)‖ = ‖x‖
  proof: Completion.extension_coe uniformContinuous_norm x

中文:
定理 norm_coe
  条件: {E} [SeminormedAddComm群 E] (x : E)
  结论: ‖(x : 完备化 E)‖ = ‖x‖
  证明: Completion.extension_coe uniformContinuous_norm x

Depends on / 依赖: Completion, Completion.extension_coe, extension_coe, uniformContinuous_norm
-/
theorem norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.extension_coe uniformContinuous_norm x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedAddCommGroup
  signature: E] : NormedAddCommGroup (Completion E) where
  body: by
    induction x, y using Completion.induction_on₂
    · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension (continuous_neg.fst.add continuous_snd)
    · rw [← Completion.coe_neg, ← Completion.coe_add, norm_coe, Completion.dist_eq,
        dist_eq_norm_neg_add]

@[simp]

中文:
实例 [SeminormedAddComm群
  签名: E] : 赋范交换加群 (完备化 E) where
  定义体: by
    induction x, y using Completion.induction_on₂
    · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension (continuous_neg.fst.add continuous_snd)
    · rw [← Completion.coe_neg, ← Completion.coe_add, norm_coe, Completion.dist_eq,
        dist_eq_norm_neg_add]

@[simp]

Depends on / 依赖: Completion, Completion.coe_add, Completion.coe_neg, Completion.continuous_extension, Completion.dist_eq, Completion.induction_on, Completion.uniformContinuous_extension, Continuous, Continuous.comp, coe_add, coe_neg, continuous, continuous_extension, continuous_neg, continuous_neg.fst.add, continuous_snd, dist_eq, dist_eq_norm_neg_add, isClosed_eq, norm_coe
-/
instance [SeminormedAddCommGroup E] : NormedAddCommGroup (Completion E) where
  dist_eq x y := by
    induction x, y using Completion.induction_on₂
    · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension (continuous_neg.fst.add continuous_snd)
    · rw [← Completion.coe_neg, ← Completion.coe_add, norm_coe, Completion.dist_eq,
        dist_eq_norm_neg_add]

@[simp]
/--
theorem `nnnorm_coe` / 定理 `nnnorm_coe`

English:
theorem nnnorm_coe
  given: {E} [SeminormedAddCommGroup E] (x : E)
  statement: ‖(x : Completion E)‖₊ = ‖x‖₊
  proof: by
  simp [nnnorm]

@[simp]

中文:
定理 nnnorm_coe
  条件: {E} [SeminormedAddComm群 E] (x : E)
  结论: ‖(x : 完备化 E)‖₊ = ‖x‖₊
  证明: by
  simp [nnnorm]

@[simp]

Depends on / 依赖: nnnorm
-/
theorem nnnorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖₊ = ‖x‖₊ := by
  simp [nnnorm]

@[simp]
/--
lemma `enorm_coe` / 引理 `enorm_coe`

English:
lemma enorm_coe
  given: {E} [SeminormedAddCommGroup E] (x : E)
  statement: ‖(x : Completion E)‖ₑ = ‖x‖ₑ
  proof: by
  simp [enorm]

中文:
引理 enorm_coe
  条件: {E} [SeminormedAddComm群 E] (x : E)
  结论: ‖(x : 完备化 E)‖ₑ = ‖x‖ₑ
  证明: by
  simp [enorm]
-/
lemma enorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ₑ = ‖x‖ₑ := by
  simp [enorm]

end Completion

end UniformSpace
