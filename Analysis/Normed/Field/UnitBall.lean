/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`Semigroup`, `CommSemigroup`, `Monoid`, `CommMonoid`,
`Group`, `CommGroup`) on `Metric.ball (0 : 𝕜) 1`, `Metric.closedBall (0 : 𝕜) 1`, and
`Metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `NonUnitalSeminormedRing` to `NormedField`.
-/

@[expose] public section


open Set Metric

variable {𝕜 : Type*}

/-!
### Algebraic structures on `Metric.ball 0 1`
-/

/--
Definition of `Subsemigroup.unitBall` / `Subsemigroup.unitBall` 的定义

English:
definition Subsemigroup.unitBall
  signature: (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜]
  body: ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

中文:
定义 Subsemigroup.unitBall
  签名: (𝕜 : 类型) [NonUnitalSeminormedRing 𝕜]
  定义体: ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)
-/
def Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

/--
lemma `Subsemigroup.mem_unitBall` / 引理 `Subsemigroup.mem_unitBall`

English:
lemma Subsemigroup.mem_unitBall
  given: (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] {x : 𝕜}
  proof: by
  simp [Subsemigroup.unitBall]

中文:
引理 Subsemigroup.mem_unitBall
  条件: (𝕜 : 类型) [NonUnitalSeminormedRing 𝕜] {x : 𝕜}
  证明: by
  simp [Subsemigroup.unitBall]
-/
@[simp] lemma Subsemigroup.mem_unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] {x : 𝕜} :
    x in Subsemigroup.unitBall 𝕜 ↔ ‖x‖ < 1 := by
  simp [Subsemigroup.unitBall]

/--
Instance `Metric.unitBall.instSemigroup` / 实例 `Metric.unitBall.instSemigroup`

English:
instance Metric.unitBall.instSemigroup
  signature: [NonUnitalSeminormedRing 𝕜]
  body: inferInstanceAs Semigroup (Subsemigroup.unitBall 𝕜)

中文:
实例 Metric.unitBall.instSemigroup
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: inferInstanceAs Semigroup (Subsemigroup.unitBall 𝕜)

Depends on / 依赖: Semigroup, Subsemigroup, Subsemigroup.unitBall, unitBall
-/
instance Metric.unitBall.instSemigroup [NonUnitalSeminormedRing 𝕜] : Semigroup (ball (0 : 𝕜) 1) :=
inferInstanceAs Semigroup (Subsemigroup.unitBall 𝕜)

/--
Instance `Metric.unitBall.instContinuousMul` / 实例 `Metric.unitBall.instContinuousMul`

English:
instance Metric.unitBall.instContinuousMul
  signature: [NonUnitalSeminormedRing 𝕜]
  body: (Subsemigroup.unitBall 𝕜).continuousMul

中文:
实例 Metric.unitBall.instContinuousMul
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: (Subsemigroup.unitBall 𝕜).continuousMul

Depends on / 依赖: Subsemigroup, Subsemigroup.unitBall, continuousMul, unitBall
-/
instance Metric.unitBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (ball (0 : 𝕜) 1) :=
  (Subsemigroup.unitBall 𝕜).continuousMul

/--
Instance `Metric.unitBall.instCommSemigroup` / 实例 `Metric.unitBall.instCommSemigroup`

English:
instance Metric.unitBall.instCommSemigroup
  signature: [SeminormedCommRing 𝕜]
  body: inferInstanceAs CommSemigroup (Subsemigroup.unitBall 𝕜)

中文:
实例 Metric.unitBall.instCommSemigroup
  签名: [SeminormedCommRing 𝕜]
  定义体: inferInstanceAs CommSemigroup (Subsemigroup.unitBall 𝕜)

Depends on / 依赖: CommSemigroup, Subsemigroup, Subsemigroup.unitBall, unitBall
-/
instance Metric.unitBall.instCommSemigroup [SeminormedCommRing 𝕜] :
    CommSemigroup (ball (0 : 𝕜) 1) :=
inferInstanceAs CommSemigroup (Subsemigroup.unitBall 𝕜)

/--
Instance `Metric.unitBall.instHasDistribNeg` / 实例 `Metric.unitBall.instHasDistribNeg`

English:
instance Metric.unitBall.instHasDistribNeg
  signature: [NonUnitalSeminormedRing 𝕜]
  body: Subtype.coe_injective.hasDistribNeg ((↑) : ball (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]

中文:
实例 Metric.unitBall.instHasDistribNeg
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: Subtype.coe_injective.hasDistribNeg ((↑) : ball (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_injective.hasDistribNeg, coe_injective, hasDistribNeg
-/
instance Metric.unitBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : ball (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]
/--
theorem `Metric.unitBall.coe_mul` / 定理 `Metric.unitBall.coe_mul`

English:
theorem Metric.unitBall.coe_mul
  given: [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1)
  proof: rfl

中文:
定理 Metric.unitBall.coe_mul
  条件: [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1)
  证明: rfl
-/
protected theorem Metric.unitBall.coe_mul [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl

/--
Instance `Metric.unitBall.instZero` / 实例 `Metric.unitBall.instZero`

English:
instance Metric.unitBall.instZero
  signature: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  body: ⟨⟨0, by simp⟩⟩

@[simp, norm_cast]

中文:
实例 Metric.unitBall.instZero
  签名: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  定义体: ⟨⟨0, by simp⟩⟩

@[simp, norm_cast]
-/
instance Metric.unitBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] : Zero (ball (0 : 𝕜) 1) :=
  ⟨⟨0, by simp⟩⟩

@[simp, norm_cast]
/--
theorem `Metric.unitBall.coe_zero` / 定理 `Metric.unitBall.coe_zero`

English:
theorem Metric.unitBall.coe_zero
  given: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  proof: rfl

@[simp, norm_cast]

中文:
定理 Metric.unitBall.coe_zero
  条件: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  证明: rfl

@[simp, norm_cast]
-/
protected theorem Metric.unitBall.coe_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    ((0 : ball (0 : 𝕜) 1) : 𝕜) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `Metric.unitBall.coe_eq_zero` / 定理 `Metric.unitBall.coe_eq_zero`

English:
theorem Metric.unitBall.coe_eq_zero
  given: [Zero 𝕜] [PseudoMetricSpace 𝕜] {a : ball (0 : 𝕜) 1}
  proof: Subtype.val_injective.eq_iff' unitBall.coe_zero

中文:
定理 Metric.unitBall.coe_eq_zero
  条件: [Zero 𝕜] [PseudoMetricSpace 𝕜] {a : ball (0 : 𝕜) 1}
  证明: Subtype.val_injective.eq_iff' unitBall.coe_zero
-/
protected theorem Metric.unitBall.coe_eq_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] {a : ball (0 : 𝕜) 1} :
    (a : 𝕜) = 0 ↔ a = 0 :=
  Subtype.val_injective.eq_iff' unitBall.coe_zero

/--
Instance `Metric.unitBall.instSemigroupWithZero` / 实例 `Metric.unitBall.instSemigroupWithZero`

English:
instance Metric.unitBall.instSemigroupWithZero
  signature: [NonUnitalSeminormedRing 𝕜]
  body: Subtype.ext zero_mul _
mul_zero _ := Subtype.ext mul_zero _

中文:
实例 Metric.unitBall.instSemigroupWithZero
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: Subtype.ext zero_mul _
mul_zero _ := Subtype.ext mul_zero _

Depends on / 依赖: Subtype, Subtype.ext, zero_mul
-/
instance Metric.unitBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] :
    SemigroupWithZero (ball (0 : 𝕜) 1) where
zero_mul _ := Subtype.ext zero_mul _
mul_zero _ := Subtype.ext mul_zero _

/--
Instance `Metric.unitBall.instIsLeftCancelMulZero` / 实例 `Metric.unitBall.instIsLeftCancelMulZero`

English:
instance Metric.unitBall.instIsLeftCancelMulZero
  signature: [NonUnitalSeminormedRing 𝕜]
  body: Subtype.val_injective.isLeftCancelMulZero _ rfl fun _ _ => rfl

中文:
实例 Metric.unitBall.instIsLeftCancelMulZero
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: Subtype.val_injective.isLeftCancelMulZero _ rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val_injective.isLeftCancelMulZero, isLeftCancelMulZero, val_injective
-/
instance Metric.unitBall.instIsLeftCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsLeftCancelMulZero 𝕜] : IsLeftCancelMulZero (ball (0 : 𝕜) 1) :=
  Subtype.val_injective.isLeftCancelMulZero _ rfl fun _ _ => rfl

/--
Instance `Metric.unitBall.instIsRightCancelMulZero` / 实例 `Metric.unitBall.instIsRightCancelMulZero`

English:
instance Metric.unitBall.instIsRightCancelMulZero
  signature: [NonUnitalSeminormedRing 𝕜]
  body: Subtype.val_injective.isRightCancelMulZero _ rfl fun _ _ => rfl

中文:
实例 Metric.unitBall.instIsRightCancelMulZero
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: Subtype.val_injective.isRightCancelMulZero _ rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val_injective.isRightCancelMulZero, isRightCancelMulZero, val_injective
-/
instance Metric.unitBall.instIsRightCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsRightCancelMulZero 𝕜] : IsRightCancelMulZero (ball (0 : 𝕜) 1) :=
  Subtype.val_injective.isRightCancelMulZero _ rfl fun _ _ => rfl

/--
Instance `Metric.unitBall.instIsCancelMulZero` / 实例 `Metric.unitBall.instIsCancelMulZero`

English:
instance Metric.unitBall.instIsCancelMulZero
  signature: [NonUnitalSeminormedRing 𝕜]

中文:
实例 Metric.unitBall.instIsCancelMulZero
  签名: [NonUnitalSeminormedRing 𝕜]
-/
instance Metric.unitBall.instIsCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsCancelMulZero 𝕜] : IsCancelMulZero (ball (0 : 𝕜) 1) where

/-!
### Algebraic instances for `Metric.closedBall 0 1`
-/

/--
Definition of `Subsemigroup.unitClosedBall` / `Subsemigroup.unitClosedBall` 的定义

English:
definition Subsemigroup.unitClosedBall
  signature: (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜]
  body: closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le _ _).trans (mul_le_one₀ hx (norm_nonneg _) hy)

中文:
定义 Subsemigroup.unitClosedBall
  签名: (𝕜 : 类型) [NonUnitalSeminormedRing 𝕜]
  定义体: closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le _ _).trans (mul_le_one₀ hx (norm_nonneg _) hy)

Depends on / 依赖: closedBall
-/
def Subsemigroup.unitClosedBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le _ _).trans (mul_le_one₀ hx (norm_nonneg _) hy)

/--
Instance `Metric.unitClosedBall.instSemigroup` / 实例 `Metric.unitClosedBall.instSemigroup`

English:
instance Metric.unitClosedBall.instSemigroup
  signature: [NonUnitalSeminormedRing 𝕜]
  body: inferInstanceAs Semigroup (Subsemigroup.unitClosedBall 𝕜)

中文:
实例 Metric.unitClosedBall.instSemigroup
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: inferInstanceAs Semigroup (Subsemigroup.unitClosedBall 𝕜)

Depends on / 依赖: Semigroup, Subsemigroup, Subsemigroup.unitClosedBall, unitClosedBall
-/
instance Metric.unitClosedBall.instSemigroup [NonUnitalSeminormedRing 𝕜] :
    Semigroup (closedBall (0 : 𝕜) 1) :=
inferInstanceAs Semigroup (Subsemigroup.unitClosedBall 𝕜)

/--
Instance `Metric.unitClosedBall.instHasDistribNeg` / 实例 `Metric.unitClosedBall.instHasDistribNeg`

English:
instance Metric.unitClosedBall.instHasDistribNeg
  signature: [NonUnitalSeminormedRing 𝕜]
  body: Subtype.coe_injective.hasDistribNeg ((↑) : closedBall (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

中文:
实例 Metric.unitClosedBall.instHasDistribNeg
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: Subtype.coe_injective.hasDistribNeg ((↑) : closedBall (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.hasDistribNeg, closedBall, coe_injective, hasDistribNeg
-/
instance Metric.unitClosedBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (closedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : closedBall (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

/--
Instance `Metric.unitClosedBall.instContinuousMul` / 实例 `Metric.unitClosedBall.instContinuousMul`

English:
instance Metric.unitClosedBall.instContinuousMul
  signature: [NonUnitalSeminormedRing 𝕜]
  body: (Subsemigroup.unitClosedBall 𝕜).continuousMul

@[simp, norm_cast]

中文:
实例 Metric.unitClosedBall.instContinuousMul
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: (Subsemigroup.unitClosedBall 𝕜).continuousMul

@[simp, norm_cast]

Depends on / 依赖: Subsemigroup, Subsemigroup.unitClosedBall, continuousMul, unitClosedBall
-/
instance Metric.unitClosedBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (closedBall (0 : 𝕜) 1) :=
  (Subsemigroup.unitClosedBall 𝕜).continuousMul

@[simp, norm_cast]
/--
theorem `Metric.unitClosedBall.coe_mul` / 定理 `Metric.unitClosedBall.coe_mul`

English:
theorem Metric.unitClosedBall.coe_mul
  statement: [NonUnitalSeminormedRing 𝕜]
  proof: rfl

中文:
定理 Metric.unitClosedBall.coe_mul
  结论: [NonUnitalSeminormedRing 𝕜]
  证明: rfl
-/
protected theorem Metric.unitClosedBall.coe_mul [NonUnitalSeminormedRing 𝕜]
    (x y : closedBall (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

/--
Instance `Metric.unitClosedBall.instZero` / 实例 `Metric.unitClosedBall.instZero`

English:
instance Metric.unitClosedBall.instZero
  signature: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  body: ⟨0, by simp⟩

@[simp, norm_cast]

中文:
实例 Metric.unitClosedBall.instZero
  签名: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  定义体: ⟨0, by simp⟩

@[simp, norm_cast]
-/
instance Metric.unitClosedBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    Zero (closedBall (0 : 𝕜) 1) where
  zero := ⟨0, by simp⟩

@[simp, norm_cast]
/--
lemma `Metric.unitClosedBall.coe_zero` / 引理 `Metric.unitClosedBall.coe_zero`

English:
lemma Metric.unitClosedBall.coe_zero
  given: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  proof: rfl

@[simp, norm_cast]

中文:
引理 Metric.unitClosedBall.coe_zero
  条件: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  证明: rfl

@[simp, norm_cast]
-/
protected lemma Metric.unitClosedBall.coe_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    ((0 : closedBall (0 : 𝕜) 1) : 𝕜) = 0 :=
  rfl

@[simp, norm_cast]
/--
lemma `Metric.unitClosedBall.coe_eq_zero` / 引理 `Metric.unitClosedBall.coe_eq_zero`

English:
lemma Metric.unitClosedBall.coe_eq_zero
  statement: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  proof: Subtype.val_injective.eq_iff' unitClosedBall.coe_zero

中文:
引理 Metric.unitClosedBall.coe_eq_zero
  结论: [Zero 𝕜] [PseudoMetricSpace 𝕜]
  证明: Subtype.val_injective.eq_iff' unitClosedBall.coe_zero
-/
protected lemma Metric.unitClosedBall.coe_eq_zero [Zero 𝕜] [PseudoMetricSpace 𝕜]
    {a : closedBall (0 : 𝕜) 1} : (a : 𝕜) = 0 ↔ a = 0 :=
  Subtype.val_injective.eq_iff' unitClosedBall.coe_zero

/--
Instance `Metric.unitClosedBall.instSemigroupWithZero` / 实例 `Metric.unitClosedBall.instSemigroupWithZero`

English:
instance Metric.unitClosedBall.instSemigroupWithZero
  signature: [NonUnitalSeminormedRing 𝕜]
  body: Subtype.ext zero_mul _
mul_zero _ := Subtype.ext mul_zero _

中文:
实例 Metric.unitClosedBall.instSemigroupWithZero
  签名: [NonUnitalSeminormedRing 𝕜]
  定义体: Subtype.ext zero_mul _
mul_zero _ := Subtype.ext mul_zero _

Depends on / 依赖: Subtype, Subtype.ext, zero_mul
-/
instance Metric.unitClosedBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] :
    SemigroupWithZero (closedBall (0 : 𝕜) 1) where
zero_mul _ := Subtype.ext zero_mul _
mul_zero _ := Subtype.ext mul_zero _

/--
Definition of `Submonoid.unitClosedBall` / `Submonoid.unitClosedBall` 的定义

English:
definition Submonoid.unitClosedBall
  signature: (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜]
  body: { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }

中文:
定义 Submonoid.unitClosedBall
  签名: (𝕜 : 类型) [SeminormedRing 𝕜] [NormOneClass 𝕜]
  定义体: { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }

Depends on / 依赖: Subsemigroup, Subsemigroup.unitClosedBall, carrier, closedBall, mem_closedBall_zero_iff, norm_one, norm_one.le, one_mem, unitClosedBall
-/
def Submonoid.unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Submonoid.mem_unitClosedBall` / 引理 `Submonoid.mem_unitClosedBall`

English:
lemma Submonoid.mem_unitClosedBall
  given: (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] {x : 𝕜}
  proof: by
  simp [Submonoid.unitClosedBall]

中文:
引理 Submonoid.mem_unitClosedBall
  条件: (𝕜 : 类型) [SeminormedRing 𝕜] [NormOneClass 𝕜] {x : 𝕜}
  证明: by
  simp [Submonoid.unitClosedBall]
-/
@[simp] lemma Submonoid.mem_unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] {x : 𝕜} :
    x in Submonoid.unitClosedBall 𝕜 ↔ ‖x‖ <= 1 := by
  simp [Submonoid.unitClosedBall]

/--
Instance `Metric.unitClosedBall.instMonoid` / 实例 `Metric.unitClosedBall.instMonoid`

English:
instance Metric.unitClosedBall.instMonoid
  signature: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  body: inferInstanceAs Monoid (Submonoid.unitClosedBall 𝕜)

中文:
实例 Metric.unitClosedBall.instMonoid
  签名: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  定义体: inferInstanceAs Monoid (Submonoid.unitClosedBall 𝕜)

Depends on / 依赖: Monoid, Submonoid, Submonoid.unitClosedBall, unitClosedBall
-/
instance Metric.unitClosedBall.instMonoid [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    Monoid (closedBall (0 : 𝕜) 1) :=
inferInstanceAs Monoid (Submonoid.unitClosedBall 𝕜)

/--
Instance `Metric.unitClosedBall.instCommMonoid` / 实例 `Metric.unitClosedBall.instCommMonoid`

English:
instance Metric.unitClosedBall.instCommMonoid
  signature: [SeminormedCommRing 𝕜] [NormOneClass 𝕜]
  body: inferInstanceAs CommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]

中文:
实例 Metric.unitClosedBall.instCommMonoid
  签名: [SeminormedCommRing 𝕜] [NormOneClass 𝕜]
  定义体: inferInstanceAs CommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]

Depends on / 依赖: CommMonoid, Submonoid, Submonoid.unitClosedBall, unitClosedBall
-/
instance Metric.unitClosedBall.instCommMonoid [SeminormedCommRing 𝕜] [NormOneClass 𝕜] :
    CommMonoid (closedBall (0 : 𝕜) 1) :=
inferInstanceAs CommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]
/--
theorem `Metric.unitClosedBall.coe_one` / 定理 `Metric.unitClosedBall.coe_one`

English:
theorem Metric.unitClosedBall.coe_one
  given: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  proof: rfl

@[simp, norm_cast]

中文:
定理 Metric.unitClosedBall.coe_one
  条件: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  证明: rfl

@[simp, norm_cast]
-/
protected theorem Metric.unitClosedBall.coe_one [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    ((1 : closedBall (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `Metric.unitClosedBall.coe_eq_one` / 定理 `Metric.unitClosedBall.coe_eq_one`

English:
theorem Metric.unitClosedBall.coe_eq_one
  statement: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  proof: Subtype.val_injective.eq_iff' unitClosedBall.coe_one

@[simp, norm_cast]

中文:
定理 Metric.unitClosedBall.coe_eq_one
  结论: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  证明: Subtype.val_injective.eq_iff' unitClosedBall.coe_one

@[simp, norm_cast]
-/
protected theorem Metric.unitClosedBall.coe_eq_one [SeminormedRing 𝕜] [NormOneClass 𝕜]
    {a : closedBall (0 : 𝕜) 1} : (a : 𝕜) = 1 ↔ a = 1 :=
  Subtype.val_injective.eq_iff' unitClosedBall.coe_one

@[simp, norm_cast]
/--
theorem `Metric.unitClosedBall.coe_pow` / 定理 `Metric.unitClosedBall.coe_pow`

English:
theorem Metric.unitClosedBall.coe_pow
  statement: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  proof: rfl

中文:
定理 Metric.unitClosedBall.coe_pow
  结论: [SeminormedRing 𝕜] [NormOneClass 𝕜]
  证明: rfl
-/
protected theorem Metric.unitClosedBall.coe_pow [SeminormedRing 𝕜] [NormOneClass 𝕜]
    (x : closedBall (0 : 𝕜) 1) (n : Nat) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

/--
Instance `Metric.unitClosedBall.instMonoidWithZero` / 实例 `Metric.unitClosedBall.instMonoidWithZero`

English:
instance Metric.unitClosedBall.instMonoidWithZero
  signature: [SeminormedRing 𝕜] [NormOneClass 𝕜]

中文:
实例 Metric.unitClosedBall.instMonoidWithZero
  签名: [SeminormedRing 𝕜] [NormOneClass 𝕜]
-/
instance Metric.unitClosedBall.instMonoidWithZero [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    MonoidWithZero (closedBall (0 : 𝕜) 1) where

/--
Instance `Metric.unitClosedBall.instIsCancelMulZero` / 实例 `Metric.unitClosedBall.instIsCancelMulZero`

English:
instance Metric.unitClosedBall.instIsCancelMulZero
  signature: [SeminormedRing 𝕜] [IsCancelMulZero 𝕜]
  body: Subtype.val_injective.isCancelMulZero _ rfl fun _ _ => rfl

中文:
实例 Metric.unitClosedBall.instIsCancelMulZero
  签名: [SeminormedRing 𝕜] [IsCancelMulZero 𝕜]
  定义体: Subtype.val_injective.isCancelMulZero _ rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val_injective.isCancelMulZero, isCancelMulZero, val_injective
-/
instance Metric.unitClosedBall.instIsCancelMulZero [SeminormedRing 𝕜] [IsCancelMulZero 𝕜]
    [NormOneClass 𝕜] : IsCancelMulZero (closedBall (0 : 𝕜) 1) :=
  Subtype.val_injective.isCancelMulZero _ rfl fun _ _ => rfl

/-!
### Algebraic instances on the unit sphere
-/

/-- Unit sphere in a seminormed ring (with strictly multiplicative norm) as a bundled
`Submonoid`. -/
@[simps]
/--
Definition of `Submonoid.unitSphere` / `Submonoid.unitSphere` 的定义

English:
definition Submonoid.unitSphere
  signature: (𝕜 : Type*) [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  body: sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

中文:
定义 Submonoid.unitSphere
  签名: (𝕜 : 类型) [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  定义体: sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

Depends on / 依赖: sphere
-/
def Submonoid.unitSphere (𝕜 : Type*) [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Submonoid 𝕜 where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

/--
Instance `Metric.unitSphere.instInv` / 实例 `Metric.unitSphere.instInv`

English:
instance Metric.unitSphere.instInv
  signature: [NormedDivisionRing 𝕜]
  body: ⟨x⁻¹, mem_sphere_zero_iff_norm.2 by
    rw [norm_inv]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [inv_one]⟩

@[simp, norm_cast]

中文:
实例 Metric.unitSphere.instInv
  签名: [NormedDivisionRing 𝕜]
  定义体: ⟨x⁻¹, mem_sphere_zero_iff_norm.2 by
    rw [norm_inv]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [inv_one]⟩

@[simp, norm_cast]

Depends on / 依赖: coe_prop, inv_one, mem_sphere_zero_iff_norm, norm_inv, x.coe_prop
-/
instance Metric.unitSphere.instInv [NormedDivisionRing 𝕜] : Inv (sphere (0 : 𝕜) 1) where
inv x := ⟨x⁻¹, mem_sphere_zero_iff_norm.2 by
    rw [norm_inv]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [inv_one]⟩

@[simp, norm_cast]
/--
theorem `Metric.unitSphere.coe_inv` / 定理 `Metric.unitSphere.coe_inv`

English:
theorem Metric.unitSphere.coe_inv
  given: [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1)
  proof: rfl

中文:
定理 Metric.unitSphere.coe_inv
  条件: [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1)
  证明: rfl
-/
theorem Metric.unitSphere.coe_inv [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    ↑x⁻¹ = (x⁻¹ : 𝕜) :=
  rfl

/--
Instance `Metric.unitSphere.instDiv` / 实例 `Metric.unitSphere.instDiv`

English:
instance Metric.unitSphere.instDiv
  signature: [NormedDivisionRing 𝕜]
  body: .mk (x / y) mem_sphere_zero_iff_norm.2 by
    rw [norm_div]; rw [mem_sphere_zero_iff_norm.1 x.2]; rw [mem_sphere_zero_iff_norm.1 y.coe_prop]; rw [div_one]

@[simp, norm_cast]

中文:
实例 Metric.unitSphere.instDiv
  签名: [NormedDivisionRing 𝕜]
  定义体: .mk (x / y) mem_sphere_zero_iff_norm.2 by
    rw [norm_div]; rw [mem_sphere_zero_iff_norm.1 x.2]; rw [mem_sphere_zero_iff_norm.1 y.coe_prop]; rw [div_one]

@[simp, norm_cast]

Depends on / 依赖: coe_prop, div_one, mem_sphere_zero_iff_norm, norm_div, y.coe_prop
-/
instance Metric.unitSphere.instDiv [NormedDivisionRing 𝕜] : Div (sphere (0 : 𝕜) 1) where
div x y := .mk (x / y) mem_sphere_zero_iff_norm.2 by
    rw [norm_div]; rw [mem_sphere_zero_iff_norm.1 x.2]; rw [mem_sphere_zero_iff_norm.1 y.coe_prop]; rw [div_one]

@[simp, norm_cast]
/--
theorem `Metric.unitSphere.coe_div` / 定理 `Metric.unitSphere.coe_div`

English:
theorem Metric.unitSphere.coe_div
  given: [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1)
  proof: rfl

中文:
定理 Metric.unitSphere.coe_div
  条件: [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1)
  证明: rfl
-/
protected theorem Metric.unitSphere.coe_div [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x / y) = (x / y : 𝕜) :=
  rfl

/--
Instance `Metric.unitSphere.instZPow` / 实例 `Metric.unitSphere.instZPow`

English:
instance Metric.unitSphere.instZPow
  signature: [NormedDivisionRing 𝕜]
  body: .mk ((x : 𝕜) ^ n) by
    rw [mem_sphere_zero_iff_norm]; rw [norm_zpow]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [one_zpow]

@[simp, norm_cast]

中文:
实例 Metric.unitSphere.instZPow
  签名: [NormedDivisionRing 𝕜]
  定义体: .mk ((x : 𝕜) ^ n) by
    rw [mem_sphere_zero_iff_norm]; rw [norm_zpow]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [one_zpow]

@[simp, norm_cast]

Depends on / 依赖: coe_prop, mem_sphere_zero_iff_norm, norm_zpow, one_zpow, x.coe_prop
-/
instance Metric.unitSphere.instZPow [NormedDivisionRing 𝕜] : Pow (sphere (0 : 𝕜) 1) Int where
pow x n := .mk ((x : 𝕜) ^ n) by
    rw [mem_sphere_zero_iff_norm]; rw [norm_zpow]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [one_zpow]

@[simp, norm_cast]
/--
theorem `Metric.unitSphere.coe_zpow` / 定理 `Metric.unitSphere.coe_zpow`

English:
theorem Metric.unitSphere.coe_zpow
  given: [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : Int)
  proof: rfl

中文:
定理 Metric.unitSphere.coe_zpow
  条件: [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : 整数)
  证明: rfl
-/
theorem Metric.unitSphere.coe_zpow [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : Int) :
    ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

/--
Instance `Metric.unitSphere.instMonoid` / 实例 `Metric.unitSphere.instMonoid`

English:
instance Metric.unitSphere.instMonoid
  signature: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  body: inferInstanceAs Monoid (Submonoid.unitSphere 𝕜)

中文:
实例 Metric.unitSphere.instMonoid
  签名: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  定义体: inferInstanceAs Monoid (Submonoid.unitSphere 𝕜)

Depends on / 依赖: Monoid, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance Metric.unitSphere.instMonoid [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Monoid (sphere (0 : 𝕜) 1) :=
inferInstanceAs Monoid (Submonoid.unitSphere 𝕜)

/--
Instance `Metric.unitSphere.instCommMonoid` / 实例 `Metric.unitSphere.instCommMonoid`

English:
instance Metric.unitSphere.instCommMonoid
  signature: [SeminormedCommRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  body: inferInstanceAs CommMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]

中文:
实例 Metric.unitSphere.instCommMonoid
  签名: [SeminormedCommRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  定义体: inferInstanceAs CommMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]

Depends on / 依赖: CommMonoid, Submonoid, Submonoid.unitSphere, unitSphere
-/
instance Metric.unitSphere.instCommMonoid [SeminormedCommRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    CommMonoid (sphere (0 : 𝕜) 1) :=
inferInstanceAs CommMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]
/--
theorem `Metric.unitSphere.coe_one` / 定理 `Metric.unitSphere.coe_one`

English:
theorem Metric.unitSphere.coe_one
  given: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  proof: rfl

@[simp, norm_cast]

中文:
定理 Metric.unitSphere.coe_one
  条件: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  证明: rfl

@[simp, norm_cast]
-/
protected theorem Metric.unitSphere.coe_one [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    ((1 : sphere (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `Metric.unitSphere.coe_mul` / 定理 `Metric.unitSphere.coe_mul`

English:
theorem Metric.unitSphere.coe_mul
  statement: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  proof: rfl

@[simp, norm_cast]

中文:
定理 Metric.unitSphere.coe_mul
  结论: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  证明: rfl

@[simp, norm_cast]
-/
theorem Metric.unitSphere.coe_mul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
    (x y : sphere (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

@[simp, norm_cast]
/--
theorem `Metric.unitSphere.coe_pow` / 定理 `Metric.unitSphere.coe_pow`

English:
theorem Metric.unitSphere.coe_pow
  statement: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  proof: rfl

中文:
定理 Metric.unitSphere.coe_pow
  结论: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  证明: rfl
-/
theorem Metric.unitSphere.coe_pow [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
    (x : sphere (0 : 𝕜) 1) (n : Nat) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

/--
Definition of `unitSphereToUnits` / `unitSphereToUnits` 的定义

English:
definition unitSphereToUnits
  signature: (𝕜 : Type*) [NormedDivisionRing 𝕜]
  body: Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl

@[simp]

中文:
定义 unitSphereToUnits
  签名: (𝕜 : 类型) [NormedDivisionRing 𝕜]
  定义体: Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl

@[simp]

Depends on / 依赖: Submonoid, Submonoid.unitSphere, Units.liftRight, Units.mk0, liftRight, ne_zero_of_mem_unit_sphere, subtype, unitSphere
-/
def unitSphereToUnits (𝕜 : Type*) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 ->* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl

@[simp]
/--
theorem `unitSphereToUnits_apply_coe` / 定理 `unitSphereToUnits_apply_coe`

English:
theorem unitSphereToUnits_apply_coe
  given: [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1)
  proof: rfl

中文:
定理 unitSphereToUnits_apply_coe
  条件: [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1)
  证明: rfl
-/
theorem unitSphereToUnits_apply_coe [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    (unitSphereToUnits 𝕜 x : 𝕜) = x :=
  rfl

/--
theorem `unitSphereToUnits_injective` / 定理 `unitSphereToUnits_injective`

English:
theorem unitSphereToUnits_injective
  given: [NormedDivisionRing 𝕜]
  proof: fun x y h =>
Subtype.ext by convert! congr_arg Units.val h

中文:
定理 unitSphereToUnits_injective
  条件: [NormedDivisionRing 𝕜]
  证明: fun x y h =>
Subtype.ext by convert! congr_arg Units.val h
-/
theorem unitSphereToUnits_injective [NormedDivisionRing 𝕜] :
    Function.Injective (unitSphereToUnits 𝕜) := fun x y h =>
Subtype.ext by convert! congr_arg Units.val h

/--
Instance `Metric.unitSphere.instGroup` / 实例 `Metric.unitSphere.instGroup`

English:
instance Metric.unitSphere.instGroup
  signature: [NormedDivisionRing 𝕜]
  body: fast_instance% unitSphereToUnits_injective.group (unitSphereToUnits 𝕜) (Units.ext rfl)
    (fun _x _y => Units.ext rfl)
    (fun _x => Units.ext rfl) (fun _x _y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Uni

中文:
实例 Metric.unitSphere.instGroup
  签名: [NormedDivisionRing 𝕜]
  定义体: fast_instance% unitSphereToUnits_injective.group (unitSphereToUnits 𝕜) (Units.ext rfl)
    (fun _x _y => Units.ext rfl)
    (fun _x => Units.ext rfl) (fun _x _y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Uni

Depends on / 依赖: Units.ext, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, div_eq_mul_inv, fast_instance, unitSphereToUnits, unitSphereToUnits_injective, unitSphereToUnits_injective.group, val_pow_eq_pow_val, val_zpow_eq_zpow_val
-/
instance Metric.unitSphere.instGroup [NormedDivisionRing 𝕜] : Group (sphere (0 : 𝕜) 1) :=
  fast_instance% unitSphereToUnits_injective.group (unitSphereToUnits 𝕜) (Units.ext rfl)
    (fun _x _y => Units.ext rfl)
    (fun _x => Units.ext rfl) (fun _x _y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Units.ext (Units.val_zpow_eq_zpow_val (unitSphereToUnits 𝕜 x) n).symm

/--
Instance `Metric.sphere.instHasDistribNeg` / 实例 `Metric.sphere.instHasDistribNeg`

English:
instance Metric.sphere.instHasDistribNeg
  signature: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  body: Subtype.coe_injective.hasDistribNeg ((↑) : sphere (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

中文:
实例 Metric.sphere.instHasDistribNeg
  签名: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  定义体: Subtype.coe_injective.hasDistribNeg ((↑) : sphere (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.hasDistribNeg, coe_injective, hasDistribNeg, sphere
-/
instance Metric.sphere.instHasDistribNeg [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    HasDistribNeg (sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : sphere (0 : 𝕜) 1 -> 𝕜) (fun _ => rfl) fun _ _ => rfl

/--
Instance `Metric.sphere.instContinuousMul` / 实例 `Metric.sphere.instContinuousMul`

English:
instance Metric.sphere.instContinuousMul
  signature: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  body: (Submonoid.unitSphere 𝕜).continuousMul

中文:
实例 Metric.sphere.instContinuousMul
  签名: [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
  定义体: (Submonoid.unitSphere 𝕜).continuousMul

Depends on / 依赖: Submonoid, Submonoid.unitSphere, continuousMul, unitSphere
-/
instance Metric.sphere.instContinuousMul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    ContinuousMul (sphere (0 : 𝕜) 1) :=
  (Submonoid.unitSphere 𝕜).continuousMul

/--
Instance `Metric.sphere.instIsTopologicalGroup` / 实例 `Metric.sphere.instIsTopologicalGroup`

English:
instance Metric.sphere.instIsTopologicalGroup
  signature: [NormedDivisionRing 𝕜]
  body: (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

中文:
实例 Metric.sphere.instIsTopologicalGroup
  签名: [NormedDivisionRing 𝕜]
  定义体: (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

Depends on / 依赖: continuous_subtype_val, continuous_subtype_val.inv, ne_zero_of_mem_unit_sphere, subtype_mk
-/
instance Metric.sphere.instIsTopologicalGroup [NormedDivisionRing 𝕜] :
    IsTopologicalGroup (sphere (0 : 𝕜) 1) where
  continuous_inv := (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

/--
Instance `Metric.sphere.instCommGroup` / 实例 `Metric.sphere.instCommGroup`

English:
instance Metric.sphere.instCommGroup
  signature: [NormedField 𝕜]

中文:
实例 Metric.sphere.instCommGroup
  签名: [NormedField 𝕜]
-/
instance Metric.sphere.instCommGroup [NormedField 𝕜] : CommGroup (sphere (0 : 𝕜) 1) where
