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

/-- Unit ball in a non-unital seminormed ring as a bundled `Subsemigroup`. -/
/-
**Subsemigroup.unitBall** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigro
up 𝕜 where carrier
参数：𝕜 : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unit ball in a non-unital seminormed ring as a bundled `Subsemigroup`.
-/
def Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)
/-
**Subsemigroup.mem_unitBall** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：∀ (𝕜 : Type u_2) [inst : NonUnitalSeminormedRing 𝕜] {x : 𝕜}, x ∈ Subsemigr
oup.unitBall 𝕜 ↔ ‖x‖ < 1
参数：𝕜 : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Subsemigroup.mem_unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] {x : 𝕜} :
    x ∈ Subsemigroup.unitBall 𝕜 ↔ ‖x‖ < 1 := by
  simp [Subsemigroup.unitBall]
/-
**Metric.unitBall.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instSemigroup [NonUnitalSeminormedRing 𝕜] : Semigroup (bal
l (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitBall.instSemigroup [NonUnitalSeminormedRing 𝕜] : Semigroup (ball (0 : 𝕜) 1) :=
  inferInstanceAs <| Semigroup (Subsemigroup.unitBall 𝕜)
/-
**Metric.unitBall.instContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] : Continuous
Mul (ball (0 : 𝕜) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
instance Metric.unitBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (ball (0 : 𝕜) 1) :=
  (Subsemigroup.unitBall 𝕜).continuousMul
/-
**Metric.unitBall.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instCommSemigroup [SeminormedCommRing 𝕜] : CommSemigroup (
ball (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitBall.instCommSemigroup [SeminormedCommRing 𝕜] :
    CommSemigroup (ball (0 : 𝕜) 1) :=
  inferInstanceAs <| CommSemigroup (Subsemigroup.unitBall 𝕜)
/-
**Metric.unitBall.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] : HasDistrib
Neg (ball (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : ball (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]
/-
**Metric.unitBall.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NonUnitalSeminormedRing 𝕜] (x y : ↑(Metric.ball 0
 1)), ↑(x * y) = ↑x * ↑y
参数：x y : ↑(Metric.ball 0 1)；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitBall.coe_mul [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
/-
**Metric.unitBall.instZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] : Zero (ball (0 : 
𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] : Zero (ball (0 : 𝕜) 1) :=
  ⟨⟨0, by simp⟩⟩

@[simp, norm_cast]
/-
**Metric.unitBall.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Zero 𝕜] [inst_1 : PseudoMetricSpace 𝕜], ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitBall.coe_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    ((0 : ball (0 : 𝕜) 1) : 𝕜) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Metric.unitBall.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Zero 𝕜] [inst_1 : PseudoMetricSpace 𝕜] {a : ↑(Met
ric.ball 0 1)}, ↑a = 0 ↔ a = 0
参数：Metric.ball 0 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Metric.unitBall.coe_zero`：∀ {𝕜 : Type u_1} [inst : Zero 𝕜] [inst_1 : Pse
udoMetricSpace 𝕜], ↑0 = 0
-/
protected theorem Metric.unitBall.coe_eq_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] {a : ball (0 : 𝕜) 1} :
    (a : 𝕜) = 0 ↔ a = 0 :=
  Subtype.val_injective.eq_iff' unitBall.coe_zero
/-
**Metric.unitBall.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] : Semigr
oupWithZero (ball (0 : 𝕜) 1) where zero_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] :
    SemigroupWithZero (ball (0 : 𝕜) 1) where
  zero_mul _ := Subtype.ext <| zero_mul _
  mul_zero _ := Subtype.ext <| mul_zero _
/-
**Metric.unitBall.instIsLeftCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instIsLeftCancelMulZero [NonUnitalSeminormedRing 𝕜] [IsLef
tCancelMulZero 𝕜] : IsLeftCancelMulZero (ball (0 : 𝕜) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
instance Metric.unitBall.instIsLeftCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsLeftCancelMulZero 𝕜] : IsLeftCancelMulZero (ball (0 : 𝕜) 1) :=
  Subtype.val_injective.isLeftCancelMulZero _ rfl fun _ _ ↦ rfl
/-
**Metric.unitBall.instIsRightCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitBall.instIsRightCancelMulZero [NonUnitalSeminormedRing 𝕜] [IsRi
ghtCancelMulZero 𝕜] : IsRightCancelMulZero (ball (0 : 𝕜) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isRightCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u
_3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   
(f : M₀ → M₀'),   Function.In…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
instance Metric.unitBall.instIsRightCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsRightCancelMulZero 𝕜] : IsRightCancelMulZero (ball (0 : 𝕜) 1) :=
  Subtype.val_injective.isRightCancelMulZero _ rfl fun _ _ ↦ rfl
/-
**Metric.unitBall.instIsCancelMulZero** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitBall
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NonUnitalSeminormedRing 𝕜] [IsCancelMulZero 𝕜], I
sCancelMulZero ↑(Metric.ball 0 1)
参数：Metric.ball 0 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
-/
instance Metric.unitBall.instIsCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsCancelMulZero 𝕜] : IsCancelMulZero (ball (0 : 𝕜) 1) where

/-!
### Algebraic instances for `Metric.closedBall 0 1`
-/

/-- Closed unit ball in a non-unital seminormed ring as a bundled `Subsemigroup`. -/
/-
**Subsemigroup.unitClosedBall** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemigroup.unitClosedBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subs
emigroup 𝕜 where carrier
参数：𝕜 : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Closed unit ball in a non-unital seminormed ring as a bundled `Subsemigroup`.
-/
def Subsemigroup.unitClosedBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le _ _).trans (mul_le_one₀ hx (norm_nonneg _) hy)
/-
**Metric.unitClosedBall.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instSemigroup [NonUnitalSeminormedRing 𝕜] : Semigrou
p (closedBall (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instSemigroup [NonUnitalSeminormedRing 𝕜] :
    Semigroup (closedBall (0 : 𝕜) 1) :=
  inferInstanceAs <| Semigroup (Subsemigroup.unitClosedBall 𝕜)
/-
**Metric.unitClosedBall.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] : HasD
istribNeg (closedBall (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (closedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : closedBall (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl
/-
**Metric.unitClosedBall.instContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] : Cont
inuousMul (closedBall (0 : 𝕜) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
instance Metric.unitClosedBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (closedBall (0 : 𝕜) 1) :=
  (Subsemigroup.unitClosedBall 𝕜).continuousMul

@[simp, norm_cast]
/-
**Metric.unitClosedBall.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitClosedBall
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NonUnitalSeminormedRing 𝕜] (x y : ↑(Metric.closed
Ball 0 1)), ↑(x * y) = ↑x * ↑y
参数：x y : ↑(Metric.closedBall 0 1)；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitClosedBall.coe_mul [NonUnitalSeminormedRing 𝕜]
    (x y : closedBall (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl
/-
**Metric.unitClosedBall.instZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] : Zero (clos
edBall (0 : 𝕜) 1) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    Zero (closedBall (0 : 𝕜) 1) where
  zero := ⟨0, by simp⟩

@[simp, norm_cast]
/-
**Metric.unitClosedBall.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitClosedBal
l`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Zero 𝕜] [inst_1 : PseudoMetricSpace 𝕜], ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Metric.unitClosedBall.coe_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    ((0 : closedBall (0 : 𝕜) 1) : 𝕜) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Metric.unitClosedBall.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitClosed
Ball`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : Zero 𝕜] [inst_1 : PseudoMetricSpace 𝕜] {a : ↑(Met
ric.closedBall 0 1)}, ↑a = 0 ↔ a = 0
参数：Metric.closedBall 0 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Metric.unitClosedBall.coe_zero`：∀ {𝕜 : Type u_1} [inst : Zero 𝕜] [inst_1
 : PseudoMetricSpace 𝕜], ↑0 = 0
-/
protected lemma Metric.unitClosedBall.coe_eq_zero [Zero 𝕜] [PseudoMetricSpace 𝕜]
    {a : closedBall (0 : 𝕜) 1} : (a : 𝕜) = 0 ↔ a = 0 :=
  Subtype.val_injective.eq_iff' unitClosedBall.coe_zero
/-
**Metric.unitClosedBall.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] : 
SemigroupWithZero (closedBall (0 : 𝕜) 1) where zero_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] :
    SemigroupWithZero (closedBall (0 : 𝕜) 1) where
  zero_mul _ := Subtype.ext <| zero_mul _
  mul_zero _ := Subtype.ext <| mul_zero _

/-- Closed unit ball in a seminormed ring as a bundled `Submonoid`. -/
/-
**Submonoid.unitClosedBall** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] :
 Submonoid 𝕜
参数：𝕜 : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Closed unit ball in a seminormed ring as a bundled `Submonoid`.
-/
def Submonoid.unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }

set_option backward.isDefEq.respectTransparency.types false in
/-
**Submonoid.mem_unitClosedBall** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ (𝕜 : Type u_2) [inst : SeminormedRing 𝕜] [inst_1 : NormOneClass 𝕜] {x : 
𝕜}, x ∈ Submonoid.unitClosedBall 𝕜 ↔ ‖x‖ ≤ 1
参数：𝕜 : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Submonoid.mem_unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] {x : 𝕜} :
    x ∈ Submonoid.unitClosedBall 𝕜 ↔ ‖x‖ ≤ 1 := by
  simp [Submonoid.unitClosedBall]
/-
**Metric.unitClosedBall.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instMonoid [SeminormedRing 𝕜] [NormOneClass 𝕜] : Mon
oid (closedBall (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instMonoid [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    Monoid (closedBall (0 : 𝕜) 1) :=
  inferInstanceAs <| Monoid (Submonoid.unitClosedBall 𝕜)
/-
**Metric.unitClosedBall.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instCommMonoid [SeminormedCommRing 𝕜] [NormOneClass 
𝕜] : CommMonoid (closedBall (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instCommMonoid [SeminormedCommRing 𝕜] [NormOneClass 𝕜] :
    CommMonoid (closedBall (0 : 𝕜) 1) :=
  inferInstanceAs <| CommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]
/-
**Metric.unitClosedBall.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitClosedBall
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : SeminormedRing 𝕜] [inst_1 : NormOneClass 𝕜], ↑1 =
 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitClosedBall.coe_one [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    ((1 : closedBall (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[simp, norm_cast]
/-
**Metric.unitClosedBall.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitClosedB
all`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : SeminormedRing 𝕜] [inst_1 : NormOneClass 𝕜] {a : 
↑(Metric.closedBall 0 1)}, ↑a = 1 ↔ a = 1
参数：Metric.closedBall 0 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Metric.unitClosedBall.coe_one`：∀ {𝕜 : Type u_1} [inst : SeminormedRing 𝕜
] [inst_1 : NormOneClass 𝕜], ↑1 = 1
-/
protected theorem Metric.unitClosedBall.coe_eq_one [SeminormedRing 𝕜] [NormOneClass 𝕜]
    {a : closedBall (0 : 𝕜) 1} : (a : 𝕜) = 1 ↔ a = 1 :=
  Subtype.val_injective.eq_iff' unitClosedBall.coe_one

@[simp, norm_cast]
/-
**Metric.unitClosedBall.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitClosedBall
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : SeminormedRing 𝕜] [inst_1 : NormOneClass 𝕜] (x : 
↑(Metric.closedBall 0 1)) (n : ℕ),   ↑(x ^ n) = ↑x ^ n
参数：x : ↑(Metric.closedBall 0 1)；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitClosedBall.coe_pow [SeminormedRing 𝕜] [NormOneClass 𝕜]
    (x : closedBall (0 : 𝕜) 1) (n : ℕ) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl
/-
**Metric.unitClosedBall.instMonoidWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Metric.uni
tClosedBall`。
形式化陈述：{𝕜 : Type u_1} → [inst : SeminormedRing 𝕜] → [NormOneClass 𝕜] → MonoidWith
Zero ↑(Metric.closedBall 0 1)
参数：Metric.closedBall 0 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitClosedBall.instMonoidWithZero [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    MonoidWithZero (closedBall (0 : 𝕜) 1) where
/-
**Metric.unitClosedBall.instIsCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitClosedBall.instIsCancelMulZero [SeminormedRing 𝕜] [IsCancelMulZ
ero 𝕜] [NormOneClass 𝕜] : IsCancelMulZero (closedBall (0 : 𝕜) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [
inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : 
M₀ → M₀'),   Function.In…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
instance Metric.unitClosedBall.instIsCancelMulZero [SeminormedRing 𝕜] [IsCancelMulZero 𝕜]
    [NormOneClass 𝕜] : IsCancelMulZero (closedBall (0 : 𝕜) 1) :=
  Subtype.val_injective.isCancelMulZero _ rfl fun _ _ ↦ rfl

/-!
### Algebraic instances on the unit sphere
-/

/-- Unit sphere in a seminormed ring (with strictly multiplicative norm) as a bundled
`Submonoid`. -/
@[simps]
/-
**Submonoid.unitSphere** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.unitSphere (𝕜 : Type*) [SeminormedRing 𝕜] [NormMulClass 𝕜] [Norm
OneClass 𝕜] : Submonoid 𝕜 where carrier
参数：𝕜 : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unit sphere in a seminormed ring (with strictly multiplicative norm) as a bundle
d
`Submonoid`.
-/
def Submonoid.unitSphere (𝕜 : Type*) [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Submonoid 𝕜 where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one
/-
**Metric.unitSphere.instInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitSphere.instInv [NormedDivisionRing 𝕜] : Inv (sphere (0 : 𝕜) 1) 
where inv x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitSphere.instInv [NormedDivisionRing 𝕜] : Inv (sphere (0 : 𝕜) 1) where
  inv x := ⟨x⁻¹, mem_sphere_zero_iff_norm.2 <| by
    rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩

@[simp, norm_cast]
/-
**Metric.unitSphere.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.unitSphere.coe_inv [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) : 
↑x⁻¹ = (x⁻¹ : 𝕜)
参数：x : sphere (0 : 𝕜) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Metric.unitSphere.coe_inv [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    ↑x⁻¹ = (x⁻¹ : 𝕜) :=
  rfl
/-
**Metric.unitSphere.instDiv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitSphere.instDiv [NormedDivisionRing 𝕜] : Div (sphere (0 : 𝕜) 1) 
where div x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitSphere.instDiv [NormedDivisionRing 𝕜] : Div (sphere (0 : 𝕜) 1) where
  div x y := .mk (x / y) <| mem_sphere_zero_iff_norm.2 <| by
    rw [norm_div, mem_sphere_zero_iff_norm.1 x.2, mem_sphere_zero_iff_norm.1 y.coe_prop, div_one]

@[simp, norm_cast]
/-
**Metric.unitSphere.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitSphere`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NormedDivisionRing 𝕜] (x y : ↑(Metric.sphere 0 1)
), ↑(x / y) = ↑x / ↑y
参数：x y : ↑(Metric.sphere 0 1)；x / y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitSphere.coe_div [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x / y) = (x / y : 𝕜) :=
  rfl
/-
**Metric.unitSphere.instZPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitSphere.instZPow [NormedDivisionRing 𝕜] : Pow (sphere (0 : 𝕜) 1)
 Int where pow x n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitSphere.instZPow [NormedDivisionRing 𝕜] : Pow (sphere (0 : 𝕜) 1) ℤ where
  pow x n := .mk ((x : 𝕜) ^ n) <| by
    rw [mem_sphere_zero_iff_norm, norm_zpow, mem_sphere_zero_iff_norm.1 x.coe_prop, one_zpow]

@[simp, norm_cast]
/-
**Metric.unitSphere.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.unitSphere.coe_zpow [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (
n : Int) : ↑(x ^ n) = (x : 𝕜) ^ n
参数：x : sphere (0 : 𝕜) 1；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Metric.unitSphere.coe_zpow [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℤ) :
    ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl
/-
**Metric.unitSphere.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitSphere.instMonoid [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneC
lass 𝕜] : Monoid (sphere (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitSphere.instMonoid [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Monoid (sphere (0 : 𝕜) 1) :=
  inferInstanceAs <| Monoid (Submonoid.unitSphere 𝕜)
/-
**Metric.unitSphere.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitSphere.instCommMonoid [SeminormedCommRing 𝕜] [NormMulClass 𝕜] [
NormOneClass 𝕜] : CommMonoid (sphere (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.unitSphere.instCommMonoid [SeminormedCommRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    CommMonoid (sphere (0 : 𝕜) 1) :=
  inferInstanceAs <| CommMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]
/-
**Metric.unitSphere.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Metric.unitSphere`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : SeminormedRing 𝕜] [inst_1 : NormMulClass 𝕜] [inst
_2 : NormOneClass 𝕜], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Metric.unitSphere.coe_one [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    ((1 : sphere (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[simp, norm_cast]
/-
**Metric.unitSphere.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.unitSphere.coe_mul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClas
s 𝕜] (x y : sphere (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜)
参数：x y : sphere (0 : 𝕜) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Metric.unitSphere.coe_mul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
    (x y : sphere (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

@[simp, norm_cast]
/-
**Metric.unitSphere.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.unitSphere.coe_pow [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClas
s 𝕜] (x : sphere (0 : 𝕜) 1) (n : Nat) : ↑(x ^ n) = (x : 𝕜) ^ n
参数：x : sphere (0 : 𝕜) 1；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Metric.unitSphere.coe_pow [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
    (x : sphere (0 : 𝕜) 1) (n : ℕ) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

/-- Monoid homomorphism from the unit sphere in a normed division ring to the group of units. -/
/-
**unitSphereToUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitSphereToUnits (𝕜 : Type*) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 ->
* Units 𝕜
参数：𝕜 : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α

--- 原说明 ---
Monoid homomorphism from the unit sphere in a normed division ring to the group 
of units.
-/
def unitSphereToUnits (𝕜 : Type*) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl

@[simp]
/-
**unitSphereToUnits_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unitSphereToUnits_apply_coe [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) 
: (unitSphereToUnits 𝕜 x : 𝕜) = x
参数：x : sphere (0 : 𝕜) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem unitSphereToUnits_apply_coe [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    (unitSphereToUnits 𝕜 x : 𝕜) = x :=
  rfl
/-
**unitSphereToUnits_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unitSphereToUnits_injective [NormedDivisionRing 𝕜] : Function.Injective (u
nitSphereToUnits 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem unitSphereToUnits_injective [NormedDivisionRing 𝕜] :
    Function.Injective (unitSphereToUnits 𝕜) := fun x y h =>
  Subtype.ext <| by convert! congr_arg Units.val h
/-
**Metric.unitSphere.instGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.unitSphere.instGroup [NormedDivisionRing 𝕜] : Group (sphere (0 : 𝕜)
 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
instance Metric.unitSphere.instGroup [NormedDivisionRing 𝕜] : Group (sphere (0 : 𝕜) 1) :=
  fast_instance% unitSphereToUnits_injective.group (unitSphereToUnits 𝕜) (Units.ext rfl)
    (fun _x _y => Units.ext rfl)
    (fun _x => Units.ext rfl) (fun _x _y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Units.ext (Units.val_zpow_eq_zpow_val (unitSphereToUnits 𝕜 x) n).symm
/-
**Metric.sphere.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.sphere.instHasDistribNeg [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormO
neClass 𝕜] : HasDistribNeg (sphere (0 : 𝕜) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.sphere.instHasDistribNeg [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    HasDistribNeg (sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : sphere (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl
/-
**Metric.sphere.instContinuousMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.sphere.instContinuousMul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormO
neClass 𝕜] : ContinuousMul (sphere (0 : 𝕜) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
instance Metric.sphere.instContinuousMul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    ContinuousMul (sphere (0 : 𝕜) 1) :=
  (Submonoid.unitSphere 𝕜).continuousMul
/-
**Metric.sphere.instIsTopologicalGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.sphere.instIsTopologicalGroup [NormedDivisionRing 𝕜] : IsTopologica
lGroup (sphere (0 : 𝕜) 1) where continuous_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.inv₀`：Continuous.inv₀ (hf : Continuous f) (h0 : forall x, f x
 != 0) : Continuous f⁻¹
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
-/
instance Metric.sphere.instIsTopologicalGroup [NormedDivisionRing 𝕜] :
    IsTopologicalGroup (sphere (0 : 𝕜) 1) where
  continuous_inv := (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _
/-
**Metric.sphere.instCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Metric.sphere`。
形式化陈述：{𝕜 : Type u_1} → [inst : NormedField 𝕜] → CommGroup ↑(Metric.sphere 0 1)
参数：Metric.sphere 0 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Metric.sphere.instCommGroup [NormedField 𝕜] : CommGroup (sphere (0 : 𝕜) 1) where
