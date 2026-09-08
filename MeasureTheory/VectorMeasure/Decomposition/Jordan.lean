/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Jordan decomposition

This file proves the existence and uniqueness of the Jordan decomposition for signed measures.
The Jordan decomposition theorem states that, given a signed measure `s`, there exists a
unique pair of mutually singular measures `μ` and `ν`, such that `s = μ - ν`.

The Jordan decomposition theorem for measures is a corollary of the Hahn decomposition theorem and
is useful for the Lebesgue decomposition theorem.

## Main definitions

* `MeasureTheory.JordanDecomposition`: a Jordan decomposition of a measurable space is a
  pair of mutually singular finite measures. We say `j` is a Jordan decomposition of a signed
  measure `s` if `s = j.posPart - j.negPart`.
* `MeasureTheory.SignedMeasure.toJordanDecomposition`: the Jordan decomposition of a
  signed measure.
* `MeasureTheory.SignedMeasure.toJordanDecompositionEquiv`: is the `Equiv` between
  `MeasureTheory.SignedMeasure` and `MeasureTheory.JordanDecomposition` formed by
  `MeasureTheory.SignedMeasure.toJordanDecomposition`.

## Main results

* `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` : the Jordan
  decomposition theorem.
* `MeasureTheory.JordanDecomposition.toSignedMeasure_injective` : the Jordan decomposition of a
  signed measure is unique.

## Tags

Jordan decomposition theorem
-/

@[expose] public section


noncomputable section

open scoped MeasureTheory ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

namespace MeasureTheory

/-- A Jordan decomposition of a measurable space is a pair of mutually singular,
finite measures. -/
@[ext]
/-
**MeasureTheory.JordanDecomposition** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：(α : Type u_2) → [MeasurableSpace α] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Jordan decomposition of a measurable space is a pair of mutually singular,
finite measures.
-/
structure JordanDecomposition (α : Type*) [MeasurableSpace α] where
  /-- Positive part of the Jordan decomposition -/
  posPart : Measure α
  /-- Negative part of the Jordan decomposition -/
  negPart : Measure α
  [posPart_finite : IsFiniteMeasure posPart]
  [negPart_finite : IsFiniteMeasure negPart]
  mutuallySingular : posPart ⟂ₘ negPart

attribute [instance] JordanDecomposition.posPart_finite

attribute [instance] JordanDecomposition.negPart_finite

namespace JordanDecomposition

open Measure VectorMeasure

variable (j : JordanDecomposition α)

/-
**MeasureTheory.JordanDecomposition.instZero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureT
heory.JordanDecomposition`。
形式化陈述：instZero : Zero (JordanDecomposition α) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (JordanDecomposition α) where zero := ⟨0, 0, MutuallySingular.zero_right⟩
/-
**MeasureTheory.JordanDecomposition.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.JordanDecomposition`。
形式化陈述：instInhabited : Inhabited (JordanDecomposition α) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (JordanDecomposition α) where default := 0
/-
**MeasureTheory.JordanDecomposition.instInvolutiveNeg** 是 Mathlib 中的一个实例，位于命名空间 
`MeasureTheory.JordanDecomposition`。
形式化陈述：instInvolutiveNeg : InvolutiveNeg (JordanDecomposition α) where neg j
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
-/
instance instInvolutiveNeg : InvolutiveNeg (JordanDecomposition α) where
  neg j := ⟨j.negPart, j.posPart, j.mutuallySingular.symm⟩
  neg_neg _ := JordanDecomposition.ext rfl rfl
/-
**MeasureTheory.JordanDecomposition.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureT
heory.JordanDecomposition`。
形式化陈述：instSMul : SMul Real>=0 (JordanDecomposition α) where smul r j
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul ℝ≥0 (JordanDecomposition α) where
  smul r j :=
    ⟨r • j.posPart, r • j.negPart,
      MutuallySingular.smul _ (MutuallySingular.smul _ j.mutuallySingular.symm).symm⟩
/-
**MeasureTheory.JordanDecomposition.instSMulReal** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.JordanDecomposition`。
形式化陈述：instSMulReal : SMul Real (JordanDecomposition α) where smul r j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulReal : SMul ℝ (JordanDecomposition α) where
  smul r j := if 0 ≤ r then r.toNNReal • j else -((-r).toNNReal • j)

@[simp]
/-
**MeasureTheory.JordanDecomposition.zero_posPart** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.JordanDecomposition`。
形式化陈述：zero_posPart : (0 : JordanDecomposition α).posPart = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_posPart : (0 : JordanDecomposition α).posPart = 0 :=
  rfl

@[simp]
/-
**MeasureTheory.JordanDecomposition.zero_negPart** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.JordanDecomposition`。
形式化陈述：zero_negPart : (0 : JordanDecomposition α).negPart = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_negPart : (0 : JordanDecomposition α).negPart = 0 :=
  rfl

@[simp]
/-
**MeasureTheory.JordanDecomposition.neg_posPart** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.JordanDecomposition`。
形式化陈述：neg_posPart : (-j).posPart = j.negPart
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_posPart : (-j).posPart = j.negPart :=
  rfl

@[simp]
/-
**MeasureTheory.JordanDecomposition.neg_negPart** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.JordanDecomposition`。
形式化陈述：neg_negPart : (-j).negPart = j.posPart
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_negPart : (-j).negPart = j.posPart :=
  rfl

@[simp]
/-
**MeasureTheory.JordanDecomposition.smul_posPart** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.JordanDecomposition`。
形式化陈述：smul_posPart (r : Real>=0) : (r • j).posPart = r • j.posPart
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_posPart (r : ℝ≥0) : (r • j).posPart = r • j.posPart :=
  rfl

@[simp]
/-
**MeasureTheory.JordanDecomposition.smul_negPart** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.JordanDecomposition`。
形式化陈述：smul_negPart (r : Real>=0) : (r • j).negPart = r • j.negPart
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_negPart (r : ℝ≥0) : (r • j).negPart = r • j.negPart :=
  rfl
/-
**MeasureTheory.JordanDecomposition.real_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.JordanDecomposition`。
形式化陈述：real_smul_def (r : Real) (j : JordanDecomposition α) : r • j = if 0 <= r t
hen r.toNNReal • j else -((-r).toNNReal • j)
参数：r : Real；j : JordanDecomposition α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem real_smul_def (r : ℝ) (j : JordanDecomposition α) :
    r • j = if 0 ≤ r then r.toNNReal • j else -((-r).toNNReal • j) :=
  rfl

@[simp]
/-
**MeasureTheory.JordanDecomposition.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.JordanDecomposition`。
形式化陈述：coe_smul (r : Real>=0) : (r : Real) • j = r • j
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_def`：real_smul_def (r : Real
) (j : JordanDecomposition α) : r • j = if 0 <= r then r.toNNReal • j else -((-r
).toNNReal • j)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
theorem coe_smul (r : ℝ≥0) : (r : ℝ) • j = r • j := by
  rw [real_smul_def, if_pos (NNReal.coe_nonneg r), Real.toNNReal_coe]
/-
**MeasureTheory.JordanDecomposition.real_smul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.JordanDecomposition`。
形式化陈述：real_smul_nonneg (r : Real) (hr : 0 <= r) : r • j = r.toNNReal • j
参数：r : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem real_smul_nonneg (r : ℝ) (hr : 0 ≤ r) : r • j = r.toNNReal • j :=
  dif_pos hr
/-
**MeasureTheory.JordanDecomposition.real_smul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.JordanDecomposition`。
形式化陈述：real_smul_neg (r : Real) (hr : r < 0) : r • j = -((-r).toNNReal • j)
参数：r : Real；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem real_smul_neg (r : ℝ) (hr : r < 0) : r • j = -((-r).toNNReal • j) :=
  dif_neg (not_le.2 hr)
/-
**MeasureTheory.JordanDecomposition.real_smul_posPart_nonneg** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：real_smul_posPart_nonneg (r : Real) (hr : 0 <= r) : (r • j).posPart = r.to
NNReal • j.posPart
参数：r : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_def`：real_smul_def (r : Real
) (j : JordanDecomposition α) : r • j = if 0 <= r then r.toNNReal • j else -((-r
).toNNReal • j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.smul_posPart`：smul_posPart (r : Real>=
0) : (r • j).posPart = r • j.posPart
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem real_smul_posPart_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (r • j).posPart = r.toNNReal • j.posPart := by
  rw [real_smul_def, ← smul_posPart, if_pos hr]
/-
**MeasureTheory.JordanDecomposition.real_smul_negPart_nonneg** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：real_smul_negPart_nonneg (r : Real) (hr : 0 <= r) : (r • j).negPart = r.to
NNReal • j.negPart
参数：r : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_def`：real_smul_def (r : Real
) (j : JordanDecomposition α) : r • j = if 0 <= r then r.toNNReal • j else -((-r
).toNNReal • j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.smul_negPart`：smul_negPart (r : Real>=
0) : (r • j).negPart = r • j.negPart
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem real_smul_negPart_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (r • j).negPart = r.toNNReal • j.negPart := by
  rw [real_smul_def, ← smul_negPart, if_pos hr]
/-
**MeasureTheory.JordanDecomposition.real_smul_posPart_neg** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：real_smul_posPart_neg (r : Real) (hr : r < 0) : (r • j).posPart = (-r).toN
NReal • j.negPart
参数：r : Real；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_def`：real_smul_def (r : Real
) (j : JordanDecomposition α) : r • j = if 0 <= r then r.toNNReal • j else -((-r
).toNNReal • j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.smul_negPart`：smul_negPart (r : Real>=
0) : (r • j).negPart = r • j.negPart
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MeasureTheory.JordanDecomposition.neg_posPart`：neg_posPart : (-j).posPar
t = j.negPart
-/
theorem real_smul_posPart_neg (r : ℝ) (hr : r < 0) :
    (r • j).posPart = (-r).toNNReal • j.negPart := by
  rw [real_smul_def, ← smul_negPart, if_neg (not_le.2 hr), neg_posPart]
/-
**MeasureTheory.JordanDecomposition.real_smul_negPart_neg** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：real_smul_negPart_neg (r : Real) (hr : r < 0) : (r • j).negPart = (-r).toN
NReal • j.posPart
参数：r : Real；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_def`：real_smul_def (r : Real
) (j : JordanDecomposition α) : r • j = if 0 <= r then r.toNNReal • j else -((-r
).toNNReal • j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.smul_posPart`：smul_posPart (r : Real>=
0) : (r • j).posPart = r • j.posPart
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MeasureTheory.JordanDecomposition.neg_negPart`：neg_negPart : (-j).negPar
t = j.posPart
-/
theorem real_smul_negPart_neg (r : ℝ) (hr : r < 0) :
    (r • j).negPart = (-r).toNNReal • j.posPart := by
  rw [real_smul_def, ← smul_posPart, if_neg (not_le.2 hr), neg_negPart]

/-- The signed measure associated with a Jordan decomposition. -/
/-
**MeasureTheory.JordanDecomposition.toSignedMeasure** 是 Mathlib 中的一个定义，位于命名空间 `M
easureTheory.JordanDecomposition`。
形式化陈述：toSignedMeasure : SignedMeasure α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart

--- 原说明 ---
The signed measure associated with a Jordan decomposition.
-/
def toSignedMeasure : SignedMeasure α :=
  j.posPart.toSignedMeasure - j.negPart.toSignedMeasure
/-
**MeasureTheory.JordanDecomposition.toSignedMeasure_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：toSignedMeasure_zero : (0 : JordanDecomposition α).toSignedMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_sub_apply`：toSignedMeasure_sub_app
ly {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {i : Set α} (hi : M
easurableSet i) : (μ.toSignedMeasure …
· 使用定理 `MeasureTheory.JordanDecomposition.zero_posPart`：zero_posPart : (0 : Jord
anDecomposition α).posPart = 0
· 使用定理 `MeasureTheory.JordanDecomposition.zero_negPart`：zero_negPart : (0 : Jord
anDecomposition α).negPart = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem toSignedMeasure_zero : (0 : JordanDecomposition α).toSignedMeasure = 0 := by
  ext1 i hi
  rw [toSignedMeasure, toSignedMeasure_sub_apply hi, zero_posPart, zero_negPart, sub_self,
    FunLike.coe_zero, Pi.zero_apply]
/-
**MeasureTheory.JordanDecomposition.toSignedMeasure_neg** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.JordanDecomposition`。
形式化陈述：toSignedMeasure_neg : (-j).toSignedMeasure = -j.toSignedMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_sub_apply`：toSignedMeasure_sub_app
ly {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {i : Set α} (hi : M
easurableSet i) : (μ.toSignedMeasure …
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `MeasureTheory.JordanDecomposition.neg_posPart`：neg_posPart : (-j).posPar
t = j.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.neg_negPart`：neg_negPart : (-j).negPar
t = j.posPart
-/
theorem toSignedMeasure_neg : (-j).toSignedMeasure = -j.toSignedMeasure := by
  ext1 i hi
  rw [neg_apply, toSignedMeasure, toSignedMeasure, toSignedMeasure_sub_apply hi,
    toSignedMeasure_sub_apply hi, neg_sub, neg_posPart, neg_negPart]
/-
**MeasureTheory.JordanDecomposition.toSignedMeasure_smul** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：toSignedMeasure_smul (r : Real>=0) : (r • j).toSignedMeasure = r • j.toSig
nedMeasure
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_sub_apply`：toSignedMeasure_sub_app
ly {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {i : Set α} (hi : M
easurableSet i) : (μ.toSignedMeasure …
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.JordanDecomposition.smul_posPart`：smul_posPart (r : Real>=
0) : (r • j).posPart = r • j.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.smul_negPart`：smul_negPart (r : Real>=
0) : (r • j).negPart = r • j.negPart
· 使用定理 `MeasureTheory.measureReal_nnreal_smul_apply`：∀ {α : Type u_1} {x : Measu
rableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} (c : NNReal),   (c • μ).
real s = ↑c * μ.real s
-/
theorem toSignedMeasure_smul (r : ℝ≥0) : (r • j).toSignedMeasure = r • j.toSignedMeasure := by
  ext1 i hi
  rw [_root_.smul_apply, toSignedMeasure, toSignedMeasure,
    toSignedMeasure_sub_apply hi, toSignedMeasure_sub_apply hi, smul_sub, smul_posPart,
    smul_negPart, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  rfl

/-- A Jordan decomposition provides a Hahn decomposition. -/
/-
**MeasureTheory.JordanDecomposition.exists_compl_positive_negative** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：exists_compl_positive_negative : exists S : Set α, MeasurableSet S ∧ j.toS
ignedMeasure <=[S] 0 ∧ 0 <=[Sᶜ] j.toSignedMeasure ∧ j.posPart S = 0 ∧ j.negPart 
Sᶜ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.mutuallySingular`：∀ {α : Type u_2} [in
st : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   self.pos
Part.MutuallySingular self.negPart
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_of_subset_le`：restrict_
le_restrict_of_subset_le {i : Set α} (h : forall ⦃j⦄, MeasurableSet j -> j subse
teq i -> v j <= w j) : v <=[i] w
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_sub_apply`：toSignedMeasure_sub_app
ly {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {i : Set α} (hi : M
easurableSet i) : (μ.toSignedMeasure …
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
A Jordan decomposition provides a Hahn decomposition.
-/
theorem exists_compl_positive_negative :
    ∃ S : Set α,
      MeasurableSet S ∧
        j.toSignedMeasure ≤[S] 0 ∧
          0 ≤[Sᶜ] j.toSignedMeasure ∧ j.posPart S = 0 ∧ j.negPart Sᶜ = 0 := by
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutuallySingular
  refine ⟨S, hS₁, ?_, ?_, hS₂, hS₃⟩
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure, toSignedMeasure_sub_apply hA, measureReal_def,
      show j.posPart A = 0 from nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁), ENNReal.toReal_zero,
      zero_sub, neg_le, zero_apply, neg_zero]
    exact ENNReal.toReal_nonneg
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure, toSignedMeasure_sub_apply hA, measureReal_def (μ := j.negPart),
      show j.negPart A = 0 from nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁), ENNReal.toReal_zero,
      sub_zero]
    exact ENNReal.toReal_nonneg

end JordanDecomposition

namespace SignedMeasure

open JordanDecomposition Measure Set VectorMeasure

variable {s : SignedMeasure α}

/-- Given a signed measure `s`, `s.toJordanDecomposition` is the Jordan decomposition `j`,
such that `s = j.toSignedMeasure`. This property is known as the Jordan decomposition
theorem, and is shown by
`MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`. -/
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition** 是 Mathlib 中的一个定义，位于命名空间 `M
easureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition (s : SignedMeasure α) : JordanDecomposition α
参数：s : SignedMeasure α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SignedMeasure.exists_compl_positive_negative`：exists_compl
_positive_negative (s : SignedMeasure α) : exists i : Set α, MeasurableSet i ∧ 0
 <=[i] s ∧ s <=[iᶜ] 0

--- 原说明 ---
Given a signed measure `s`, `s.toJordanDecomposition` is the Jordan decompositio
n `j`,
such that `s = j.toSignedMeasure`. This property is known as the Jordan decompos
ition
theorem, and is shown by
`MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`.
-/
def toJordanDecomposition (s : SignedMeasure α) : JordanDecomposition α :=
  let i := s.exists_compl_positive_negative.choose
  have hi := s.exists_compl_positive_negative.choose_spec
  { posPart := s.toMeasureOfZeroLE i hi.1 hi.2.1
    negPart := s.toMeasureOfLEZero iᶜ hi.1.compl hi.2.2
    posPart_finite := inferInstance
    negPart_finite := inferInstance
    mutuallySingular := by
      refine ⟨iᶜ, hi.1.compl, ?_, ?_⟩
      · rw [toMeasureOfZeroLE_apply _ _ hi.1 hi.1.compl]; simp
      · rw [toMeasureOfLEZero_apply _ _ hi.1.compl hi.1.compl.compl]; simp }
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_spec** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_spec (s : SignedMeasure α) : exists (i : Set α) (hi₁
 : MeasurableSet i) (hi₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0), s.toJordanDecompositio
n.posPart = s.toMeasureOfZeroLE i hi₁ hi₂ ∧ s.toJordanDecomposition.negPart = s.
toMeasureOfLEZero iᶜ hi₁.compl hi₃
参数：s : SignedMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SignedMeasure.exists_compl_positive_negative`：exists_compl
_positive_negative (s : SignedMeasure α) : exists i : Set α, MeasurableSet i ∧ 0
 <=[i] s ∧ s <=[iᶜ] 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem toJordanDecomposition_spec (s : SignedMeasure α) :
    ∃ (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) (hi₃ : s ≤[iᶜ] 0),
      s.toJordanDecomposition.posPart = s.toMeasureOfZeroLE i hi₁ hi₂ ∧
        s.toJordanDecomposition.negPart = s.toMeasureOfLEZero iᶜ hi₁.compl hi₃ := by
  set i := s.exists_compl_positive_negative.choose
  obtain ⟨hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative.choose_spec
  exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩

/-- **The Jordan decomposition theorem**: Given a signed measure `s`, there exists a pair of
mutually singular measures `μ` and `ν` such that `s = μ - ν`. In this case, the measures `μ`
and `ν` are given by `s.toJordanDecomposition.posPart` and
`s.toJordanDecomposition.negPart` respectively.

Note that we use `MeasureTheory.JordanDecomposition.toSignedMeasure` to represent the
signed measure corresponding to
`s.toJordanDecomposition.posPart - s.toJordanDecomposition.negPart`. -/
@[simp]
/-
**MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toSignedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDe
composition.toSignedMeasure = s
参数：s : SignedMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_spec`：toJordanDecompos
ition_spec (s : SignedMeasure α) : exists (i : Set α) (hi₁ : MeasurableSet i) (h
i₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0), s.toJord…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.toSignedMeasure.congr_simp`：∀ {α : Type u_1} {m : 
MeasurableSpace α} (μ μ_1 : MeasureTheory.Measure α) (e_μ : μ = μ_1)   [hμ : Mea
sureTheory.IsFiniteMeasure μ], μ.toSig…
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_sub_apply`：toSignedMeasure_sub_app
ly {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {i : Set α} (hi : M
easurableSet i) : (μ.toSignedMeasure …
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_real_apply`：toMeasureOfZer
oLE_real_apply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) 
: (s.toMeasureOfZeroLE i hi₁ hi).real j = s (i…
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_real_apply`：toMeasureOfLEZ
ero_real_apply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) 
: (s.toMeasureOfLEZero i hi₁ hi).real j = -s (…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Disjoint.inf_right`：Disjoint.inf_right (h : Disjoint a b) : Disjoint a (
b ⊓ c)
· 使用定理 `Disjoint.inf_left`：Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ 
c) b
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s

--- 原说明 ---
**The Jordan decomposition theorem**: Given a signed measure `s`, there exists a
 pair of
mutually singular measures `μ` and `ν` such that `s = μ - ν`. In this case, the 
measures `μ`
and `ν` are given by `s.toJordanDecomposition.posPart` and
`s.toJordanDecomposition.negPart` respectively.

Note that we use `MeasureTheory.JordanDecomposition.toSignedMeasure` to represen
t the
signed measure corresponding to
`s.toJordanDecomposition.posPart - s.toJordanDecomposition.negPart`.
-/
theorem toSignedMeasure_toJordanDecomposition (s : SignedMeasure α) :
    s.toJordanDecomposition.toSignedMeasure = s := by
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.toJordanDecomposition_spec
  simp only [JordanDecomposition.toSignedMeasure, hμ, hν]
  ext k hk
  rw [toSignedMeasure_sub_apply hk, toMeasureOfZeroLE_real_apply _ hi₂ hi₁ hk,
    toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl hk]
  simp only [sub_neg_eq_add]
  rw [← of_union _ (MeasurableSet.inter hi₁ hk) (MeasurableSet.inter hi₁.compl hk),
    Set.inter_comm i, Set.inter_comm iᶜ, Set.inter_union_compl _ _]
  exact (disjoint_compl_right.inf_left _).inf_right _

section

variable {u v w : Set α}

/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a positive set `u`. -/
/-
**MeasureTheory.SignedMeasure.subset_positive_null_set** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SignedMeasure`。
形式化陈述：subset_positive_null_set (hu : MeasurableSet u) (hv : MeasurableSet v) (hw
 : MeasurableSet w) (hsu : 0 <=[u] s) (hw₁ : s w = 0) (hw₂ : w subseteq u) (hwt 
: v subseteq w) : s v = 0
参数：hu : MeasurableSet u；hv : MeasurableSet v；hw : MeasurableSet w；hsu : 0 <=[u] 
s；hw₁ : s w = 0；hw₂ : w subseteq u；hwt : v subseteq w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_subset`：restrict_le_res
trict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w) (hij : j su
bseteq i) : v <=[j] w
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A subset `v` of a null-set `w` has zero measure if `w` is a subset of a positive
 set `u`.
-/
theorem subset_positive_null_set (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : 0 ≤[u] s) (hw₁ : s w = 0) (hw₂ : w ⊆ u) (hwt : v ⊆ w) :
    s v = 0 := by
  have : s v + s (w \ v) = 0 := by
    rw [← hw₁, ← of_union Set.disjoint_sdiff_right hv (hw.diff hv), Set.union_sdiff_self,
      Set.union_eq_self_of_subset_left hwt]
  have h₁ := nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂))
  have h₂ : 0 ≤ s (w \ v) :=
    nonneg_of_zero_le_restrict _
      (restrict_le_restrict_subset _ _ hu hsu (sdiff_subset.trans hw₂))
  linarith

/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a negative set `u`. -/
/-
**MeasureTheory.SignedMeasure.subset_negative_null_set** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SignedMeasure`。
形式化陈述：subset_negative_null_set (hu : MeasurableSet u) (hv : MeasurableSet v) (hw
 : MeasurableSet w) (hsu : s <=[u] 0) (hw₁ : s w = 0) (hw₂ : w subseteq u) (hwt 
: v subseteq w) : s v = 0
参数：hu : MeasurableSet u；hv : MeasurableSet v；hw : MeasurableSet w；hsu : s <=[u] 
0；hw₁ : s w = 0；hw₂ : w subseteq u；hwt : v subseteq w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.SignedMeasure.subset_positive_null_set`：subset_positive_nu
ll_set (hu : MeasurableSet u) (hv : MeasurableSet v) (hw : MeasurableSet w) (hsu
 : 0 <=[u] s) (hw₁ : s w = 0) (hw₂ : w sub…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg_iff`：neg_le_neg_iff {i : Set α} (
hi : MeasurableSet i) : -w <=[i] -v ↔ v <=[i] w
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…

--- 原说明 ---
A subset `v` of a null-set `w` has zero measure if `w` is a subset of a negative
 set `u`.
-/
theorem subset_negative_null_set (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : s ≤[u] 0) (hw₁ : s w = 0) (hw₂ : w ⊆ u) (hwt : v ⊆ w) :
    s v = 0 := by
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu
  have := subset_positive_null_set hu hv hw hsu
  simp only [neg_apply, neg_eq_zero] at this
  exact this hw₁ hw₂ hwt

open scoped symmDiff

/-- If the symmetric difference of two positive sets is a null-set, then so are the differences
between the two sets. -/
/-
**MeasureTheory.SignedMeasure.of_sdiff_eq_zero_of_symmDiff_eq_zero_positive** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：of_sdiff_eq_zero_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv :
 MeasurableSet v) (hsu : 0 <=[u] s) (hsv : 0 <=[v] s) (hs : s (u ∆ v) = 0) : s (
u \ v) = 0 ∧ s (v \ u) = 0
参数：hu : MeasurableSet u；hv : MeasurableSet v；hsu : 0 <=[u] s；hsv : 0 <=[v] s；hs 
: s (u ∆ v) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If the symmetric difference of two positive sets is a null-set, then so are the 
differences
between the two sets.
-/
theorem of_sdiff_eq_zero_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hsu : 0 ≤[u] s) (hsv : 0 ≤[v] s) (hs : s (u ∆ v) = 0) : s (u \ v) = 0 ∧ s (v \ u) = 0 := by
  rw [restrict_le_restrict_iff] at hsu hsv
  on_goal 1 =>
    have a := hsu (hu.diff hv) sdiff_subset
    have b := hsv (hv.diff hu) sdiff_subset
    rw [Set.symmDiff_def,
      of_union (v := s) (Set.disjoint_of_subset_left sdiff_subset disjoint_sdiff_self_right)
        (hu.diff hv) (hv.diff hu)] at hs
    rw [zero_apply] at a b
    constructor
  · linarith
  · linarith
  · assumption
  · assumption

@[deprecated (since := "2026-06-03")]
alias of_diff_eq_zero_of_symmDiff_eq_zero_positive := of_sdiff_eq_zero_of_symmDiff_eq_zero_positive

/-- If the symmetric difference of two negative sets is a null-set, then so are the differences
between the two sets. -/
/-
**MeasureTheory.SignedMeasure.of_sdiff_eq_zero_of_symmDiff_eq_zero_negative** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：of_sdiff_eq_zero_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv :
 MeasurableSet v) (hsu : s <=[u] 0) (hsv : s <=[v] 0) (hs : s (u ∆ v) = 0) : s (
u \ v) = 0 ∧ s (v \ u) = 0
参数：hu : MeasurableSet u；hv : MeasurableSet v；hsu : s <=[u] 0；hsv : s <=[v] 0；hs 
: s (u ∆ v) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.SignedMeasure.of_sdiff_eq_zero_of_symmDiff_eq_zero_positiv
e`：of_sdiff_eq_zero_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : Me
asurableSet v) (hsu : 0 <=[u] s) (hsv : 0 <=[v] s) (hs : s (u ∆…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg_iff`：neg_le_neg_iff {i : Set α} (
hi : MeasurableSet i) : -w <=[i] -v ↔ v <=[i] w
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
If the symmetric difference of two negative sets is a null-set, then so are the 
differences
between the two sets.
-/
theorem of_sdiff_eq_zero_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hsu : s ≤[u] 0) (hsv : s ≤[v] 0) (hs : s (u ∆ v) = 0) : s (u \ v) = 0 ∧ s (v \ u) = 0 := by
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv, neg_zero] at hsv
  have := of_sdiff_eq_zero_of_symmDiff_eq_zero_positive hu hv hsu hsv
  simp only [neg_apply, neg_eq_zero] at this
  exact this hs

@[deprecated (since := "2026-06-03")]
alias of_diff_eq_zero_of_symmDiff_eq_zero_negative := of_sdiff_eq_zero_of_symmDiff_eq_zero_negative
/-
**MeasureTheory.SignedMeasure.of_inter_eq_of_symmDiff_eq_zero_positive** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：of_inter_eq_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : Meas
urableSet v) (hw : MeasurableSet w) (hsu : 0 <=[u] s) (hsv : 0 <=[v] s) (hs : s 
(u ∆ v) = 0) : s (w inter u) = s (w inter v)
参数：hu : MeasurableSet u；hv : MeasurableSet v；hw : MeasurableSet w；hsu : 0 <=[u] 
s；hsv : 0 <=[v] s；hs : s (u ∆ v) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SignedMeasure.subset_positive_null_set`：subset_positive_nu
ll_set (hu : MeasurableSet u) (hv : MeasurableSet v) (hw : MeasurableSet w) (hsu
 : 0 <=[u] s) (hw₁ : s w = 0) (hw₂ : w sub…
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.symmDiff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ 
: Set α},   MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (symmDiff s₁ s₂)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_union`：restrict_le_rest
rict_union (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w) (hj₁ : MeasurableSet j) (hj
₂ : v <=[j] w) : v <=[i union j] w
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.symmDiff_subset_union`：symmDiff_subset_union : s ∆ t subseteq s unio
n t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_symmDiff_distrib_left`：inter_symmDiff_distrib_left (s t u : Se
t α) : s inter t ∆ u = (s inter t) ∆ (s inter u)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.SignedMeasure.of_sdiff_eq_zero_of_symmDiff_eq_zero_positiv
e`：of_sdiff_eq_zero_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : Me
asurableSet v) (hsu : 0 <=[u] s) (hsv : 0 <=[v] s) (hs : s (u ∆…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_subset`：restrict_le_res
trict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w) (hij : j su
bseteq i) : v <=[j] w
· 使用定理 `MeasureTheory.VectorMeasure.of_sdiff_of_sdiff_eq_zero`：of_sdiff_of_sdiff
_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h' : v (B 
\ A) = 0) : v (A \ B) + v B = v A
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem of_inter_eq_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : 0 ≤[u] s) (hsv : 0 ≤[v] s) (hs : s (u ∆ v) = 0) :
    s (w ∩ u) = s (w ∩ v) := by
  have hwuv : s ((w ∩ u) ∆ (w ∩ v)) = 0 := by
    refine
      subset_positive_null_set (hu.union hv) ((hw.inter hu).symmDiff (hw.inter hv))
        (hu.symmDiff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs
        Set.symmDiff_subset_union ?_
    rw [← Set.inter_symmDiff_distrib_left]
    exact Set.inter_subset_right
  obtain ⟨huv, hvu⟩ :=
    of_sdiff_eq_zero_of_symmDiff_eq_zero_positive (hw.inter hu) (hw.inter hv)
      (restrict_le_restrict_subset _ _ hu hsu (w.inter_subset_right))
      (restrict_le_restrict_subset _ _ hv hsv (w.inter_subset_right)) hwuv
  rw [← of_sdiff_of_sdiff_eq_zero (hw.inter hu) (hw.inter hv) hvu, huv, zero_add]
/-
**MeasureTheory.SignedMeasure.of_inter_eq_of_symmDiff_eq_zero_negative** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：of_inter_eq_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : Meas
urableSet v) (hw : MeasurableSet w) (hsu : s <=[u] 0) (hsv : s <=[v] 0) (hs : s 
(u ∆ v) = 0) : s (w inter u) = s (w inter v)
参数：hu : MeasurableSet u；hv : MeasurableSet v；hw : MeasurableSet w；hsu : s <=[u] 
0；hsv : s <=[v] 0；hs : s (u ∆ v) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.SignedMeasure.of_inter_eq_of_symmDiff_eq_zero_positive`：of
_inter_eq_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSe
t v) (hw : MeasurableSet w) (hsu : 0 <=[u] s) (hsv : 0 <=[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg_iff`：neg_le_neg_iff {i : Set α} (
hi : MeasurableSet i) : -w <=[i] -v ↔ v <=[i] w
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem of_inter_eq_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : s ≤[u] 0) (hsv : s ≤[v] 0) (hs : s (u ∆ v) = 0) :
    s (w ∩ u) = s (w ∩ v) := by
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv, neg_zero] at hsv
  have := of_inter_eq_of_symmDiff_eq_zero_positive hu hv hw hsu hsv
  simp only [neg_apply, neg_inj, neg_eq_zero] at this
  exact this hs

end

end SignedMeasure

namespace JordanDecomposition

open Measure VectorMeasure SignedMeasure Function

/-
**MeasureTheory.JordanDecomposition.eq_of_posPart_eq_posPart** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.JordanDecomposition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eq_of_posPart_eq_posPart {j₁ j₂ : JordanDecomposition α}
    (hj : j₁.posPart = j₂.posPart) (hj' : j₁.toSignedMeasure = j₂.toSignedMeasure) : j₁ = j₂ := by
  ext1
  · exact hj
  · rw [← toSignedMeasure_eq_toSignedMeasure_iff]
    unfold toSignedMeasure at hj'
    simp_rw [hj, sub_right_inj] at hj'
    exact hj'

/-- The Jordan decomposition of a signed measure is unique. -/
/-
**MeasureTheory.JordanDecomposition.toSignedMeasure_injective** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：toSignedMeasure_injective : Injective @JordanDecomposition.toSignedMeasure
 α _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.exists_compl_positive_negative`：exists
_compl_positive_negative : exists S : Set α, MeasurableSet S ∧ j.toSignedMeasure
 <=[S] 0 ∧ 0 <=[Sᶜ] j.toSignedMeasure ∧ j.posPart S = …
· 使用定理 `MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative`：of_symm
Diff_compl_positive_negative {s : SignedMeasure α} {i j : Set α} (hi : Measurabl
eSet i) (hj : MeasurableSet j) (hi' : 0 <=[i] s ∧ s <…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan.0.Meas
ureTheory.JordanDecomposition.eq_of_posPart_eq_posPart`：∀ {α : Type u_1} [inst :
 MeasurableSpace α] {j₁ j₂ : MeasureTheory.JordanDecomposition α},   j₁.posPart 
= j₂.posPart → j₁.toSignedMeasure = …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_sub_apply`：toSignedMeasure_sub_app
ly {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {i : Set α} (hi : M
easurableSet i) : (μ.toSignedMeasure …
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measureReal_union`：measureReal_union (hd : Disjoint s₁ s₂)
 (h : MeasurableSet s₂) (h₁ : μ s₁ != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The Jordan decomposition of a signed measure is unique.
-/
theorem toSignedMeasure_injective : Injective <| @JordanDecomposition.toSignedMeasure α _ := by
  /- The main idea is that two Jordan decompositions of a signed measure provide two
    Hahn decompositions for that measure. Then, from `of_symmDiff_compl_positive_negative`,
    the symmetric difference of the two Hahn decompositions has measure zero, thus, allowing us to
    show the equality of the underlying measures of the Jordan decompositions. -/
  intro j₁ j₂ hj
  -- obtain the two Hahn decompositions from the Jordan decompositions
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ := j₁.exists_compl_positive_negative
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ := j₂.exists_compl_positive_negative
  rw [← hj] at hT₂ hT₃
  -- the symmetric differences of the two Hahn decompositions have measure zero
  obtain ⟨hST₁, -⟩ :=
    of_symmDiff_compl_positive_negative hS₁.compl hT₁.compl ⟨hS₃, (compl_compl S).symm ▸ hS₂⟩
      ⟨hT₃, (compl_compl T).symm ▸ hT₂⟩
  -- it suffices to show the Jordan decompositions have the same positive parts
  refine eq_of_posPart_eq_posPart ?_ hj
  ext1 i hi
  -- we see that the positive parts of the two Jordan decompositions are equal to their
  -- associated signed measures restricted on their associated Hahn decompositions
  have hμ₁ : j₁.posPart.real i = j₁.toSignedMeasure (i ∩ Sᶜ) := by
    rw [toSignedMeasure, toSignedMeasure_sub_apply (hi.inter hS₁.compl),
      measureReal_def (μ := j₁.negPart),
      show j₁.negPart (i ∩ Sᶜ) = 0 from
        nonpos_iff_eq_zero.1 (hS₅ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, sub_zero]
    conv_lhs => rw [← Set.inter_union_compl i S]
    rw [measureReal_union, measureReal_def,
      show j₁.posPart (i ∩ S) = 0 from
        nonpos_iff_eq_zero.1 (hS₄ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, zero_add]
    · refine
        Set.disjoint_of_subset_left Set.inter_subset_right
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right)
    · exact hi.inter hS₁.compl
  have hμ₂ : j₂.posPart.real i = j₂.toSignedMeasure (i ∩ Tᶜ) := by
    rw [toSignedMeasure, toSignedMeasure_sub_apply (hi.inter hT₁.compl),
      measureReal_def (μ := j₂.negPart),
      show j₂.negPart (i ∩ Tᶜ) = 0 from
        nonpos_iff_eq_zero.1 (hT₅ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, sub_zero]
    conv_lhs => rw [← Set.inter_union_compl i T]
    rw [measureReal_union, measureReal_def,
      show j₂.posPart (i ∩ T) = 0 from
        nonpos_iff_eq_zero.1 (hT₄ ▸ measure_mono Set.inter_subset_right),
      ENNReal.toReal_zero, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_right
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right)
    · exact hi.inter hT₁.compl
  -- since the two signed measures associated with the Jordan decompositions are the same,
  -- and the symmetric difference of the Hahn decompositions have measure zero, the result follows
  rw [← measureReal_eq_measureReal_iff, hμ₁, hμ₂, ← hj]
  exact of_inter_eq_of_symmDiff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁

@[simp]
/-
**MeasureTheory.JordanDecomposition.toJordanDecomposition_toSignedMeasure** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.JordanDecomposition`。
形式化陈述：toJordanDecomposition_toSignedMeasure (j : JordanDecomposition α) : j.toSi
gnedMeasure.toJordanDecomposition = j
参数：j : JordanDecomposition α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_injective`：toSignedMea
sure_injective : Injective @JordanDecomposition.toSignedMeasure α _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toJordanDecomposition_toSignedMeasure (j : JordanDecomposition α) :
    j.toSignedMeasure.toJordanDecomposition = j :=
  (@toSignedMeasure_injective _ _ j j.toSignedMeasure.toJordanDecomposition (by simp)).symm

end JordanDecomposition

namespace SignedMeasure

open JordanDecomposition

/-- `MeasureTheory.SignedMeasure.toJordanDecomposition` and
`MeasureTheory.JordanDecomposition.toSignedMeasure` form an `Equiv`. -/
@[simps apply symm_apply]
/-
**MeasureTheory.SignedMeasure.toJordanDecompositionEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecompositionEquiv (α : Type*) [MeasurableSpace α] : SignedMeasure
 α ≃ JordanDecomposition α where toFun
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `MeasureTheory.JordanDecomposition.toJordanDecomposition_toSignedMeasure`
：toJordanDecomposition_toSignedMeasure (j : JordanDecomposition α) : j.toSignedM
easure.toJordanDecomposition = j

--- 原说明 ---
`MeasureTheory.SignedMeasure.toJordanDecomposition` and
`MeasureTheory.JordanDecomposition.toSignedMeasure` form an `Equiv`.
-/
def toJordanDecompositionEquiv (α : Type*) [MeasurableSpace α] :
    SignedMeasure α ≃ JordanDecomposition α where
  toFun := toJordanDecomposition
  invFun := toSignedMeasure
  left_inv := toSignedMeasure_toJordanDecomposition
  right_inv := toJordanDecomposition_toSignedMeasure
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_zero : (0 : SignedMeasure α).toJordanDecomposition =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_injective`：toSignedMea
sure_injective : Injective @JordanDecomposition.toSignedMeasure α _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_zero`：toSignedMeasure_
zero : (0 : JordanDecomposition α).toSignedMeasure = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toJordanDecomposition_zero : (0 : SignedMeasure α).toJordanDecomposition = 0 := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_zero]
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_neg** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_neg (s : SignedMeasure α) : (-s).toJordanDecompositi
on = -s.toJordanDecomposition
参数：s : SignedMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_injective`：toSignedMea
sure_injective : Injective @JordanDecomposition.toSignedMeasure α _
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_neg`：toSignedMeasure_n
eg : (-j).toSignedMeasure = -j.toSignedMeasure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toJordanDecomposition_neg (s : SignedMeasure α) :
    (-s).toJordanDecomposition = -s.toJordanDecomposition := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_neg]
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_smul** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_smul (s : SignedMeasure α) (r : Real>=0) : (r • s).t
oJordanDecomposition = r • s.toJordanDecomposition
参数：s : SignedMeasure α；r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_injective`：toSignedMea
sure_injective : Injective @JordanDecomposition.toSignedMeasure α _
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_smul`：toSignedMeasure_
smul (r : Real>=0) : (r • j).toSignedMeasure = r • j.toSignedMeasure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toJordanDecomposition_smul (s : SignedMeasure α) (r : ℝ≥0) :
    (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_smul]
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real_nonneg** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toJordanDecomposition_smul_real_nonneg (s : SignedMeasure α) (r : ℝ)
    (hr : 0 ≤ r) : (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  lift r to ℝ≥0 using hr
  rw [JordanDecomposition.coe_smul, ← toJordanDecomposition_smul]
  rfl
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_smul_real (s : SignedMeasure α) (r : Real) : (r • s)
.toJordanDecomposition = r • s.toJordanDecomposition
参数：s : SignedMeasure α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan.0.Meas
ureTheory.SignedMeasure.toJordanDecomposition_smul_real_nonneg`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (s : MeasureTheory.SignedMeasure α) (r : ℝ),   0 ≤ r
 → (r • s).toJordanDecomposition = r • s.toJ…
· 使用定理 `MeasureTheory.JordanDecomposition.ext`：∀ {α : Type u_2} {inst : Measurab
leSpace α} {x y : MeasureTheory.JordanDecomposition α},   x.posPart = y.posPart 
→ x.negPart = y.negPart → x…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_posPart_neg`：real_smul_posPa
rt_neg (r : Real) (hr : r < 0) : (r • j).posPart = (-r).toNNReal • j.negPart
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_neg`：toJordanDecomposi
tion_neg (s : SignedMeasure α) : (-s).toJordanDecomposition = -s.toJordanDecompo
sition
· 使用定理 `MeasureTheory.JordanDecomposition.neg_posPart`：neg_posPart : (-j).posPar
t = j.negPart
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.smul_negPart`：smul_negPart (r : Real>=
0) : (r • j).negPart = r • j.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_nonneg`：real_smul_nonneg (r 
: Real) (hr : 0 <= r) : r • j = r.toNNReal • j
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_negPart_neg`：real_smul_negPa
rt_neg (r : Real) (hr : r < 0) : (r • j).negPart = (-r).toNNReal • j.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.neg_negPart`：neg_negPart : (-j).negPar
t = j.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.smul_posPart`：smul_posPart (r : Real>=
0) : (r • j).posPart = r • j.posPart
-/
theorem toJordanDecomposition_smul_real (s : SignedMeasure α) (r : ℝ) :
    (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  by_cases! hr : 0 ≤ r
  · exact toJordanDecomposition_smul_real_nonneg s r hr
  · ext1
    · rw [real_smul_posPart_neg _ _ hr,
        show r • s = -(-r • s) by rw [neg_smul, neg_neg], toJordanDecomposition_neg, neg_posPart,
        toJordanDecomposition_smul_real_nonneg, ← smul_negPart, real_smul_nonneg]
      all_goals exact Left.nonneg_neg_iff.2 hr.le
    · rw [real_smul_negPart_neg _ _ hr,
        show r • s = -(-r • s) by rw [neg_smul, neg_neg], toJordanDecomposition_neg, neg_negPart,
        toJordanDecomposition_smul_real_nonneg, ← smul_posPart, real_smul_nonneg]
      all_goals exact Left.nonneg_neg_iff.2 hr.le
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_eq** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_eq {s : SignedMeasure α} {j : JordanDecomposition α}
 (h : s = j.toSignedMeasure) : s.toJordanDecomposition = j
参数：h : s = j.toSignedMeasure。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.JordanDecomposition.toJordanDecomposition_toSignedMeasure`
：toJordanDecomposition_toSignedMeasure (j : JordanDecomposition α) : j.toSignedM
easure.toJordanDecomposition = j
-/
theorem toJordanDecomposition_eq {s : SignedMeasure α} {j : JordanDecomposition α}
    (h : s = j.toSignedMeasure) : s.toJordanDecomposition = j := by
  rw [h, toJordanDecomposition_toSignedMeasure]

/-- The total variation of a signed measure. -/
/-
**MeasureTheory.SignedMeasure.totalVariation** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.SignedMeasure`。
形式化陈述：totalVariation (s : SignedMeasure α) : Measure α
参数：s : SignedMeasure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The total variation of a signed measure.
-/
def totalVariation (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart
/-
**MeasureTheory.SignedMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SignedMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : SignedMeasure α) : IsFiniteMeasure s.totalVariation := by
  unfold totalVariation; infer_instance
/-
**MeasureTheory.SignedMeasure.totalVariation_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SignedMeasure`。
形式化陈述：totalVariation_zero : (0 : SignedMeasure α).totalVariation = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_zero`：toJordanDecompos
ition_zero : (0 : SignedMeasure α).toJordanDecomposition = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem totalVariation_zero : (0 : SignedMeasure α).totalVariation = 0 := by
  simp [totalVariation, toJordanDecomposition_zero]
/-
**MeasureTheory.SignedMeasure.totalVariation_neg** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SignedMeasure`。
形式化陈述：totalVariation_neg (s : SignedMeasure α) : (-s).totalVariation = s.totalVa
riation
参数：s : SignedMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_neg`：toJordanDecomposi
tion_neg (s : SignedMeasure α) : (-s).toJordanDecomposition = -s.toJordanDecompo
sition
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem totalVariation_neg (s : SignedMeasure α) : (-s).totalVariation = s.totalVariation := by
  simp [totalVariation, toJordanDecomposition_neg, add_comm]

/-- Pointwise form of `toSignedMeasure_toJordanDecomposition`. -/
/-
**MeasureTheory.SignedMeasure.apply_eq_posPart_real_sub_negPart_real** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：apply_eq_posPart_real_sub_negPart_real (s : SignedMeasure α) {i : Set α} (
hi : MeasurableSet i) : s i = s.toJordanDecomposition.posPart.real i - s.toJorda
nDecomposition.negPart.real i
参数：s : SignedMeasure α；hi : MeasurableSet i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise form of `toSignedMeasure_toJordanDecomposition`.
-/
theorem apply_eq_posPart_real_sub_negPart_real (s : SignedMeasure α) {i : Set α}
    (hi : MeasurableSet i) :
    s i = s.toJordanDecomposition.posPart.real i - s.toJordanDecomposition.negPart.real i := by
  grind [Measure.toSignedMeasure_sub_apply, toSignedMeasure, toSignedMeasure_toJordanDecomposition]
/-
**MeasureTheory.SignedMeasure.null_of_totalVariation_zero** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：null_of_totalVariation_zero (s : SignedMeasure α) {i : Set α} (hs : s.tota
lVariation i = 0) : s i = 0
参数：s : SignedMeasure α；hs : s.totalVariation i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSubApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `MeasureTheory.Measure.coe_add`：coe_add {_m : MeasurableSpace α} (μ₁ μ₂ :
 Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem null_of_totalVariation_zero (s : SignedMeasure α) {i : Set α}
    (hs : s.totalVariation i = 0) : s i = 0 := by
  rw [totalVariation, Measure.coe_add, Pi.add_apply, add_eq_zero] at hs
  by_cases hi : MeasurableSet i
  · rw [← toSignedMeasure_toJordanDecomposition s, toSignedMeasure]
    simp [hi, measureReal_def, hs.1, hs.2]
  · simp [hi]
/-
**MeasureTheory.SignedMeasure.absolutelyContinuous_ennreal_iff** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：absolutelyContinuous_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure 
α Real>=0∞) : s ≪ᵥ μ ↔ s.totalVariation ≪ μ.ennrealToMeasure
参数：s : SignedMeasure α；μ : VectorMeasure α Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_spec`：toJordanDecompos
ition_spec (s : SignedMeasure α) : exists (i : Set α) (hi₁ : MeasurableSet i) (h
i₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0), s.toJord…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply`：toMeasureOfLEZero_a
pply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.AbsolutelyContinuous.ennrealToMeasure`：ennre
alToMeasure {μ : VectorMeasure α Real>=0∞} : (forall ⦃s : Set α⦄, μ.ennrealToMea
sure s = 0 -> v s = 0) ↔ v ≪ᵥ μ
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s :
 Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0) : v ≪ᵥ w
· 使用定理 `MeasureTheory.SignedMeasure.null_of_totalVariation_zero`：null_of_totalVa
riation_zero (s : SignedMeasure α) {i : Set α} (hs : s.totalVariation i = 0) : s
 i = 0
（共 31 条，此处仅展示前 30 条）
-/
theorem absolutelyContinuous_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    s ≪ᵥ μ ↔ s.totalVariation ≪ μ.ennrealToMeasure := by
  constructor <;> intro h
  · refine Measure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    rw [totalVariation, Measure.add_apply, hpos, hneg, toMeasureOfZeroLE_apply _ _ _ hS₁,
      toMeasureOfLEZero_apply _ _ _ hS₁]
    rw [← VectorMeasure.AbsolutelyContinuous.ennrealToMeasure] at h
    simp [h (measure_mono_null (i.inter_subset_right) hS₂),
      h (measure_mono_null (iᶜ.inter_subset_right) hS₂)]
  · refine VectorMeasure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    rw [← VectorMeasure.ennrealToMeasure_apply hS₁] at hS₂
    exact null_of_totalVariation_zero s (h hS₂)
/-
**MeasureTheory.SignedMeasure.totalVariation_absolutelyContinuous_iff** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：totalVariation_absolutelyContinuous_iff (s : SignedMeasure α) (μ : Measure
 α) : s.totalVariation ≪ μ ↔ s.toJordanDecomposition.posPart ≪ μ ∧ s.toJordanDec
omposition.negPart ≪ μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem totalVariation_absolutelyContinuous_iff (s : SignedMeasure α) (μ : Measure α) :
    s.totalVariation ≪ μ ↔
      s.toJordanDecomposition.posPart ≪ μ ∧ s.toJordanDecomposition.negPart ≪ μ := by
  constructor <;> intro h
  · constructor
    all_goals
      refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
      have := h hS₂
      rw [totalVariation, Measure.add_apply, add_eq_zero] at this
    exacts [this.1, this.2]
  · refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
    rw [totalVariation, Measure.add_apply, h.1 hS₂, h.2 hS₂, add_zero]

-- TODO: Generalize to vector measures once total variation on vector measures is defined
/-
**MeasureTheory.SignedMeasure.mutuallySingular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SignedMeasure`。
形式化陈述：mutuallySingular_iff (s t : SignedMeasure α) : s ⟂ᵥ t ↔ s.totalVariation ⟂
ₘ t.totalVariation
参数：s t : SignedMeasure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_spec`：toJordanDecompos
ition_spec (s : SignedMeasure α) : exists (i : Set α) (hi₁ : MeasurableSet i) (h
i₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0), s.toJord…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply`：toMeasureOfLEZero_a
pply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SignedMeasure.null_of_totalVariation_zero`：null_of_totalVa
riation_zero (s : SignedMeasure α) {i : Set α} (hs : s.totalVariation i = 0) : s
 i = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem mutuallySingular_iff (s t : SignedMeasure α) :
    s ⟂ᵥ t ↔ s.totalVariation ⟂ₘ t.totalVariation := by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hipos, hineg⟩ := s.toJordanDecomposition_spec
    obtain ⟨j, hj₁, hj₂, hj₃, hjpos, hjneg⟩ := t.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hipos, hineg, toMeasureOfZeroLE_apply _ _ _ hmeas,
        toMeasureOfLEZero_apply _ _ _ hmeas]
      simp [hu₁ _ Set.inter_subset_right]
    · rw [totalVariation, Measure.add_apply, hjpos, hjneg,
        toMeasureOfZeroLE_apply _ _ _ hmeas.compl,
        toMeasureOfLEZero_apply _ _ _ hmeas.compl]
      simp [hu₂ _ Set.inter_subset_right]
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    exact
      ⟨u, hmeas, fun t htu => null_of_totalVariation_zero _ (measure_mono_null htu hu₁),
        fun t htv => null_of_totalVariation_zero _ (measure_mono_null htv hu₂)⟩
/-
**MeasureTheory.SignedMeasure.mutuallySingular_ennreal_iff** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：mutuallySingular_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α Re
al>=0∞) : s ⟂ᵥ μ ↔ s.totalVariation ⟂ₘ μ.ennrealToMeasure
参数：s : SignedMeasure α；μ : VectorMeasure α Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_spec`：toJordanDecompos
ition_spec (s : SignedMeasure α) : exists (i : Set α) (hi₁ : MeasurableSet i) (h
i₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0), s.toJord…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.VectorMeasure.nonneg_of_zero_le_restrict`：nonneg_of_zero_l
e_restrict (hi₂ : 0 <=[i] v) : 0 <= v i
· 使用定理 `MeasureTheory.VectorMeasure.zero_le_restrict_subset`：zero_le_restrict_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply`：toMeasureOfZeroLE_a
pply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.VectorMeasure.neg_le_neg`：∀ {α : Type u_1} {m : Measurable
Space α} {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : AddCommGroup M]   
[inst_2 : PartialOrder M] [I…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply`：toMeasureOfLEZero_a
pply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) : s.toMeas
ureOfLEZero i hi₁ hi j = ((↑) : Real>=0 -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.mk`：mk (s : Set α) (hs : Me
asurableSet s) (h₁ : forall t subseteq s, MeasurableSet t -> v t = 0) (h₂ : fora
ll t subseteq sᶜ, MeasurableSet t -> …
· 使用定理 `MeasureTheory.SignedMeasure.null_of_totalVariation_zero`：null_of_totalVa
riation_zero (s : SignedMeasure α) {i : Set α} (hs : s.totalVariation i = 0) : s
 i = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mutuallySingular_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    s ⟂ᵥ μ ↔ s.totalVariation ⟂ₘ μ.ennrealToMeasure := by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hpos, hneg, toMeasureOfZeroLE_apply _ _ _ hmeas,
        toMeasureOfLEZero_apply _ _ _ hmeas]
      simp [hu₁ _ Set.inter_subset_right]
    · rw [VectorMeasure.ennrealToMeasure_apply hmeas.compl]
      exact hu₂ _ (Set.Subset.refl _)
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    refine
      VectorMeasure.MutuallySingular.mk u hmeas
        (fun t htu _ => null_of_totalVariation_zero _ (measure_mono_null htu hu₁)) fun t htv hmt =>
        ?_
    rw [← VectorMeasure.ennrealToMeasure_apply hmt]
    exact measure_mono_null htv hu₂
/-
**MeasureTheory.SignedMeasure.totalVariation_mutuallySingular_iff** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：totalVariation_mutuallySingular_iff (s : SignedMeasure α) (μ : Measure α) 
: s.totalVariation ⟂ₘ μ ↔ s.toJordanDecomposition.posPart ⟂ₘ μ ∧ s.toJordanDecom
position.negPart ⟂ₘ μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left_iff`：add_left_iff : μ₁ +
 μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
-/
theorem totalVariation_mutuallySingular_iff (s : SignedMeasure α) (μ : Measure α) :
    s.totalVariation ⟂ₘ μ ↔
      s.toJordanDecomposition.posPart ⟂ₘ μ ∧ s.toJordanDecomposition.negPart ⟂ₘ μ :=
  Measure.MutuallySingular.add_left_iff

end SignedMeasure

end MeasureTheory

