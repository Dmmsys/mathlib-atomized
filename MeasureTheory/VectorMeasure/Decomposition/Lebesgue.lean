/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem for signed measures. The Lebesgue decomposition
theorem states that, given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ`
and a measurable function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect
to `ν`.

## Main definitions

* `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition` : A signed measure `s` is said to have
  Lebesgue decomposition with respect to a measure `μ` if both the positive part and negative part
  of `s` have Lebesgue decomposition with respect to `μ`.
* `MeasureTheory.SignedMeasure.singularPart` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `MeasureTheory.SignedMeasure.rnDeriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

## Tags

Lebesgue decomposition theorem
-/

@[expose] public section


noncomputable section

open scoped MeasureTheory NNReal ENNReal

open Set

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

namespace MeasureTheory

namespace SignedMeasure

open Measure

/-- A signed measure `s` is said to `HaveLebesgueDecomposition` with respect to a measure `μ`
if the positive part and the negative part of `s` both `HaveLebesgueDecomposition` with
respect to `μ`. -/
/-
**MeasureTheory.SignedMeasure.HaveLebesgueDecomposition** 是 Mathlib 中的一个归纳类型，位于命
名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：{α : Type u_1} → {m : MeasurableSpace α} → MeasureTheory.SignedMeasure α →
 MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A signed measure `s` is said to `HaveLebesgueDecomposition` with respect to a me
asure `μ`
if the positive part and the negative part of `s` both `HaveLebesgueDecompositio
n` with
respect to `μ`.
-/
class HaveLebesgueDecomposition (s : SignedMeasure α) (μ : Measure α) : Prop where
  posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
  negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.posPart

attribute [instance] HaveLebesgueDecomposition.negPart
/-
**MeasureTheory.SignedMeasure.not_haveLebesgueDecomposition_iff** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) : 
¬s.HaveLebesgueDecomposition μ ↔ ¬s.toJordanDecomposition.posPart.HaveLebesgueDe
composition μ ∨ ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.posPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.negPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
-/
theorem not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) :
    ¬s.HaveLebesgueDecomposition μ ↔
      ¬s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ ∨
        ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩

-- `inferInstance` directly does not work
-- see Note [lower instance priority]
/-
**MeasureTheory.SignedMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SignedMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (s : SignedMeasure α)
    (μ : Measure α) [SigmaFinite μ] : s.HaveLebesgueDecomposition μ where
  posPart := inferInstance
  negPart := inferInstance
/-
**MeasureTheory.SignedMeasure.haveLebesgueDecomposition_neg** 是 Mathlib 中的一个实例，位
于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：haveLebesgueDecomposition_neg (s : SignedMeasure α) (μ : Measure α) [s.Hav
eLebesgueDecomposition μ] : (-s).HaveLebesgueDecomposition μ where posPart
参数：s : SignedMeasure α；μ : Measure α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_neg`：toJordanDecomposi
tion_neg (s : SignedMeasure α) : (-s).toJordanDecomposition = -s.toJordanDecompo
sition
· 使用定理 `MeasureTheory.JordanDecomposition.neg_posPart`：neg_posPart : (-j).posPar
t = j.negPart
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.negPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
· 使用定理 `MeasureTheory.JordanDecomposition.neg_negPart`：neg_negPart : (-j).negPar
t = j.posPart
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.posPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
-/
instance haveLebesgueDecomposition_neg (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] : (-s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_negPart]
    infer_instance
/-
**MeasureTheory.SignedMeasure.haveLebesgueDecomposition_smul** 是 Mathlib 中的一个实例，
位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：haveLebesgueDecomposition_smul (s : SignedMeasure α) (μ : Measure α) [s.Ha
veLebesgueDecomposition μ] (r : Real>=0) : (r • s).HaveLebesgueDecomposition μ w
here posPart
参数：s : SignedMeasure α；μ : Measure α；r : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_smul`：toJordanDecompos
ition_smul (s : SignedMeasure α) (r : Real>=0) : (r • s).toJordanDecomposition =
 r • s.toJordanDecomposition
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.JordanDecomposition.smul_posPart`：smul_posPart (r : Real>=
0) : (r • j).posPart = r • j.posPart
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.posPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
· 使用定理 `MeasureTheory.JordanDecomposition.smul_negPart`：smul_negPart (r : Real>=
0) : (r • j).negPart = r • j.negPart
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.negPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
-/
instance haveLebesgueDecomposition_smul (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ≥0) : (r • s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_smul, JordanDecomposition.smul_negPart]
    infer_instance
/-
**MeasureTheory.SignedMeasure.haveLebesgueDecomposition_smul_real** 是 Mathlib 中的
一个实例，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：haveLebesgueDecomposition_smul_real (s : SignedMeasure α) (μ : Measure α) 
[s.HaveLebesgueDecomposition μ] (r : Real) : (r • s).HaveLebesgueDecomposition μ
参数：s : SignedMeasure α；μ : Measure α；r : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
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
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real`：toJordanDec
omposition_smul_real (s : SignedMeasure α) (r : Real) : (r • s).toJordanDecompos
ition = r • s.toJordanDecomposition
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_posPart_neg`：real_smul_posPa
rt_neg (r : Real) (hr : r < 0) : (r • j).posPart = (-r).toNNReal • j.negPart
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.negPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
· 使用定理 `MeasureTheory.JordanDecomposition.real_smul_negPart_neg`：real_smul_negPa
rt_neg (r : Real) (hr : r < 0) : (r • j).negPart = (-r).toNNReal • j.posPart
· 使用定理 `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.posPart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {s : MeasureTheory.SignedMeasure α} {μ : Measure
Theory.Measure α}   [self : s.HaveLebesgueDecomposi…
-/
instance haveLebesgueDecomposition_smul_real (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ) : (r • s).HaveLebesgueDecomposition μ := by
  by_cases! hr : 0 ≤ r
  · lift r to ℝ≥0 using hr
    exact s.haveLebesgueDecomposition_smul μ _
  · refine
      { posPart := by
          rw [toJordanDecomposition_smul_real, JordanDecomposition.real_smul_posPart_neg _ _ hr]
          infer_instance
        negPart := by
          rw [toJordanDecomposition_smul_real, JordanDecomposition.real_smul_negPart_neg _ _ hr]
          infer_instance }

/-- Given a signed measure `s` and a measure `μ`, `s.singularPart μ` is the signed measure
such that `s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s` and
`s.singularPart μ` is mutually singular with respect to `μ`. -/
/-
**MeasureTheory.SignedMeasure.singularPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.SignedMeasure`。
形式化陈述：singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α
参数：s : SignedMeasure α；μ : Measure α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
Given a signed measure `s` and a measure `μ`, `s.singularPart μ` is the signed m
easure
such that `s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s` and
`s.singularPart μ` is mutually singular with respect to `μ`.
-/
def singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α :=
  (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure

section

/-
**MeasureTheory.SignedMeasure.singularPart_mutuallySingular** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) : s.to
JordanDecomposition.posPart.singularPart μ ⟂ₘ s.toJordanDecomposition.negPart.si
ngularPart μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono`：mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ
₂ <= μ₁) (hν : ν₂ <= ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.MutuallySingular.singularPart`：∀ {α : Type u_1} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.MutuallySingular ν → 
∀ (ν' : MeasureTheory.Measure α), (μ.sing…
· 使用定理 `MeasureTheory.JordanDecomposition.mutuallySingular`：∀ {α : Type u_2} [in
st : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   self.pos
Part.MutuallySingular self.negPart
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
-/
theorem singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) :
    s.toJordanDecomposition.posPart.singularPart μ ⟂ₘ
      s.toJordanDecomposition.negPart.singularPart μ :=
  (s.toJordanDecomposition.mutuallySingular.singularPart μ).mono le_rfl (singularPart_le _ _)
/-
**MeasureTheory.SignedMeasure.singularPart_totalVariation** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) : (s.sin
gularPart μ).totalVariation = s.toJordanDecomposition.posPart.singularPart μ + s
.toJordanDecomposition.negPart.singularPart μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_mutuallySingular`：singularPart_
mutuallySingular (s : SignedMeasure α) (μ : Measure α) : s.toJordanDecomposition
.posPart.singularPart μ ⟂ₘ s.toJordanDecomposit…
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure_injective`：toSignedMea
sure_injective : Injective @JordanDecomposition.toSignedMeasure α _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.SignedMeasure.singularPart.eq_1`：∀ {α : Type u_1} {m : Mea
surableSpace α} (s : MeasureTheory.SignedMeasure α) (μ : MeasureTheory.Measure α
),   s.singularPart μ =     (s.toJo…
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
-/
theorem singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) :
    (s.singularPart μ).totalVariation =
      s.toJordanDecomposition.posPart.singularPart μ +
        s.toJordanDecomposition.negPart.singularPart μ := by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine JordanDecomposition.toSignedMeasure_injective ?_
    rw [toSignedMeasure_toJordanDecomposition, singularPart, JordanDecomposition.toSignedMeasure]
  rw [totalVariation, this]

nonrec theorem mutuallySingular_singularPart (s : SignedMeasure α) (μ : Measure α) :
    singularPart s μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  rw [mutuallySingular_ennreal_iff, singularPart_totalVariation,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact (mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)

end

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`rnDeriv s μ` satisfies `μ.withDensityᵥ (s.rnDeriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`
and can be found in `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`. -/
/-
**MeasureTheory.SignedMeasure.rnDeriv** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.S
ignedMeasure`。
形式化陈述：rnDeriv (s : SignedMeasure α) (μ : Measure α) : α -> Real
参数：s : SignedMeasure α；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Radon-Nikodym derivative between a signed measure and a positive measure.

`rnDeriv s μ` satisfies `μ.withDensityᵥ (s.rnDeriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is
 known as
`MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`
and can be found in `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.le
an`.
-/
def rnDeriv (s : SignedMeasure α) (μ : Measure α) : α → ℝ := fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal

-- The generated equation theorem is the form of `rnDeriv s μ x = ...`.
/-
**MeasureTheory.SignedMeasure.rnDeriv_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SignedMeasure`。
形式化陈述：rnDeriv_def (s : SignedMeasure α) (μ : Measure α) : rnDeriv s μ = fun x =>
 (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal - (s.toJordanDecomposition
.negPart.rnDeriv μ x).toReal
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rnDeriv_def (s : SignedMeasure α) (μ : Measure α) : rnDeriv s μ = fun x =>
    (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
      (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal :=
  rfl

variable {s t : SignedMeasure α}

@[fun_prop]
/-
**MeasureTheory.SignedMeasure.measurable_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SignedMeasure`。
形式化陈述：measurable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Measurable (rnD
eriv s μ)
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.rnDeriv_def`：rnDeriv_def (s : SignedMeasure 
α) (μ : Measure α) : rnDeriv s μ = fun x => (s.toJordanDecomposition.posPart.rnD
eriv μ x).toReal - (s.toJorda…
· 使用定理 `Measurable.fun_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ 
G], Meas…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
-/
theorem measurable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Measurable (rnDeriv s μ) := by
  rw [rnDeriv_def]
  fun_prop
/-
**MeasureTheory.SignedMeasure.integrable_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SignedMeasure`。
形式化陈述：integrable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Integrable (rnD
eriv s μ) μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.hasFiniteIntegral_toReal_of_lintegral_ne_top`：hasFiniteInt
egral_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hf : ∫⁻ x, f x ∂μ != ∞) : 
HasFiniteIntegral (fun x => (f x).toReal) μ
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
-/
theorem integrable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ := by
  refine Integrable.sub ?_ ?_ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable
        fun_prop
      exact hasFiniteIntegral_toReal_of_lintegral_ne_top (lintegral_rnDeriv_lt_top _ μ).ne

variable (s μ)

/-- **The Lebesgue Decomposition theorem between a signed measure and a measure**:
Given a signed measure `s` and a σ-finite measure `μ`, there exist a signed measure `t` and a
measurable and integrable function `f`, such that `t` is mutually singular with respect to `μ`
and `s = t + μ.withDensityᵥ f`. In this case `t = s.singularPart μ` and
`f = s.rnDeriv μ`. -/
/-
**MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：singularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : 
s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.SignedMeasure.singularPart.eq_1`：∀ {α : Type u_1} {m : Mea
surableSpace α} (s : MeasureTheory.SignedMeasure α) (μ : MeasureTheory.Measure α
),   s.singularPart μ =     (s.toJo…
· 使用定理 `MeasureTheory.SignedMeasure.rnDeriv_def`：rnDeriv_def (s : SignedMeasure 
α) (μ : Measure α) : rnDeriv s μ = fun x => (s.toJordanDecomposition.posPart.rnD
eriv μ x).toReal - (s.toJorda…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.withDensityᵥ_sub'`：withDensityᵥ_sub' (hf : Integrable f μ)
 (hg : Integrable g μ) : (μ.withDensityᵥ fun x => f x - g x) = μ.withDensityᵥ f 
- μ.withDensityᵥ g
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.isFiniteMeasure_withDensity`：isFiniteMeasure_withDensity {
f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) : IsFiniteMeasure (μ.withDensity f)
· 使用定理 `MeasureTheory.withDensityᵥ_toReal`：withDensityᵥ_toReal {f : α -> Real>=0
∞} (hfm : AEMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) != ∞) : (μ.withDensityᵥ fun x =
> (f x).toReal) = @toSi…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_add`：toSignedMeasure_add (μ ν : Me
asure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : (μ + ν).toSignedMeasure = μ.t
oSignedMeasure + ν.toSignedMeas…
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
**The Lebesgue Decomposition theorem between a signed measure and a measure**:
Given a signed measure `s` and a σ-finite measure `μ`, there exist a signed meas
ure `t` and a
measurable and integrable function `f`, such that `t` is mutually singular with 
respect to `μ`
and `s = t + μ.withDensityᵥ f`. In this case `t = s.singularPart μ` and
`f = s.rnDeriv μ`.
-/
theorem singularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] :
    s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s := by
  conv_rhs =>
    rw [← toSignedMeasure_toJordanDecomposition s, JordanDecomposition.toSignedMeasure]
  rw [singularPart, rnDeriv_def,
    withDensityᵥ_sub' (integrable_toReal_of_lintegral_ne_top _ _)
      (integrable_toReal_of_lintegral_ne_top _ _),
    withDensityᵥ_toReal, withDensityᵥ_toReal, sub_eq_add_neg, sub_eq_add_neg,
    add_comm (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure, ← add_assoc,
    add_assoc (-(s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure),
    ← toSignedMeasure_add, add_comm, ← add_assoc, ← neg_add, ← toSignedMeasure_add, add_comm,
    ← sub_eq_add_neg]
  · convert! rfl
    -- `convert rfl` much faster than `congr`
    · exact s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ
    · rw [add_comm]
      exact s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ
  all_goals
    first
    | exact (lintegral_rnDeriv_lt_top _ _).ne
    | measurability

variable {s μ}
/-
**MeasureTheory.SignedMeasure.jordanDecomposition_add_withDensity_mutuallySingul
ar** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：jordanDecomposition_add_withDensity_mutuallySingular {f : α -> Real} (hf :
 Measurable f) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) : (t.toJordanDecomposition.
posPart + μ.withDensity fun x : α => ENNReal.ofReal (f x)) ⟂ₘ t.toJordanDecompos
ition.negPart + μ.withDensity fun x : α => ENNReal.ofReal (-f x)
参数：hf : Measurable f；htμ : t ⟂ᵥ μ.toENNRealVectorMeasure。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left`：add_left (h₁ : ν₁ ⟂ₘ μ)
 (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_right`：add_right (h₁ : μ ⟂ₘ ν
₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂
· 使用定理 `MeasureTheory.JordanDecomposition.mutuallySingular`：∀ {α : Type u_2} [in
st : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   self.pos
Part.MutuallySingular self.negPart
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure`：enn
realToMeasure_toENNRealVectorMeasure (μ : Measure α) : ennrealToMeasure (toENNRe
alVectorMeasure μ) = μ
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation_mutuallySingular_iff`：totalVa
riation_mutuallySingular_iff (s : SignedMeasure α) (μ : Measure α) : s.totalVari
ation ⟂ₘ μ ↔ s.toJordanDecomposition.posPart ⟂ₘ μ ∧ s…
· 使用定理 `MeasureTheory.SignedMeasure.mutuallySingular_ennreal_iff`：mutuallySingul
ar_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α Real>=0∞) : s ⟂ᵥ μ ↔ s
.totalVariation ⟂ₘ μ.ennrealToMeasure
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.withDensity_ofReal_mutuallySingular`：withDensity_ofReal_mu
tuallySingular {f : α -> Real} (hf : Measurable f) : (μ.withDensity fun x => ENN
Real.ofReal <| f x) ⟂ₘ μ.withDensity fu…
-/
theorem jordanDecomposition_add_withDensity_mutuallySingular {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) :
    (t.toJordanDecomposition.posPart + μ.withDensity fun x : α => ENNReal.ofReal (f x)) ⟂ₘ
      t.toJordanDecomposition.negPart + μ.withDensity fun x : α => ENNReal.ofReal (-f x) := by
  rw [mutuallySingular_ennreal_iff, totalVariation_mutuallySingular_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  exact
    ((JordanDecomposition.mutuallySingular _).add_right
          (htμ.1.mono_ac (refl _) (withDensity_absolutelyContinuous _ _))).add_left
      ((htμ.2.symm.mono_ac (withDensity_absolutelyContinuous _ _) (refl _)).add_right
        (withDensity_ofReal_mutuallySingular hf))
/-
**MeasureTheory.SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：toJordanDecomposition_eq_of_eq_add_withDensity {f : α -> Real} (hf : Measu
rable f) (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s 
= t + μ.withDensityᵥ f) : s.toJordanDecomposition = @JordanDecomposition.mk α _ 
(t.toJordanDecomposition.posPart + μ.withDensity fun x => ENNReal.ofReal (f x)) 
(t.toJordanDecomposition.negPart + μ.withDensity fun x => ENNReal.ofReal (-f x))
 (by have
参数：hf : Measurable f；hfi : Integrable f μ；htμ : t ⟂ᵥ μ.toENNRealVectorMeasure；ha
dd : s = t + μ.withDensityᵥ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.isFiniteMeasure_withDensity_ofReal`：isFiniteMeasure_withDe
nsity_ofReal {f : α -> Real} (hfi : HasFiniteIntegral f μ) : IsFiniteMeasure (μ.
withDensity fun x => ENNReal.ofReal <|…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_eq`：toJordanDecomposit
ion_eq {s : SignedMeasure α} {j : JordanDecomposition α} (h : s = j.toSignedMeas
ure) : s.toJordanDecomposition = j
· 使用定理 `MeasureTheory.SignedMeasure.jordanDecomposition_add_withDensity_mutually
Singular`：jordanDecomposition_add_withDensity_mutuallySingular {f : α -> Real} (
hf : Measurable f) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) : (t.toJordan…
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
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSubApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_apply_measurable`：toSignedMeasure_
apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α} (hi : Measurabl
eSet i) : μ.toSignedMeasure i = μ.real i
· 使用定理 `MeasureTheory.measureReal_add_apply`：measureReal_add_apply {μ₁ μ₂ : Meas
ure α} (h₁ : μ₁ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.JordanDecomposition.toSignedMeasure.eq_1`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (j : MeasureTheory.JordanDecomposition α),   j.toSig
nedMeasure = j.posPart.toSignedMeasure - j.n…
· 使用定理 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`：toSig
nedMeasure_toJordanDecomposition (s : SignedMeasure α) : s.toJordanDecomposition
.toSignedMeasure = s
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `MeasureTheory.withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_p
art`：withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part {f : α -> Rea
l} (hfi : Integrable f μ) : μ.withDensityᵥ f = @toSignedMeasure α…
-/
theorem toJordanDecomposition_eq_of_eq_add_withDensity {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.toJordanDecomposition =
      @JordanDecomposition.mk α _
        (t.toJordanDecomposition.posPart + μ.withDensity fun x => ENNReal.ofReal (f x))
        (t.toJordanDecomposition.negPart + μ.withDensity fun x => ENNReal.ofReal (-f x))
        (by have := isFiniteMeasure_withDensity_ofReal hfi.2; infer_instance)
        (by have := isFiniteMeasure_withDensity_ofReal hfi.neg.2; infer_instance)
        (jordanDecomposition_add_withDensity_mutuallySingular hf htμ) := by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine toJordanDecomposition_eq ?_
  simp_rw [JordanDecomposition.toSignedMeasure, hadd]
  ext i hi
  rw [_root_.sub_apply, toSignedMeasure_apply_measurable hi,
      toSignedMeasure_apply_measurable hi, measureReal_add_apply, measureReal_add_apply,
      add_sub_add_comm, ← toSignedMeasure_apply_measurable hi,
      ← toSignedMeasure_apply_measurable hi, ← _root_.sub_apply,
      ← JordanDecomposition.toSignedMeasure, toSignedMeasure_toJordanDecomposition,
      _root_.add_apply, ← toSignedMeasure_apply_measurable hi,
      ← toSignedMeasure_apply_measurable hi,
      withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi,
      _root_.sub_apply]
/-
**MeasureTheory.SignedMeasure.haveLebesgueDecomposition_mk'** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem haveLebesgueDecomposition_mk' (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff] at htμ
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv, totalVariation_mutuallySingular_iff] at htμ
  refine
    { posPart := by
        use ⟨t.toJordanDecomposition.posPart, fun x => ENNReal.ofReal (f x)⟩
        refine ⟨hf.ennreal_ofReal, htμ.1, ?_⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
      negPart := by
        use ⟨t.toJordanDecomposition.negPart, fun x => ENNReal.ofReal (-f x)⟩
        refine ⟨hf.neg.ennreal_ofReal, htμ.2, ?_⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd] }
/-
**MeasureTheory.SignedMeasure.haveLebesgueDecomposition_mk** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：haveLebesgueDecomposition_mk (μ : Measure α) {f : α -> Real} (hf : Measura
ble f) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
 s.HaveLebesgueDecomposition μ
参数：μ : Measure α；hf : Measurable f；htμ : t ⟂ᵥ μ.toENNRealVectorMeasure；hadd : s 
= t + μ.withDensityᵥ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue.0.Me
asureTheory.SignedMeasure.haveLebesgueDecomposition_mk'`：∀ {α : Type u_1} {m : M
easurableSpace α} {s t : MeasureTheory.SignedMeasure α} (μ : MeasureTheory.Measu
re α)   {f : α → ℝ},   Measurable f →…
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensityᵥ_zero`：withDensityᵥ_zero : μ.withDensityᵥ (0 :
 α -> E) = 0
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.Measure.withDensityᵥ.eq_1`：∀ {α : Type u_1} {E : Type u_2}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m : MeasurableSpace α
}   (μ : MeasureTheory.Measur…
-/
theorem haveLebesgueDecomposition_mk (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  by_cases hfi : Integrable f μ
  · exact haveLebesgueDecomposition_mk' μ hf hfi htμ hadd
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine haveLebesgueDecomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]
/-
**MeasureTheory.SignedMeasure.eq_singularPart'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eq_singularPart' (t : SignedMeasure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    t = s.singularPart μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff, totalVariation_mutuallySingular_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  rw [singularPart, ← t.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure]
  congr
  · have hfpos : Measurable fun x => ENNReal.ofReal (f x) := by fun_prop
    refine eq_singularPart hfpos htμ.1 ?_
    rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
  · have hfneg : Measurable fun x => ENNReal.ofReal (-f x) := by fun_prop
    refine eq_singularPart hfneg htμ.2 ?_
    rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`t = singularPart s μ`, i.e. `t` is the singular part of the Lebesgue decomposition between
`s` and `μ`. -/
/-
**MeasureTheory.SignedMeasure.eq_singularPart** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SignedMeasure`。
形式化陈述：eq_singularPart (t : SignedMeasure α) (f : α -> Real) (htμ : t ⟂ᵥ μ.toENNR
ealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) : t = s.singularPart μ
参数：t : SignedMeasure α；f : α -> Real；htμ : t ⟂ᵥ μ.toENNRealVectorMeasure；hadd : 
s = t + μ.withDensityᵥ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue.0.Me
asureTheory.SignedMeasure.eq_singularPart'`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {s : MeasureTheory.SignedMeasure α}   (t : Me
asureTheory.SignedMeasur…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.measurable_mk`：measurable_mk [PseudoM
etrizableSpace β] [MeasurableSpace β] [BorelSpace β] (hf : AEStronglyMeasurable[
m] f μ) : Measurable[m] (hf.mk f)
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.WithDensityᵥEq.congr_ae`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedSpace …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensityᵥ_zero`：withDensityᵥ_zero : μ.withDensityᵥ (0 :
 α -> E) = 0
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.Measure.withDensityᵥ.eq_1`：∀ {α : Type u_1} {E : Type u_2}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m : MeasurableSpace α
}   (μ : MeasureTheory.Measur…

--- 原说明 ---
Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `
t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`t = singularPart s μ`, i.e. `t` is the singular part of the Lebesgue decomposit
ion between
`s` and `μ`.
-/
theorem eq_singularPart (t : SignedMeasure α) (f : α → ℝ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure)
    (hadd : s = t + μ.withDensityᵥ f) : t = s.singularPart μ := by
  by_cases hfi : Integrable f μ
  · refine eq_singularPart' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ ?_
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine eq_singularPart' t measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]
/-
**MeasureTheory.SignedMeasure.singularPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SignedMeasure`。
形式化陈述：singularPart_zero (μ : Measure α) : (0 : SignedMeasure α).singularPart μ =
 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SignedMeasure.eq_singularPart`：eq_singularPart (t : Signed
Measure α) (f : α -> Real) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t +
 μ.withDensityᵥ f) : t = s.singul…
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.zero_left`：zero_left : (0 :
 VectorMeasure α M) ⟂ᵥ w
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.withDensityᵥ_zero`：withDensityᵥ_zero : μ.withDensityᵥ (0 :
 α -> E) = 0
-/
theorem singularPart_zero (μ : Measure α) : (0 : SignedMeasure α).singularPart μ = 0 := by
  refine (eq_singularPart 0 0 VectorMeasure.MutuallySingular.zero_left ?_).symm
  rw [zero_add, withDensityᵥ_zero]
/-
**MeasureTheory.SignedMeasure.singularPart_neg** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SignedMeasure`。
形式化陈述：singularPart_neg (s : SignedMeasure α) (μ : Measure α) : (-s).singularPart
 μ = -s.singularPart μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_neg`：toJordanDecomposi
tion_neg (s : SignedMeasure α) : (-s).toJordanDecomposition = -s.toJordanDecompo
sition
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.toSignedMeasure.congr_simp`：∀ {α : Type u_1} {m : 
MeasurableSpace α} (μ μ_1 : MeasureTheory.Measure α) (e_μ : μ = μ_1)   [hμ : Mea
sureTheory.IsFiniteMeasure μ], μ.toSig…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singularPart_neg (s : SignedMeasure α) (μ : Measure α) :
    (-s).singularPart μ = -s.singularPart μ := by
  simp [singularPart, toJordanDecomposition_neg]
/-
**MeasureTheory.SignedMeasure.singularPart_smul_nnreal** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SignedMeasure`。
形式化陈述：singularPart_smul_nnreal (s : SignedMeasure α) (μ : Measure α) (r : Real>=
0) : (r • s).singularPart μ = r • s.singularPart μ
参数：s : SignedMeasure α；μ : Measure α；r : Real>=0。
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
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.singularPart.eq_1`：∀ {α : Type u_1} {m : Mea
surableSpace α} (s : MeasureTheory.SignedMeasure α) (μ : MeasureTheory.Measure α
),   s.singularPart μ =     (s.toJo…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.toSignedMeasure_smul`：toSignedMeasure_smul (μ : Me
asure α) [IsFiniteMeasure μ] (r : Real>=0) : (r • μ).toSignedMeasure = r • μ.toS
ignedMeasure
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_smul`：toJordanDecompos
ition_smul (s : SignedMeasure α) (r : Real>=0) : (r • s).toJordanDecomposition =
 r • s.toJordanDecomposition
· 使用定理 `MeasureTheory.JordanDecomposition.smul_posPart`：smul_posPart (r : Real>=
0) : (r • j).posPart = r • j.posPart
· 使用定理 `MeasureTheory.Measure.singularPart_smul`：singularPart_smul (μ ν : Measur
e α) (r : Real>=0) : (r • μ).singularPart ν = r • μ.singularPart ν
· 使用定理 `MeasureTheory.JordanDecomposition.smul_negPart`：smul_negPart (r : Real>=
0) : (r • j).negPart = r • j.negPart
-/
theorem singularPart_smul_nnreal (s : SignedMeasure α) (μ : Measure α) (r : ℝ≥0) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  rw [singularPart, singularPart, smul_sub, ← toSignedMeasure_smul, ← toSignedMeasure_smul]
  conv_lhs =>
    congr
    · congr
      · rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart, singularPart_smul]
    · congr
      rw [toJordanDecomposition_smul, JordanDecomposition.smul_negPart, singularPart_smul]

nonrec theorem singularPart_smul (s : SignedMeasure α) (μ : Measure α) (r : ℝ) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  cases le_or_gt 0 r with
  | inl hr =>
    lift r to ℝ≥0 using hr
    exact singularPart_smul_nnreal s μ r
  | inr hr =>
    rw [singularPart, singularPart]
    conv_lhs =>
      congr
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_posPart_neg _ _ hr, singularPart_smul]
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_negPart_neg _ _ hr, singularPart_smul]
    rw [toSignedMeasure_smul, toSignedMeasure_smul, ← neg_sub, ← smul_sub, NNReal.smul_def,
      ← neg_smul, Real.coe_toNNReal _ (le_of_lt (neg_pos.mpr hr)), neg_neg]
/-
**MeasureTheory.SignedMeasure.singularPart_add** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SignedMeasure`。
形式化陈述：singularPart_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDe
composition μ] [t.HaveLebesgueDecomposition μ] : (s + t).singularPart μ = s.sing
ularPart μ + t.singularPart μ
参数：s t : SignedMeasure α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.SignedMeasure.eq_singularPart`：eq_singularPart (t : Signed
Measure α) (f : α -> Real) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t +
 μ.withDensityᵥ f) : t = s.singul…
· 使用定理 `MeasureTheory.VectorMeasure.MutuallySingular.add_left`：add_left [T2Space
 N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.SignedMeasure.mutuallySingular_singularPart`：∀ {α : Type u
_1} {m : MeasurableSpace α} (s : MeasureTheory.SignedMeasure α) (μ : MeasureTheo
ry.Measure α),   MeasureTheory.VectorMeasure.Mu…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensityᵥ_add`：withDensityᵥ_add (hf : Integrable f μ) (
hg : Integrable g μ) : μ.withDensityᵥ (f + g) = μ.withDensityᵥ f + μ.withDensity
ᵥ g
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`：sin
gularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : s.singula
rPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s
-/
theorem singularPart_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s + t).singularPart μ = s.singularPart μ + t.singularPart μ := by
  refine
    (eq_singularPart _ (s.rnDeriv μ + t.rnDeriv μ)
        ((mutuallySingular_singularPart s μ).add_left (mutuallySingular_singularPart t μ))
        ?_).symm
  rw [withDensityᵥ_add (integrable_rnDeriv s μ) (integrable_rnDeriv t μ), add_assoc,
    add_comm (t.singularPart μ), add_assoc, add_comm _ (t.singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, ← add_assoc,
    singularPart_add_withDensity_rnDeriv_eq]
/-
**MeasureTheory.SignedMeasure.singularPart_sub** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SignedMeasure`。
形式化陈述：singularPart_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDe
composition μ] [t.HaveLebesgueDecomposition μ] : (s - t).singularPart μ = s.sing
ularPart μ - t.singularPart μ
参数：s t : SignedMeasure α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add`：singularPart_add (s t : Si
gnedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] [t.HaveLebesgueDe
composition μ] : (s + t).singularP…
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_neg`：singularPart_neg (s : Sign
edMeasure α) (μ : Measure α) : (-s).singularPart μ = -s.singularPart μ
-/
theorem singularPart_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s - t).singularPart μ = s.singularPart μ - t.singularPart μ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, singularPart_add, singularPart_neg]

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`f = rnDeriv s μ`, i.e. `f` is the Radon-Nikodym derivative of `s` and `μ`. -/
/-
**MeasureTheory.SignedMeasure.eq_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SignedMeasure`。
形式化陈述：eq_rnDeriv (t : SignedMeasure α) (f : α -> Real) (hfi : Integrable f μ) (h
tμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) : f =ᵐ[μ] 
s.rnDeriv μ
参数：t : SignedMeasure α；f : α -> Real；hfi : Integrable f μ；htμ : t ⟂ᵥ μ.toENNReal
VectorMeasure；hadd : s = t + μ.withDensityᵥ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.WithDensityᵥEq.congr_ae`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedSpace …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.SignedMeasure.haveLebesgueDecomposition_mk`：haveLebesgueDe
composition_mk (μ : Measure α) {f : α -> Real} (hf : Measurable f) (htμ : t ⟂ᵥ μ
.toENNRealVectorMeasure) (hadd : s = t + μ.wit…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.measurable_mk`：measurable_mk [PseudoM
etrizableSpace β] [MeasurableSpace β] [BorelSpace β] (hf : AEStronglyMeasurable[
m] f μ) : Measurable[m] (hf.mk f)
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SignedMeasure.eq_singularPart`：eq_singularPart (t : Signed
Measure α) (f : α -> Real) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t +
 μ.withDensityᵥ f) : t = s.singul…
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`：sin
gularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : s.singula
rPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s

--- 原说明 ---
Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `
t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`f = rnDeriv s μ`, i.e. `f` is the Radon-Nikodym derivative of `s` and `μ`.
-/
theorem eq_rnDeriv (t : SignedMeasure α) (f : α → ℝ) (hfi : Integrable f μ)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    f =ᵐ[μ] s.rnDeriv μ := by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.withDensityᵥ f' := by
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  have := haveLebesgueDecomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine (Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) hfi ?_).symm
  rw [← add_right_inj t, ← hadd, eq_singularPart _ f htμ hadd,
    singularPart_add_withDensity_rnDeriv_eq]
/-
**MeasureTheory.SignedMeasure.rnDeriv_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SignedMeasure`。
形式化陈述：rnDeriv_neg (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposi
tion μ] : (-s).rnDeriv μ =ᵐ[μ] -s.rnDeriv μ
参数：s : SignedMeasure α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedSpace …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensityᵥ_neg`：withDensityᵥ_neg : μ.withDensityᵥ (-f) =
 -μ.withDensityᵥ f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`：sin
gularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : s.singula
rPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_neg`：singularPart_neg (s : Sign
edMeasure α) (μ : Measure α) : (-s).singularPart μ = -s.singularPart μ
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
-/
theorem rnDeriv_neg (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] :
    (-s).rnDeriv μ =ᵐ[μ] -s.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) (integrable_rnDeriv _ _).neg ?_
  rw [withDensityᵥ_neg, ← add_right_inj ((-s).singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, singularPart_neg, ← neg_add,
    singularPart_add_withDensity_rnDeriv_eq]
/-
**MeasureTheory.SignedMeasure.rnDeriv_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SignedMeasure`。
形式化陈述：rnDeriv_smul (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecompos
ition μ] (r : Real) : (r • s).rnDeriv μ =ᵐ[μ] r • s.rnDeriv μ
参数：s : SignedMeasure α；μ : Measure α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedSpace …
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
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensityᵥ_smul`：withDensityᵥ_smul {𝕜 : Type*} [Nontrivi
allyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass Real 𝕜 E] (f : α -> E) (r : 
𝕜) : μ.withDensityᵥ (…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`：sin
gularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : s.singula
rPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_smul`：∀ {α : Type u_1} {m : Mea
surableSpace α} (s : MeasureTheory.SignedMeasure α) (μ : MeasureTheory.Measure α
) (r : ℝ),   (r • s).singularPart μ…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
theorem rnDeriv_smul (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : ℝ) :
    (r • s).rnDeriv μ =ᵐ[μ] r • s.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).smul r) ?_
  rw [withDensityᵥ_smul (rnDeriv s μ) r, ← add_right_inj ((r • s).singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, singularPart_smul, ← smul_add,
    singularPart_add_withDensity_rnDeriv_eq]
/-
**MeasureTheory.SignedMeasure.rnDeriv_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SignedMeasure`。
形式化陈述：rnDeriv_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecompo
sition μ] [t.HaveLebesgueDecomposition μ] [(s + t).HaveLebesgueDecomposition μ] 
: (s + t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ + t.rnDeriv μ
参数：s t : SignedMeasure α；μ : Measure α；s + t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedSpace …
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`：sin
gularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : s.singula
rPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.withDensityᵥ_add`：withDensityᵥ_add (hf : Integrable f μ) (
hg : Integrable g μ) : μ.withDensityᵥ (f + g) = μ.withDensityᵥ f + μ.withDensity
ᵥ g
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add`：singularPart_add (s t : Si
gnedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] [t.HaveLebesgueDe
composition μ] : (s + t).singularP…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem rnDeriv_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [(s + t).HaveLebesgueDecomposition μ] :
    (s + t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ + t.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).add (integrable_rnDeriv _ _)) ?_
  rw [← add_right_inj ((s + t).singularPart μ), singularPart_add_withDensity_rnDeriv_eq,
    withDensityᵥ_add (integrable_rnDeriv _ _) (integrable_rnDeriv _ _), singularPart_add,
    add_assoc, add_comm (t.singularPart μ), add_assoc, add_comm _ (t.singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, ← add_assoc,
    singularPart_add_withDensity_rnDeriv_eq]
/-
**MeasureTheory.SignedMeasure.rnDeriv_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SignedMeasure`。
形式化陈述：rnDeriv_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecompo
sition μ] [t.HaveLebesgueDecomposition μ] [hst : (s - t).HaveLebesgueDecompositi
on μ] : (s - t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ - t.rnDeriv μ
参数：s t : SignedMeasure α；μ : Measure α；s - t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.SignedMeasure.rnDeriv_add`：rnDeriv_add (s t : SignedMeasur
e α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] [t.HaveLebesgueDecompositio
n μ] [(s + t).HaveLebesgueDec…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `MeasureTheory.SignedMeasure.rnDeriv_neg`：rnDeriv_neg (s : SignedMeasure 
α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] : (-s).rnDeriv μ =ᵐ[μ] -s.rnD
eriv μ
-/
theorem rnDeriv_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [hst : (s - t).HaveLebesgueDecomposition μ] :
    (s - t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ - t.rnDeriv μ := by
  rw [sub_eq_add_neg] at hst
  rw [sub_eq_add_neg, sub_eq_add_neg]
  grw [rnDeriv_add, rnDeriv_neg]

end SignedMeasure

namespace ComplexMeasure

/-- A complex measure is said to `HaveLebesgueDecomposition` with respect to a positive measure
if both its real and imaginary part `HaveLebesgueDecomposition` with respect to that measure. -/
/-
**MeasureTheory.ComplexMeasure.HaveLebesgueDecomposition** 是 Mathlib 中的一个归纳类型，位于
命名空间 `MeasureTheory.ComplexMeasure`。
形式化陈述：{α : Type u_1} → {m : MeasurableSpace α} → MeasureTheory.ComplexMeasure α 
→ MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complex measure is said to `HaveLebesgueDecomposition` with respect to a posit
ive measure
if both its real and imaginary part `HaveLebesgueDecomposition` with respect to 
that measure.
-/
class HaveLebesgueDecomposition (c : ComplexMeasure α) (μ : Measure α) : Prop where
  rePart : c.re.HaveLebesgueDecomposition μ
  imPart : c.im.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.rePart

attribute [instance] HaveLebesgueDecomposition.imPart

/-- The singular part between a complex measure `c` and a positive measure `μ` is the complex
measure satisfying `c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c`. This property is given
by `MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq`. -/
/-
**MeasureTheory.ComplexMeasure.singularPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTh
eory.ComplexMeasure`。
形式化陈述：singularPart (c : ComplexMeasure α) (μ : Measure α) : ComplexMeasure α
参数：c : ComplexMeasure α；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singular part between a complex measure `c` and a positive measure `μ` is th
e complex
measure satisfying `c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c`. This p
roperty is given
by `MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq`.
-/
def singularPart (c : ComplexMeasure α) (μ : Measure α) : ComplexMeasure α :=
  (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)

/-- The Radon-Nikodym derivative between a complex measure and a positive measure. -/
/-
**MeasureTheory.ComplexMeasure.rnDeriv** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
ComplexMeasure`。
形式化陈述：rnDeriv (c : ComplexMeasure α) (μ : Measure α) : α -> Complex
参数：c : ComplexMeasure α；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Radon-Nikodym derivative between a complex measure and a positive measure.
-/
def rnDeriv (c : ComplexMeasure α) (μ : Measure α) : α → ℂ := fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩

variable {c : ComplexMeasure α}
/-
**MeasureTheory.ComplexMeasure.integrable_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.ComplexMeasure`。
形式化陈述：integrable_rnDeriv (c : ComplexMeasure α) (μ : Measure α) : Integrable (c.
rnDeriv μ) μ
参数：c : ComplexMeasure α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.memLp_re_im_iff`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {K : Type u_8} [inst : RCLike K]   {
f : α → K},   Measu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
-/
theorem integrable_rnDeriv (c : ComplexMeasure α) (μ : Measure α) : Integrable (c.rnDeriv μ) μ := by
  rw [← memLp_one_iff_integrable, ← memLp_re_im_iff]
  exact
    ⟨memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _),
      memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _)⟩
/-
**MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ComplexMeasure`。
形式化陈述：singularPart_add_withDensity_rnDeriv_eq [c.HaveLebesgueDecomposition μ] : 
c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ComplexMeasure.toComplexMeasure_to_signedMeasure`：toComple
xMeasure_to_signedMeasure (c : ComplexMeasure α) : SignedMeasure.toComplexMeasur
e (ComplexMeasure.re c) (ComplexMeasure.im c) = c
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `MeasureTheory.SignedMeasure.toComplexMeasure_apply`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {s t : MeasureTheory.SignedMeasure α} {i : Set α},   (s.toC
omplexMeasure t) i = { re := s i, im := …
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `MeasureTheory.withDensityᵥ_apply`：withDensityᵥ_apply (hf : Integrable f 
μ) {s : Set α} (hs : MeasurableSet s) : μ.withDensityᵥ f s = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.ComplexMeasure.integrable_rnDeriv`：integrable_rnDeriv (c :
 ComplexMeasure α) (μ : Measure α) : Integrable (c.rnDeriv μ) μ
· 使用定理 `RCLike.re_eq_complex_re`：⇑RCLike.re = Complex.re
· 使用定理 `integral_re`：integral_re {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLik
e.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ)
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq`：sin
gularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] : s.singula
rPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s
· 使用定理 `MeasureTheory.ComplexMeasure.HaveLebesgueDecomposition.rePart`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {c : MeasureTheory.ComplexMeasure α} {μ : Measur
eTheory.Measure α}   [self : c.HaveLebesgueDecompos…
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `RCLike.im_eq_complex_im`：⇑RCLike.im = Complex.im
· 使用定理 `integral_im`：integral_im {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLik
e.im (f x) ∂μ = RCLike.im (∫ x, f x ∂μ)
（共 31 条，此处仅展示前 30 条）
-/
theorem singularPart_add_withDensity_rnDeriv_eq [c.HaveLebesgueDecomposition μ] :
    c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c := by
  conv_rhs => rw [← c.toComplexMeasure_to_signedMeasure]
  ext i hi : 1
  rw [add_apply, SignedMeasure.toComplexMeasure_apply]
  apply Complex.ext
  · rw [Complex.add_re, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.re_eq_complex_re,
      ← integral_re (c.integrable_rnDeriv μ).integrableOn, RCLike.re_eq_complex_re,
      ← withDensityᵥ_apply _ hi]
    · change (c.re.singularPart μ + μ.withDensityᵥ (c.re.rnDeriv μ)) i = _
      rw [c.re.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _
  · rw [Complex.add_im, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.im_eq_complex_im,
      ← integral_im (c.integrable_rnDeriv μ).integrableOn, RCLike.im_eq_complex_im,
      ← withDensityᵥ_apply _ hi]
    · change (c.im.singularPart μ + μ.withDensityᵥ (c.im.rnDeriv μ)) i = _
      rw [c.im.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _

end ComplexMeasure

end MeasureTheory

