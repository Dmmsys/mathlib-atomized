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
/--
Definition of `JordanDecomposition` / `JordanDecomposition` 的定义

English:
structure JordanDecomposition
  parameters: (α : Type*) [MeasurableSpace α]
  axioms and operations (5):
    - posPart : Measure α
    - negPart : Measure α
    - [posPart_finite : IsFiniteMeasure posPart]
    - [negPart_finite : IsFiniteMeasure negPart]
    - mutuallySingular : posPart ⟂ₘ negPart

中文:
结构 JordanDecomposition
  参数: (α : 类型) [MeasurableSpace α]
  公理与运算 (5 个):
    - posPart : Measure α
    - negPart : Measure α
    - [posPart_finite : IsFiniteMeasure posPart]
    - [negPart_finite : IsFiniteMeasure negPart]
    - mutuallySingular : posPart ⟂ₘ negPart
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

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (JordanDecomposition α) where zero
  body: ⟨0, 0, MutuallySingular.zero_right⟩

中文:
实例 instZero
  签名: : Zero (JordanDecomposition α) where zero
  定义体: ⟨0, 0, MutuallySingular.zero_right⟩

Depends on / 依赖: MutuallySingular, MutuallySingular.zero_right, zero_right
-/
instance instZero : Zero (JordanDecomposition α) where zero := ⟨0, 0, MutuallySingular.zero_right⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (JordanDecomposition α) where default
  body: 0

中文:
实例 instInhabited
  签名: : Inhabited (JordanDecomposition α) where default
  定义体: 0
-/
instance instInhabited : Inhabited (JordanDecomposition α) where default := 0

/--
Instance `instInvolutiveNeg` / 实例 `instInvolutiveNeg`

English:
instance instInvolutiveNeg
  signature: : InvolutiveNeg (JordanDecomposition α) where
  body: ⟨j.negPart, j.posPart, j.mutuallySingular.symm⟩
  neg_neg _ := JordanDecomposition.ext rfl rfl

中文:
实例 instInvolutiveNeg
  签名: : InvolutiveNeg (JordanDecomposition α) where
  定义体: ⟨j.negPart, j.posPart, j.mutuallySingular.symm⟩
  neg_neg _ := JordanDecomposition.ext rfl rfl

Depends on / 依赖: j.mutuallySingular.symm, j.negPart, j.posPart, mutuallySingular, negPart, posPart
-/
instance instInvolutiveNeg : InvolutiveNeg (JordanDecomposition α) where
  neg j := ⟨j.negPart, j.posPart, j.mutuallySingular.symm⟩
  neg_neg _ := JordanDecomposition.ext rfl rfl

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul Real>=0 (JordanDecomposition α) where
  body: ⟨r • j.posPart, r • j.negPart,
      MutuallySingular.smul _ (MutuallySingular.smul _ j.mutuallySingular.symm).symm⟩

中文:
实例 instSMul
  签名: : SMul 实数>=0 (JordanDecomposition α) where
  定义体: ⟨r • j.posPart, r • j.negPart,
      MutuallySingular.smul _ (MutuallySingular.smul _ j.mutuallySingular.symm).symm⟩

Depends on / 依赖: MutuallySingular, MutuallySingular.smul, j.mutuallySingular.symm, j.negPart, j.posPart, mutuallySingular, negPart, posPart
-/
instance instSMul : SMul Real>=0 (JordanDecomposition α) where
  smul r j :=
    ⟨r • j.posPart, r • j.negPart,
      MutuallySingular.smul _ (MutuallySingular.smul _ j.mutuallySingular.symm).symm⟩

/--
Instance `instSMulReal` / 实例 `instSMulReal`

English:
instance instSMulReal
  signature: : SMul Real (JordanDecomposition α) where
  body: if 0 <= r then r.toNNReal • j else -((-r).toNNReal • j)

@[simp]

中文:
实例 instSMulReal
  签名: : SMul 实数 (JordanDecomposition α) where
  定义体: if 0 <= r then r.toNNReal • j else -((-r).toNNReal • j)

@[simp]

Depends on / 依赖: r.toNNReal, toNNReal
-/
instance instSMulReal : SMul Real (JordanDecomposition α) where
  smul r j := if 0 <= r then r.toNNReal • j else -((-r).toNNReal • j)

@[simp]
/--
theorem `zero_posPart` / 定理 `zero_posPart`

English:
theorem zero_posPart
  statement: (0 : JordanDecomposition α).posPart = 0
  proof: rfl

@[simp]

中文:
定理 zero_posPart
  结论: (0 : JordanDecomposition α).posPart = 0
  证明: rfl

@[simp]
-/
theorem zero_posPart : (0 : JordanDecomposition α).posPart = 0 :=
  rfl

@[simp]
/--
theorem `zero_negPart` / 定理 `zero_negPart`

English:
theorem zero_negPart
  statement: (0 : JordanDecomposition α).negPart = 0
  proof: rfl

@[simp]

中文:
定理 zero_negPart
  结论: (0 : JordanDecomposition α).negPart = 0
  证明: rfl

@[simp]

Depends on / 依赖: EventuallyEq, EventuallyEq.trans
-/
theorem zero_negPart : (0 : JordanDecomposition α).negPart = 0 :=
  rfl

@[simp]
/--
theorem `neg_posPart` / 定理 `neg_posPart`

English:
theorem neg_posPart
  statement: (-j).posPart = j.negPart
  proof: rfl

@[simp]

中文:
定理 neg_posPart
  结论: (-j).posPart = j.negPart
  证明: rfl

@[simp]
-/
theorem neg_posPart : (-j).posPart = j.negPart :=
  rfl

@[simp]
/--
theorem `neg_negPart` / 定理 `neg_negPart`

English:
theorem neg_negPart
  statement: (-j).negPart = j.posPart
  proof: rfl

@[simp]

中文:
定理 neg_negPart
  结论: (-j).negPart = j.posPart
  证明: rfl

@[simp]
-/
theorem neg_negPart : (-j).negPart = j.posPart :=
  rfl

@[simp]
/--
theorem `smul_posPart` / 定理 `smul_posPart`

English:
theorem smul_posPart
  given: (r : Real>=0)
  statement: (r • j).posPart = r • j.posPart
  proof: rfl

@[simp]

中文:
定理 smul_posPart
  条件: (r : 实数>=0)
  结论: (r • j).posPart = r • j.posPart
  证明: rfl

@[simp]
-/
theorem smul_posPart (r : Real>=0) : (r • j).posPart = r • j.posPart :=
  rfl

@[simp]
/--
theorem `smul_negPart` / 定理 `smul_negPart`

English:
theorem smul_negPart
  given: (r : Real>=0)
  statement: (r • j).negPart = r • j.negPart
  proof: rfl

中文:
定理 smul_negPart
  条件: (r : 实数>=0)
  结论: (r • j).negPart = r • j.negPart
  证明: rfl
-/
theorem smul_negPart (r : Real>=0) : (r • j).negPart = r • j.negPart :=
  rfl

/--
theorem `real_smul_def` / 定理 `real_smul_def`

English:
theorem real_smul_def
  given: (r : Real) (j : JordanDecomposition α)
  proof: rfl

@[simp]

中文:
定理 real_smul_def
  条件: (r : 实数) (j : JordanDecomposition α)
  证明: rfl

@[simp]
-/
theorem real_smul_def (r : Real) (j : JordanDecomposition α) :
    r • j = if 0 <= r then r.toNNReal • j else -((-r).toNNReal • j) :=
  rfl

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : Real>=0)
  statement: (r : Real) • j = r • j
  proof: by
  rw [real_smul_def]; rw [if_pos (NNReal.coe_nonneg r)]; rw [Real.toNNReal_coe]

中文:
定理 coe_smul
  条件: (r : 实数>=0)
  结论: (r : 实数) • j = r • j
  证明: by
  rw [real_smul_def]; rw [if_pos (NNReal.coe_nonneg r)]; rw [Real.toNNReal_coe]

Depends on / 依赖: NNReal, NNReal.coe_nonneg, Real.toNNReal_coe, coe_nonneg, if_pos, real_smul_def, toNNReal_coe
-/
theorem coe_smul (r : Real>=0) : (r : Real) • j = r • j := by
  rw [real_smul_def]; rw [if_pos (NNReal.coe_nonneg r)]; rw [Real.toNNReal_coe]

/--
theorem `real_smul_nonneg` / 定理 `real_smul_nonneg`

English:
theorem real_smul_nonneg
  given: (r : Real) (hr : 0 <= r)
  statement: r • j = r.toNNReal • j
  proof: dif_pos hr

中文:
定理 real_smul_nonneg
  条件: (r : 实数) (hr : 0 <= r)
  结论: r • j = r.toNN实数 • j
  证明: dif_pos hr

Depends on / 依赖: dif_pos
-/
theorem real_smul_nonneg (r : Real) (hr : 0 <= r) : r • j = r.toNNReal • j :=
  dif_pos hr

/--
theorem `real_smul_neg` / 定理 `real_smul_neg`

English:
theorem real_smul_neg
  given: (r : Real) (hr : r < 0)
  statement: r • j = -((-r).toNNReal • j)
  proof: dif_neg (not_le.2 hr)

中文:
定理 real_smul_neg
  条件: (r : 实数) (hr : r < 0)
  结论: r • j = -((-r).toNN实数 • j)
  证明: dif_neg (not_le.2 hr)

Depends on / 依赖: dif_neg, not_le
-/
theorem real_smul_neg (r : Real) (hr : r < 0) : r • j = -((-r).toNNReal • j) :=
  dif_neg (not_le.2 hr)

/--
theorem `real_smul_posPart_nonneg` / 定理 `real_smul_posPart_nonneg`

English:
theorem real_smul_posPart_nonneg
  given: (r : Real) (hr : 0 <= r)
  proof: by
  rw [real_smul_def]; rw [← smul_posPart]; rw [if_pos hr]

中文:
定理 real_smul_posPart_nonneg
  条件: (r : 实数) (hr : 0 <= r)
  证明: by
  rw [real_smul_def]; rw [← smul_posPart]; rw [if_pos hr]

Depends on / 依赖: if_pos, real_smul_def, smul_posPart
-/
theorem real_smul_posPart_nonneg (r : Real) (hr : 0 <= r) :
    (r • j).posPart = r.toNNReal • j.posPart := by
  rw [real_smul_def]; rw [← smul_posPart]; rw [if_pos hr]

/--
theorem `real_smul_negPart_nonneg` / 定理 `real_smul_negPart_nonneg`

English:
theorem real_smul_negPart_nonneg
  given: (r : Real) (hr : 0 <= r)
  proof: by
  rw [real_smul_def]; rw [← smul_negPart]; rw [if_pos hr]

中文:
定理 real_smul_negPart_nonneg
  条件: (r : 实数) (hr : 0 <= r)
  证明: by
  rw [real_smul_def]; rw [← smul_negPart]; rw [if_pos hr]

Depends on / 依赖: if_pos, real_smul_def, smul_negPart
-/
theorem real_smul_negPart_nonneg (r : Real) (hr : 0 <= r) :
    (r • j).negPart = r.toNNReal • j.negPart := by
  rw [real_smul_def]; rw [← smul_negPart]; rw [if_pos hr]

/--
theorem `real_smul_posPart_neg` / 定理 `real_smul_posPart_neg`

English:
theorem real_smul_posPart_neg
  given: (r : Real) (hr : r < 0)
  proof: by
  rw [real_smul_def]; rw [← smul_negPart]; rw [if_neg (not_le.2 hr)]; rw [neg_posPart]

中文:
定理 real_smul_posPart_neg
  条件: (r : 实数) (hr : r < 0)
  证明: by
  rw [real_smul_def]; rw [← smul_negPart]; rw [if_neg (not_le.2 hr)]; rw [neg_posPart]

Depends on / 依赖: if_neg, neg_posPart, not_le, real_smul_def, smul_negPart
-/
theorem real_smul_posPart_neg (r : Real) (hr : r < 0) :
    (r • j).posPart = (-r).toNNReal • j.negPart := by
  rw [real_smul_def]; rw [← smul_negPart]; rw [if_neg (not_le.2 hr)]; rw [neg_posPart]

/--
theorem `real_smul_negPart_neg` / 定理 `real_smul_negPart_neg`

English:
theorem real_smul_negPart_neg
  given: (r : Real) (hr : r < 0)
  proof: by
  rw [real_smul_def]; rw [← smul_posPart]; rw [if_neg (not_le.2 hr)]; rw [neg_negPart]

中文:
定理 real_smul_negPart_neg
  条件: (r : 实数) (hr : r < 0)
  证明: by
  rw [real_smul_def]; rw [← smul_posPart]; rw [if_neg (not_le.2 hr)]; rw [neg_negPart]

Depends on / 依赖: if_neg, neg_negPart, not_le, real_smul_def, smul_posPart
-/
theorem real_smul_negPart_neg (r : Real) (hr : r < 0) :
    (r • j).negPart = (-r).toNNReal • j.posPart := by
  rw [real_smul_def]; rw [← smul_posPart]; rw [if_neg (not_le.2 hr)]; rw [neg_negPart]

/--
Definition of `toSignedMeasure` / `toSignedMeasure` 的定义

English:
definition toSignedMeasure
  signature: : SignedMeasure α
  body: j.posPart.toSignedMeasure - j.negPart.toSignedMeasure

中文:
定义 toSignedMeasure
  签名: : SignedMeasure α
  定义体: j.posPart.toSignedMeasure - j.negPart.toSignedMeasure

Depends on / 依赖: j.negPart.toSignedMeasure, j.posPart.toSignedMeasure, negPart, posPart, toSignedMeasure
-/
def toSignedMeasure : SignedMeasure α :=
  j.posPart.toSignedMeasure - j.negPart.toSignedMeasure

/--
theorem `toSignedMeasure_zero` / 定理 `toSignedMeasure_zero`

English:
theorem toSignedMeasure_zero
  statement: (0 : JordanDecomposition α).toSignedMeasure = 0
  proof: by
  ext1 i hi
  rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [zero_posPart]; rw [zero_negPart]; rw [sub_self]; rw [FunLike.coe_zero]; rw [Pi.zero_apply]

中文:
定理 toSignedMeasure_zero
  结论: (0 : JordanDecomposition α).toSignedMeasure = 0
  证明: by
  ext1 i hi
  rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [zero_posPart]; rw [zero_negPart]; rw [sub_self]; rw [FunLike.coe_zero]; rw [Pi.zero_apply]

Depends on / 依赖: FunLike, FunLike.coe_zero, Pi.zero_apply, coe_zero, sub_self, toSignedMeasure, toSignedMeasure_sub_apply, zero_apply, zero_negPart, zero_posPart
-/
theorem toSignedMeasure_zero : (0 : JordanDecomposition α).toSignedMeasure = 0 := by
  ext1 i hi
  rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [zero_posPart]; rw [zero_negPart]; rw [sub_self]; rw [FunLike.coe_zero]; rw [Pi.zero_apply]

/--
theorem `toSignedMeasure_neg` / 定理 `toSignedMeasure_neg`

English:
theorem toSignedMeasure_neg
  statement: (-j).toSignedMeasure = -j.toSignedMeasure
  proof: by
  ext1 i hi
  rw [neg_apply]; rw [toSignedMeasure]; rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [toSignedMeasure_sub_apply hi]; rw [neg_sub]; rw [neg_posPart]; rw [neg_negPart]

中文:
定理 toSignedMeasure_neg
  结论: (-j).toSignedMeasure = -j.toSignedMeasure
  证明: by
  ext1 i hi
  rw [neg_apply]; rw [toSignedMeasure]; rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [toSignedMeasure_sub_apply hi]; rw [neg_sub]; rw [neg_posPart]; rw [neg_negPart]

Depends on / 依赖: neg_apply, neg_negPart, neg_posPart, neg_sub, toSignedMeasure, toSignedMeasure_sub_apply
-/
theorem toSignedMeasure_neg : (-j).toSignedMeasure = -j.toSignedMeasure := by
  ext1 i hi
  rw [neg_apply]; rw [toSignedMeasure]; rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [toSignedMeasure_sub_apply hi]; rw [neg_sub]; rw [neg_posPart]; rw [neg_negPart]

/--
theorem `toSignedMeasure_smul` / 定理 `toSignedMeasure_smul`

English:
theorem toSignedMeasure_smul
  given: (r : Real>=0)
  statement: (r • j).toSignedMeasure = r • j.toSignedMeasure
  proof: by
  ext1 i hi
  rw [_root_.smul_apply]; rw [toSignedMeasure]; rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [toSignedMeasure_sub_apply hi]; rw [smul_sub]; rw [smul_posPart]; rw [smul_negPart]; rw [measureReal_nnreal_smul_apply]; rw [measureReal_nnreal_smul_apply]
  rfl

中文:
定理 toSignedMeasure_smul
  条件: (r : 实数>=0)
  结论: (r • j).toSignedMeasure = r • j.toSignedMeasure
  证明: by
  ext1 i hi
  rw [_root_.smul_apply]; rw [toSignedMeasure]; rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [toSignedMeasure_sub_apply hi]; rw [smul_sub]; rw [smul_posPart]; rw [smul_negPart]; rw [measureReal_nnreal_smul_apply]; rw [measureReal_nnreal_smul_apply]
  rfl

Depends on / 依赖: _root_, _root_.smul_apply, measureReal_nnreal_smul_apply, smul_apply, smul_negPart, smul_posPart, smul_sub, toSignedMeasure, toSignedMeasure_sub_apply
-/
theorem toSignedMeasure_smul (r : Real>=0) : (r • j).toSignedMeasure = r • j.toSignedMeasure := by
  ext1 i hi
  rw [_root_.smul_apply]; rw [toSignedMeasure]; rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hi]; rw [toSignedMeasure_sub_apply hi]; rw [smul_sub]; rw [smul_posPart]; rw [smul_negPart]; rw [measureReal_nnreal_smul_apply]; rw [measureReal_nnreal_smul_apply]
  rfl

/--
theorem `exists_compl_positive_negative` / 定理 `exists_compl_positive_negative`

English:
theorem exists_compl_positive_negative
  proof: by
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutuallySingular
  refine ⟨S, hS₁, ?_, ?_, hS₂, hS₃⟩
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hA]; rw [measureReal_def]; rw [show j.posPart A = 0 from nonpos_iff_eq_zero.1 (hS₂ ▸ me

中文:
定理 exists_compl_positive_negative
  证明: by
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutuallySingular
  refine ⟨S, hS₁, ?_, ?_, hS₂, hS₃⟩
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hA]; rw [measureReal_def]; rw [show j.posPart A = 0 from nonpos_iff_eq_zero.1 (hS₂ ▸ me

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, ENNReal.toReal_zero, j.mutuallySingular, j.posPart, measureReal_def, measure_mono, mutuallySingular, neg_le, neg_zero, nonpos_iff_eq_zero, posPart, restrict_le_restrict_of_subset_le, toReal_nonneg, toReal_zero, toSignedM, toSignedMeasure, toSignedMeasure_sub_apply, zero_apply, zero_sub
-/
theorem exists_compl_positive_negative :
    exists S : Set α,
      MeasurableSet S ∧
        j.toSignedMeasure <=[S] 0 ∧
          0 <=[Sᶜ] j.toSignedMeasure ∧ j.posPart S = 0 ∧ j.negPart Sᶜ = 0 := by
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutuallySingular
  refine ⟨S, hS₁, ?_, ?_, hS₂, hS₃⟩
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hA]; rw [measureReal_def]; rw [show j.posPart A = 0 from nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁)]; rw [ENNReal.toReal_zero]; rw [zero_sub]; rw [neg_le]; rw [zero_apply]; rw [neg_zero]
    exact ENNReal.toReal_nonneg
  · refine restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => ?_
    rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply hA]; rw [measureReal_def (μ := j.negPart)]; rw [show j.negPart A = 0 from nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁)]; rw [ENNReal.toReal_zero]; rw [sub_zero]
    exact ENNReal.toReal_nonneg

end JordanDecomposition

namespace SignedMeasure

open JordanDecomposition Measure Set VectorMeasure

variable {s : SignedMeasure α}

/--
Definition of `toJordanDecomposition` / `toJordanDecomposition` 的定义

English:
definition toJordanDecomposition
  signature: (s : SignedMeasure α)
  body: let i := s.exists_compl_positive_negative.choose
  have hi := s.exists_compl_positive_negative.choose_spec
  { posPart := s.toMeasureOfZeroLE i hi.1 hi.2.1
    negPart := s.toMeasureOfLEZero iᶜ hi.1.compl hi.2.2
    posPart_finite := inferInstance
    negPart_finite := inferInstance
    mutuallySing

中文:
定义 toJordanDecomposition
  签名: (s : SignedMeasure α)
  定义体: let i := s.exists_compl_positive_negative.choose
  have hi := s.exists_compl_positive_negative.choose_spec
  { posPart := s.toMeasureOfZeroLE i hi.1 hi.2.1
    negPart := s.toMeasureOfLEZero iᶜ hi.1.compl hi.2.2
    posPart_finite := inferInstance
    negPart_finite := inferInstance
    mutuallySing

Depends on / 依赖: choose_spec, compl.compl, exists_compl_positive_negative, mutuallySingular, negPart, negPart_finite, posPart, posPart_finite, s.exists_compl_positive_negative.choose, s.exists_compl_positive_negative.choose_spec, s.toMeasureOfLEZero, s.toMeasureOfZeroLE, toMeasureOfLEZero, toMeasureOfLEZero_apply, toMeasureOfZeroLE, toMeasureOfZeroLE_apply
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

/--
theorem `toJordanDecomposition_spec` / 定理 `toJordanDecomposition_spec`

English:
theorem toJordanDecomposition_spec
  given: (s : SignedMeasure α)
  proof: by
  set i := s.exists_compl_positive_negative.choose
  obtain ⟨hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative.choose_spec
  exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩

中文:
定理 toJordanDecomposition_spec
  条件: (s : SignedMeasure α)
  证明: by
  set i := s.exists_compl_positive_negative.choose
  obtain ⟨hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative.choose_spec
  exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩

Depends on / 依赖: choose_spec, exists_compl_positive_negative, s.exists_compl_positive_negative.choose, s.exists_compl_positive_negative.choose_spec
-/
theorem toJordanDecomposition_spec (s : SignedMeasure α) :
    exists (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0),
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
/--
theorem `toSignedMeasure_toJordanDecomposition` / 定理 `toSignedMeasure_toJordanDecomposition`

English:
theorem toSignedMeasure_toJordanDecomposition
  given: (s : SignedMeasure α)
  proof: by
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.toJordanDecomposition_spec
  simp only [JordanDecomposition.toSignedMeasure, hμ, hν]
  ext k hk
  rw [toSignedMeasure_sub_apply hk]; rw [toMeasureOfZeroLE_real_apply _ hi₂ hi₁ hk]; rw [toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl hk]
  simp only [sub_neg_e

中文:
定理 toSignedMeasure_toJordanDecomposition
  条件: (s : SignedMeasure α)
  证明: by
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.toJordanDecomposition_spec
  simp only [JordanDecomposition.toSignedMeasure, hμ, hν]
  ext k hk
  rw [toSignedMeasure_sub_apply hk]; rw [toMeasureOfZeroLE_real_apply _ hi₂ hi₁ hk]; rw [toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl hk]
  simp only [sub_neg_e

Depends on / 依赖: JordanDecomposition, JordanDecomposition.toSignedMeasure, MeasurableSet, MeasurableSet.inter, Set.inter_comm, Set.inter_union_compl, disjoint_compl_right, disjoint_compl_right.inf_left, inf_left, inter_comm, inter_union_compl, of_union, s.toJordanDecomposition_spec, sub_neg_eq_add, toJordanDecomposition_spec, toMeasureOfLEZero_real_apply, toMeasureOfZeroLE_real_apply, toSignedMeasure, toSignedMeasure_sub_apply
-/
theorem toSignedMeasure_toJordanDecomposition (s : SignedMeasure α) :
    s.toJordanDecomposition.toSignedMeasure = s := by
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.toJordanDecomposition_spec
  simp only [JordanDecomposition.toSignedMeasure, hμ, hν]
  ext k hk
  rw [toSignedMeasure_sub_apply hk]; rw [toMeasureOfZeroLE_real_apply _ hi₂ hi₁ hk]; rw [toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl hk]
  simp only [sub_neg_eq_add]
  rw [← of_union _ (MeasurableSet.inter hi₁ hk) (MeasurableSet.inter hi₁.compl hk)]; rw [Set.inter_comm i]; rw [Set.inter_comm iᶜ]; rw [Set.inter_union_compl _ _]
  exact (disjoint_compl_right.inf_left _).inf_right _

section

variable {u v w : Set α}

/--
theorem `subset_positive_null_set` / 定理 `subset_positive_null_set`

English:
theorem subset_positive_null_set
  statement: (hu : MeasurableSet u) (hv : MeasurableSet v)
  proof: by
  have : s v + s (w \ v) = 0 := by
    rw [← hw₁]; rw [← of_union Set.disjoint_sdiff_right hv (hw.diff hv)]; rw [Set.union_sdiff_self]; rw [Set.union_eq_self_of_subset_left hwt]
  have h₁ := nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂))
  have h₂ : 0 <= s (

中文:
定理 subset_positive_null_set
  结论: (hu : MeasurableSet u) (hv : MeasurableSet v)
  证明: by
  have : s v + s (w \ v) = 0 := by
    rw [← hw₁]; rw [← of_union Set.disjoint_sdiff_right hv (hw.diff hv)]; rw [Set.union_sdiff_self]; rw [Set.union_eq_self_of_subset_left hwt]
  have h₁ := nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂))
  have h₂ : 0 <= s (

Depends on / 依赖: Set.disjoint_sdiff_right, Set.union_eq_self_of_subset_left, Set.union_sdiff_self, disjoint_sdiff_right, hw.diff, hwt.trans, nonneg_of_zero_le_restrict, of_union, restrict_le_restrict_subset, sdiff_subset, sdiff_subset.trans, union_eq_self_of_subset_left, union_sdiff_self
-/
theorem subset_positive_null_set (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : 0 <=[u] s) (hw₁ : s w = 0) (hw₂ : w subseteq u) (hwt : v subseteq w) :
    s v = 0 := by
  have : s v + s (w \ v) = 0 := by
    rw [← hw₁]; rw [← of_union Set.disjoint_sdiff_right hv (hw.diff hv)]; rw [Set.union_sdiff_self]; rw [Set.union_eq_self_of_subset_left hwt]
  have h₁ := nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂))
  have h₂ : 0 <= s (w \ v) :=
    nonneg_of_zero_le_restrict _
      (restrict_le_restrict_subset _ _ hu hsu (sdiff_subset.trans hw₂))
  linarith

/--
theorem `subset_negative_null_set` / 定理 `subset_negative_null_set`

English:
theorem subset_negative_null_set
  statement: (hu : MeasurableSet u) (hv : MeasurableSet v)
  proof: by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  have := subset_positive_null_set hu hv hw hsu
  simp only [neg_apply, neg_eq_zero] at this
  exact this hw₁ hw₂ hwt

中文:
定理 subset_negative_null_set
  结论: (hu : MeasurableSet u) (hv : MeasurableSet v)
  证明: by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  have := subset_positive_null_set hu hv hw hsu
  simp only [neg_apply, neg_eq_zero] at this
  exact this hw₁ hw₂ hwt

Depends on / 依赖: neg_apply, neg_eq_zero, neg_le_neg_iff, neg_zero, s.neg_le_neg_iff, subset_positive_null_set
-/
theorem subset_negative_null_set (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : s <=[u] 0) (hw₁ : s w = 0) (hw₂ : w subseteq u) (hwt : v subseteq w) :
    s v = 0 := by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  have := subset_positive_null_set hu hv hw hsu
  simp only [neg_apply, neg_eq_zero] at this
  exact this hw₁ hw₂ hwt

open scoped symmDiff

/--
theorem `of_sdiff_eq_zero_of_symmDiff_eq_zero_positive` / 定理 `of_sdiff_eq_zero_of_symmDiff_eq_zero_positive`

English:
theorem of_sdiff_eq_zero_of_symmDiff_eq_zero_positive
  statement: (hu : MeasurableSet u) (hv : MeasurableSet v)
  proof: by
  rw [restrict_le_restrict_iff] at hsu hsv
  on_goal 1 =>
    have a := hsu (hu.diff hv) sdiff_subset
    have b := hsv (hv.diff hu) sdiff_subset
    rw [Set.symmDiff_def]; rw [of_union (v := s) (Set.disjoint_of_subset_left sdiff_subset disjoint_sdiff_self_right)
        (hu.diff hv) (hv.diff hu)

中文:
定理 of_sdiff_eq_zero_of_symmDiff_eq_zero_positive
  结论: (hu : MeasurableSet u) (hv : MeasurableSet v)
  证明: by
  rw [restrict_le_restrict_iff] at hsu hsv
  on_goal 1 =>
    have a := hsu (hu.diff hv) sdiff_subset
    have b := hsv (hv.diff hu) sdiff_subset
    rw [Set.symmDiff_def]; rw [of_union (v := s) (Set.disjoint_of_subset_left sdiff_subset disjoint_sdiff_self_right)
        (hu.diff hv) (hv.diff hu)

Depends on / 依赖: Set.disjoint_of_subset_left, Set.symmDiff_def, disjoint_of_subset_left, disjoint_sdiff_self_right, hu.diff, hv.diff, of_union, on_goal, restrict_le_restrict_iff, sdiff_subset, symmDiff_def, zero_apply
-/
theorem of_sdiff_eq_zero_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hsu : 0 <=[u] s) (hsv : 0 <=[v] s) (hs : s (u ∆ v) = 0) : s (u \ v) = 0 ∧ s (v \ u) = 0 := by
  rw [restrict_le_restrict_iff] at hsu hsv
  on_goal 1 =>
    have a := hsu (hu.diff hv) sdiff_subset
    have b := hsv (hv.diff hu) sdiff_subset
    rw [Set.symmDiff_def]; rw [of_union (v := s) (Set.disjoint_of_subset_left sdiff_subset disjoint_sdiff_self_right)
        (hu.diff hv) (hv.diff hu)] at hs
    rw [zero_apply] at a b
    constructor
  · linarith
  · linarith
  · assumption
  · assumption

@[deprecated (since := "2026-06-03")]
alias of_diff_eq_zero_of_symmDiff_eq_zero_positive := of_sdiff_eq_zero_of_symmDiff_eq_zero_positive

/--
theorem `of_sdiff_eq_zero_of_symmDiff_eq_zero_negative` / 定理 `of_sdiff_eq_zero_of_symmDiff_eq_zero_negative`

English:
theorem of_sdiff_eq_zero_of_symmDiff_eq_zero_negative
  statement: (hu : MeasurableSet u) (hv : MeasurableSet v)
  proof: by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv]; rw [neg_zero] at hsv
  have := of_sdiff_eq_zero_of_symmDiff_eq_zero_positive hu hv hsu hsv
  simp only [neg_apply, neg_eq_zero] at this
  exact this hs

@[deprecated (since := "2026-06-03")]
alias of_diff_eq_zero

中文:
定理 of_sdiff_eq_zero_of_symmDiff_eq_zero_negative
  结论: (hu : MeasurableSet u) (hv : MeasurableSet v)
  证明: by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv]; rw [neg_zero] at hsv
  have := of_sdiff_eq_zero_of_symmDiff_eq_zero_positive hu hv hsu hsv
  simp only [neg_apply, neg_eq_zero] at this
  exact this hs

@[deprecated (since := "2026-06-03")]
alias of_diff_eq_zero

Depends on / 依赖: neg_apply, neg_eq_zero, neg_le_neg_iff, neg_zero, of_sdiff_eq_zero_of_symmDiff_eq_zero_positive, s.neg_le_neg_iff
-/
theorem of_sdiff_eq_zero_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hsu : s <=[u] 0) (hsv : s <=[v] 0) (hs : s (u ∆ v) = 0) : s (u \ v) = 0 ∧ s (v \ u) = 0 := by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv]; rw [neg_zero] at hsv
  have := of_sdiff_eq_zero_of_symmDiff_eq_zero_positive hu hv hsu hsv
  simp only [neg_apply, neg_eq_zero] at this
  exact this hs

@[deprecated (since := "2026-06-03")]
alias of_diff_eq_zero_of_symmDiff_eq_zero_negative := of_sdiff_eq_zero_of_symmDiff_eq_zero_negative

/--
theorem `of_inter_eq_of_symmDiff_eq_zero_positive` / 定理 `of_inter_eq_of_symmDiff_eq_zero_positive`

English:
theorem of_inter_eq_of_symmDiff_eq_zero_positive
  statement: (hu : MeasurableSet u) (hv : MeasurableSet v)
  proof: by
  have hwuv : s ((w inter u) ∆ (w inter v)) = 0 := by
    refine
      subset_positive_null_set (hu.union hv) ((hw.inter hu).symmDiff (hw.inter hv))
        (hu.symmDiff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs
        Set.symmDiff_subset_union ?_
    rw [← Set.inter_symmDiff_distrib

中文:
定理 of_inter_eq_of_symmDiff_eq_zero_positive
  结论: (hu : MeasurableSet u) (hv : MeasurableSet v)
  证明: by
  have hwuv : s ((w inter u) ∆ (w inter v)) = 0 := by
    refine
      subset_positive_null_set (hu.union hv) ((hw.inter hu).symmDiff (hw.inter hv))
        (hu.symmDiff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs
        Set.symmDiff_subset_union ?_
    rw [← Set.inter_symmDiff_distrib

Depends on / 依赖: Set.inter_subset_right, Set.inter_symmDiff_distrib_left, Set.symmDiff_subset_union, hu.symmDiff, hu.union, hw.inter, inter_subset_right, inter_symmDiff_distrib_left, of_sdiff_eq_zero_of_symmDiff_eq_zero_positive, restrict_le_restrict_subset, restrict_le_restrict_union, subset_positive_null_set, symmDiff, symmDiff_subset_union, w.inter_subset_right
-/
theorem of_inter_eq_of_symmDiff_eq_zero_positive (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : 0 <=[u] s) (hsv : 0 <=[v] s) (hs : s (u ∆ v) = 0) :
    s (w inter u) = s (w inter v) := by
  have hwuv : s ((w inter u) ∆ (w inter v)) = 0 := by
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
  rw [← of_sdiff_of_sdiff_eq_zero (hw.inter hu) (hw.inter hv) hvu]; rw [huv]; rw [zero_add]

/--
theorem `of_inter_eq_of_symmDiff_eq_zero_negative` / 定理 `of_inter_eq_of_symmDiff_eq_zero_negative`

English:
theorem of_inter_eq_of_symmDiff_eq_zero_negative
  statement: (hu : MeasurableSet u) (hv : MeasurableSet v)
  proof: by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv]; rw [neg_zero] at hsv
  have := of_inter_eq_of_symmDiff_eq_zero_positive hu hv hw hsu hsv
  simp only [neg_apply, neg_inj, neg_eq_zero] at this
  exact this hs

中文:
定理 of_inter_eq_of_symmDiff_eq_zero_negative
  结论: (hu : MeasurableSet u) (hv : MeasurableSet v)
  证明: by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv]; rw [neg_zero] at hsv
  have := of_inter_eq_of_symmDiff_eq_zero_positive hu hv hw hsu hsv
  simp only [neg_apply, neg_inj, neg_eq_zero] at this
  exact this hs

Depends on / 依赖: neg_apply, neg_eq_zero, neg_inj, neg_le_neg_iff, neg_zero, of_inter_eq_of_symmDiff_eq_zero_positive, s.neg_le_neg_iff
-/
theorem of_inter_eq_of_symmDiff_eq_zero_negative (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hw : MeasurableSet w) (hsu : s <=[u] 0) (hsv : s <=[v] 0) (hs : s (u ∆ v) = 0) :
    s (w inter u) = s (w inter v) := by
  rw [← s.neg_le_neg_iff _ hu]; rw [neg_zero] at hsu
  rw [← s.neg_le_neg_iff _ hv]; rw [neg_zero] at hsv
  have := of_inter_eq_of_symmDiff_eq_zero_positive hu hv hw hsu hsv
  simp only [neg_apply, neg_inj, neg_eq_zero] at this
  exact this hs

end

end SignedMeasure

namespace JordanDecomposition

open Measure VectorMeasure SignedMeasure Function

/--
theorem `eq_of_posPart_eq_posPart` / 定理 `eq_of_posPart_eq_posPart`

English:
theorem eq_of_posPart_eq_posPart
  statement: {j₁ j₂ : JordanDecomposition α}
  proof: by
  ext1
  · exact hj
  · rw [← toSignedMeasure_eq_toSignedMeasure_iff]
    unfold toSignedMeasure at hj'
    simp_rw [hj, sub_right_inj] at hj'
    exact hj'

中文:
定理 eq_of_posPart_eq_posPart
  结论: {j₁ j₂ : JordanDecomposition α}
  证明: by
  ext1
  · exact hj
  · rw [← toSignedMeasure_eq_toSignedMeasure_iff]
    unfold toSignedMeasure at hj'
    simp_rw [hj, sub_right_inj] at hj'
    exact hj'
-/
private theorem eq_of_posPart_eq_posPart {j₁ j₂ : JordanDecomposition α}
    (hj : j₁.posPart = j₂.posPart) (hj' : j₁.toSignedMeasure = j₂.toSignedMeasure) : j₁ = j₂ := by
  ext1
  · exact hj
  · rw [← toSignedMeasure_eq_toSignedMeasure_iff]
    unfold toSignedMeasure at hj'
    simp_rw [hj, sub_right_inj] at hj'
    exact hj'

/--
theorem `toSignedMeasure_injective` / 定理 `toSignedMeasure_injective`

English:
theorem toSignedMeasure_injective
  statement: Injective @JordanDecomposition.toSignedMeasure α _
  proof: by
  /- The main idea is that two Jordan decompositions of a signed measure provide two
    Hahn decompositions for that measure. Then, from `of_symmDiff_compl_positive_negative`,
    the symmetric difference of the two Hahn decompositions has measure zero, thus, allowing us to
    show the equality

中文:
定理 toSignedMeasure_injective
  结论: Injective @JordanDecomposition.toSignedMeasure α _
  证明: by
  /- The main idea is that two Jordan decompositions of a signed measure provide two
    Hahn decompositions for that measure. Then, from `of_symmDiff_compl_positive_negative`,
    the symmetric difference of the two Hahn decompositions has measure zero, thus, allowing us to
    show the equality
-/
theorem toSignedMeasure_injective : Injective @JordanDecomposition.toSignedMeasure α _ := by
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
  have hμ₁ : j₁.posPart.real i = j₁.toSignedMeasure (i inter Sᶜ) := by
    rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply (hi.inter hS₁.compl)]; rw [measureReal_def (μ := j₁.negPart)]; rw [show j₁.negPart (i inter Sᶜ) = 0 from
        nonpos_iff_eq_zero.1 (hS₅ ▸ measure_mono Set.inter_subset_right)]; rw [ENNReal.toReal_zero]; rw [sub_zero]
    conv_lhs => rw [← Set.inter_union_compl i S]
    rw [measureReal_union]; rw [measureReal_def]; rw [show j₁.posPart (i inter S) = 0 from
        nonpos_iff_eq_zero.1 (hS₄ ▸ measure_mono Set.inter_subset_right)]; rw [ENNReal.toReal_zero]; rw [zero_add]
    · refine
        Set.disjoint_of_subset_left Set.inter_subset_right
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right)
    · exact hi.inter hS₁.compl
  have hμ₂ : j₂.posPart.real i = j₂.toSignedMeasure (i inter Tᶜ) := by
    rw [toSignedMeasure]; rw [toSignedMeasure_sub_apply (hi.inter hT₁.compl)]; rw [measureReal_def (μ := j₂.negPart)]; rw [show j₂.negPart (i inter Tᶜ) = 0 from
        nonpos_iff_eq_zero.1 (hT₅ ▸ measure_mono Set.inter_subset_right)]; rw [ENNReal.toReal_zero]; rw [sub_zero]
    conv_lhs => rw [← Set.inter_union_compl i T]
    rw [measureReal_union]; rw [measureReal_def]; rw [show j₂.posPart (i inter T) = 0 from
        nonpos_iff_eq_zero.1 (hT₄ ▸ measure_mono Set.inter_subset_right)]; rw [ENNReal.toReal_zero]; rw [zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_right
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right)
    · exact hi.inter hT₁.compl
  -- since the two signed measures associated with the Jordan decompositions are the same,
  -- and the symmetric difference of the Hahn decompositions have measure zero, the result follows
  rw [← measureReal_eq_measureReal_iff]; rw [hμ₁]; rw [hμ₂]; rw [← hj]
  exact of_inter_eq_of_symmDiff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁

@[simp]
/--
theorem `toJordanDecomposition_toSignedMeasure` / 定理 `toJordanDecomposition_toSignedMeasure`

English:
theorem toJordanDecomposition_toSignedMeasure
  given: (j : JordanDecomposition α)
  proof: (@toSignedMeasure_injective _ _ j j.toSignedMeasure.toJordanDecomposition (by simp)).symm

中文:
定理 toJordanDecomposition_toSignedMeasure
  条件: (j : JordanDecomposition α)
  证明: (@toSignedMeasure_injective _ _ j j.toSignedMeasure.toJordanDecomposition (by simp)).symm

Depends on / 依赖: j.toSignedMeasure.toJordanDecomposition, toJordanDecomposition, toSignedMeasure, toSignedMeasure_injective
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
/--
Definition of `toJordanDecompositionEquiv` / `toJordanDecompositionEquiv` 的定义

English:
definition toJordanDecompositionEquiv
  signature: (α : Type*) [MeasurableSpace α]
  body: toJordanDecomposition
  invFun := toSignedMeasure
  left_inv := toSignedMeasure_toJordanDecomposition
  right_inv := toJordanDecomposition_toSignedMeasure

中文:
定义 toJordanDecompositionEquiv
  签名: (α : 类型) [MeasurableSpace α]
  定义体: toJordanDecomposition
  invFun := toSignedMeasure
  left_inv := toSignedMeasure_toJordanDecomposition
  right_inv := toJordanDecomposition_toSignedMeasure

Depends on / 依赖: toJordanDecomposition
-/
def toJordanDecompositionEquiv (α : Type*) [MeasurableSpace α] :
    SignedMeasure α ≃ JordanDecomposition α where
  toFun := toJordanDecomposition
  invFun := toSignedMeasure
  left_inv := toSignedMeasure_toJordanDecomposition
  right_inv := toJordanDecomposition_toSignedMeasure

/--
theorem `toJordanDecomposition_zero` / 定理 `toJordanDecomposition_zero`

English:
theorem toJordanDecomposition_zero
  statement: (0 : SignedMeasure α).toJordanDecomposition = 0
  proof: by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_zero]

中文:
定理 toJordanDecomposition_zero
  结论: (0 : SignedMeasure α).toJordanDecomposition = 0
  证明: by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_zero]

Depends on / 依赖: toSignedMeasure_injective, toSignedMeasure_zero
-/
theorem toJordanDecomposition_zero : (0 : SignedMeasure α).toJordanDecomposition = 0 := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_zero]

/--
theorem `toJordanDecomposition_neg` / 定理 `toJordanDecomposition_neg`

English:
theorem toJordanDecomposition_neg
  given: (s : SignedMeasure α)
  proof: by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_neg]

中文:
定理 toJordanDecomposition_neg
  条件: (s : SignedMeasure α)
  证明: by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_neg]

Depends on / 依赖: toSignedMeasure_injective, toSignedMeasure_neg
-/
theorem toJordanDecomposition_neg (s : SignedMeasure α) :
    (-s).toJordanDecomposition = -s.toJordanDecomposition := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_neg]

/--
theorem `toJordanDecomposition_smul` / 定理 `toJordanDecomposition_smul`

English:
theorem toJordanDecomposition_smul
  given: (s : SignedMeasure α) (r : Real>=0)
  proof: by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_smul]

中文:
定理 toJordanDecomposition_smul
  条件: (s : SignedMeasure α) (r : 实数>=0)
  证明: by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_smul]

Depends on / 依赖: toSignedMeasure_injective, toSignedMeasure_smul
-/
theorem toJordanDecomposition_smul (s : SignedMeasure α) (r : Real>=0) :
    (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  apply toSignedMeasure_injective
  simp [toSignedMeasure_smul]

/--
theorem `toJordanDecomposition_smul_real_nonneg` / 定理 `toJordanDecomposition_smul_real_nonneg`

English:
theorem toJordanDecomposition_smul_real_nonneg
  statement: (s : SignedMeasure α) (r : Real)
  proof: by
  lift r to Real>=0 using hr
  rw [JordanDecomposition.coe_smul]; rw [← toJordanDecomposition_smul]
  rfl

中文:
定理 toJordanDecomposition_smul_real_nonneg
  结论: (s : SignedMeasure α) (r : 实数)
  证明: by
  lift r to Real>=0 using hr
  rw [JordanDecomposition.coe_smul]; rw [← toJordanDecomposition_smul]
  rfl
-/
private theorem toJordanDecomposition_smul_real_nonneg (s : SignedMeasure α) (r : Real)
    (hr : 0 <= r) : (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  lift r to Real>=0 using hr
  rw [JordanDecomposition.coe_smul]; rw [← toJordanDecomposition_smul]
  rfl

/--
theorem `toJordanDecomposition_smul_real` / 定理 `toJordanDecomposition_smul_real`

English:
theorem toJordanDecomposition_smul_real
  given: (s : SignedMeasure α) (r : Real)
  proof: by
  by_cases! hr : 0 <= r
  · exact toJordanDecomposition_smul_real_nonneg s r hr
  · ext1
    · rw [real_smul_posPart_neg _ _ hr,
        show r • s = -(-r • s) by rw [neg_smul, neg_neg], toJordanDecomposition_neg, neg_posPart,
        toJordanDecomposition_smul_real_nonneg, ← smul_negPart, real_s

中文:
定理 toJordanDecomposition_smul_real
  条件: (s : SignedMeasure α) (r : 实数)
  证明: by
  by_cases! hr : 0 <= r
  · exact toJordanDecomposition_smul_real_nonneg s r hr
  · ext1
    · rw [real_smul_posPart_neg _ _ hr,
        show r • s = -(-r • s) by rw [neg_smul, neg_neg], toJordanDecomposition_neg, neg_posPart,
        toJordanDecomposition_smul_real_nonneg, ← smul_negPart, real_s

Depends on / 依赖: Left.nonneg_neg_iff, all_goals, hr.le, neg_neg, neg_negPart, neg_posPart, neg_smul, nonneg_neg_iff, real_smul_negPart_neg, real_smul_nonneg, real_smul_posPart_neg, smul_negPart, toJordanDecomposition_neg, toJordanDecomposition_smul_real_nonneg
-/
theorem toJordanDecomposition_smul_real (s : SignedMeasure α) (r : Real) :
    (r • s).toJordanDecomposition = r • s.toJordanDecomposition := by
  by_cases! hr : 0 <= r
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

/--
theorem `toJordanDecomposition_eq` / 定理 `toJordanDecomposition_eq`

English:
theorem toJordanDecomposition_eq
  statement: {s : SignedMeasure α} {j : JordanDecomposition α}
  proof: by
  rw [h]; rw [toJordanDecomposition_toSignedMeasure]

中文:
定理 toJordanDecomposition_eq
  结论: {s : SignedMeasure α} {j : JordanDecomposition α}
  证明: by
  rw [h]; rw [toJordanDecomposition_toSignedMeasure]

Depends on / 依赖: toJordanDecomposition_toSignedMeasure
-/
theorem toJordanDecomposition_eq {s : SignedMeasure α} {j : JordanDecomposition α}
    (h : s = j.toSignedMeasure) : s.toJordanDecomposition = j := by
  rw [h]; rw [toJordanDecomposition_toSignedMeasure]

/--
Definition of `totalVariation` / `totalVariation` 的定义

English:
definition totalVariation
  signature: (s : SignedMeasure α)
  body: s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart

中文:
定义 totalVariation
  签名: (s : SignedMeasure α)
  定义体: s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart

Depends on / 依赖: negPart, posPart, s.toJordanDecomposition.negPart, s.toJordanDecomposition.posPart, toJordanDecomposition
-/
def totalVariation (s : SignedMeasure α) : Measure α :=
  s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart

instance (s : SignedMeasure α) : IsFiniteMeasure s.totalVariation := by
  unfold totalVariation; infer_instance

/--
theorem `totalVariation_zero` / 定理 `totalVariation_zero`

English:
theorem totalVariation_zero
  statement: (0 : SignedMeasure α).totalVariation = 0
  proof: by
  simp [totalVariation, toJordanDecomposition_zero]

中文:
定理 totalVariation_zero
  结论: (0 : SignedMeasure α).totalVariation = 0
  证明: by
  simp [totalVariation, toJordanDecomposition_zero]

Depends on / 依赖: toJordanDecomposition_zero, totalVariation
-/
theorem totalVariation_zero : (0 : SignedMeasure α).totalVariation = 0 := by
  simp [totalVariation, toJordanDecomposition_zero]

/--
theorem `totalVariation_neg` / 定理 `totalVariation_neg`

English:
theorem totalVariation_neg
  given: (s : SignedMeasure α)
  statement: (-s).totalVariation = s.totalVariation
  proof: by
  simp [totalVariation, toJordanDecomposition_neg, add_comm]

中文:
定理 totalVariation_neg
  条件: (s : SignedMeasure α)
  结论: (-s).totalVariation = s.totalVariation
  证明: by
  simp [totalVariation, toJordanDecomposition_neg, add_comm]

Depends on / 依赖: add_comm, toJordanDecomposition_neg, totalVariation
-/
theorem totalVariation_neg (s : SignedMeasure α) : (-s).totalVariation = s.totalVariation := by
  simp [totalVariation, toJordanDecomposition_neg, add_comm]

/--
theorem `apply_eq_posPart_real_sub_negPart_real` / 定理 `apply_eq_posPart_real_sub_negPart_real`

English:
theorem apply_eq_posPart_real_sub_negPart_real
  statement: (s : SignedMeasure α) {i : Set α}
  proof: by
  grind [Measure.toSignedMeasure_sub_apply, toSignedMeasure, toSignedMeasure_toJordanDecomposition]

中文:
定理 apply_eq_posPart_real_sub_negPart_real
  结论: (s : SignedMeasure α) {i : Set α}
  证明: by
  grind [Measure.toSignedMeasure_sub_apply, toSignedMeasure, toSignedMeasure_toJordanDecomposition]

Depends on / 依赖: Measure, Measure.toSignedMeasure_sub_apply, toSignedMeasure, toSignedMeasure_sub_apply, toSignedMeasure_toJordanDecomposition
-/
theorem apply_eq_posPart_real_sub_negPart_real (s : SignedMeasure α) {i : Set α}
    (hi : MeasurableSet i) :
    s i = s.toJordanDecomposition.posPart.real i - s.toJordanDecomposition.negPart.real i := by
  grind [Measure.toSignedMeasure_sub_apply, toSignedMeasure, toSignedMeasure_toJordanDecomposition]

/--
theorem `null_of_totalVariation_zero` / 定理 `null_of_totalVariation_zero`

English:
theorem null_of_totalVariation_zero
  statement: (s : SignedMeasure α) {i : Set α}
  proof: by
  rw [totalVariation]; rw [Measure.coe_add]; rw [Pi.add_apply]; rw [add_eq_zero] at hs
  by_cases hi : MeasurableSet i
  · rw [← toSignedMeasure_toJordanDecomposition s, toSignedMeasure]
    simp [hi, measureReal_def, hs.1, hs.2]
  · simp [hi]

中文:
定理 null_of_totalVariation_zero
  结论: (s : SignedMeasure α) {i : Set α}
  证明: by
  rw [totalVariation]; rw [Measure.coe_add]; rw [Pi.add_apply]; rw [add_eq_zero] at hs
  by_cases hi : MeasurableSet i
  · rw [← toSignedMeasure_toJordanDecomposition s, toSignedMeasure]
    simp [hi, measureReal_def, hs.1, hs.2]
  · simp [hi]

Depends on / 依赖: MeasurableSet, Measure, Measure.coe_add, Pi.add_apply, add_apply, add_eq_zero, coe_add, measureReal_def, toSignedMeasure, toSignedMeasure_toJordanDecomposition, totalVariation
-/
theorem null_of_totalVariation_zero (s : SignedMeasure α) {i : Set α}
    (hs : s.totalVariation i = 0) : s i = 0 := by
  rw [totalVariation]; rw [Measure.coe_add]; rw [Pi.add_apply]; rw [add_eq_zero] at hs
  by_cases hi : MeasurableSet i
  · rw [← toSignedMeasure_toJordanDecomposition s, toSignedMeasure]
    simp [hi, measureReal_def, hs.1, hs.2]
  · simp [hi]

/--
theorem `absolutelyContinuous_ennreal_iff` / 定理 `absolutelyContinuous_ennreal_iff`

English:
theorem absolutelyContinuous_ennreal_iff
  given: (s : SignedMeasure α) (μ : VectorMeasure α Real>=0∞)
  proof: by
  constructor <;> intro h
  · refine Measure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    rw [totalVariation]; rw [Measure.add_apply]; rw [hpos]; rw [hneg]; rw [toMeasureOfZeroLE_apply _ _ _ hS₁]; rw [toMeasureOfLEZero_a

中文:
定理 absolutelyContinuous_ennreal_iff
  条件: (s : SignedMeasure α) (μ : VectorMeasure α 实数>=0∞)
  证明: by
  constructor <;> intro h
  · refine Measure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    rw [totalVariation]; rw [Measure.add_apply]; rw [hpos]; rw [hneg]; rw [toMeasureOfZeroLE_apply _ _ _ hS₁]; rw [toMeasureOfLEZero_a

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.mk, Measure.add_apply, VectorMeasure, VectorMeasure.Ab, VectorMeasure.AbsolutelyContinuous.ennrealToMeasure, add_apply, ennrealToMeasure, i.inter_subset_right, inter_subset_right, measure_mono_null, s.toJordanDecomposition_spec, toJordanDecomposition_spec, toMeasureOfLEZero_apply, toMeasureOfZeroLE_apply, totalVariation
-/
theorem absolutelyContinuous_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α Real>=0∞) :
    s ≪ᵥ μ ↔ s.totalVariation ≪ μ.ennrealToMeasure := by
  constructor <;> intro h
  · refine Measure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    rw [totalVariation]; rw [Measure.add_apply]; rw [hpos]; rw [hneg]; rw [toMeasureOfZeroLE_apply _ _ _ hS₁]; rw [toMeasureOfLEZero_apply _ _ _ hS₁]
    rw [← VectorMeasure.AbsolutelyContinuous.ennrealToMeasure] at h
    simp [h (measure_mono_null (i.inter_subset_right) hS₂),
      h (measure_mono_null (iᶜ.inter_subset_right) hS₂)]
  · refine VectorMeasure.AbsolutelyContinuous.mk fun S hS₁ hS₂ => ?_
    rw [← VectorMeasure.ennrealToMeasure_apply hS₁] at hS₂
    exact null_of_totalVariation_zero s (h hS₂)

/--
theorem `totalVariation_absolutelyContinuous_iff` / 定理 `totalVariation_absolutelyContinuous_iff`

English:
theorem totalVariation_absolutelyContinuous_iff
  given: (s : SignedMeasure α) (μ : Measure α)
  proof: by
  constructor <;> intro h
  · constructor
    all_goals
      refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
      have := h hS₂
      rw [totalVariation]; rw [Measure.add_apply]; rw [add_eq_zero] at this
    exacts [this.1, this.2]
  · refine Measure.AbsolutelyContinuous.mk fun S _ hS₂

中文:
定理 totalVariation_absolutelyContinuous_iff
  条件: (s : SignedMeasure α) (μ : Measure α)
  证明: by
  constructor <;> intro h
  · constructor
    all_goals
      refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
      have := h hS₂
      rw [totalVariation]; rw [Measure.add_apply]; rw [add_eq_zero] at this
    exacts [this.1, this.2]
  · refine Measure.AbsolutelyContinuous.mk fun S _ hS₂

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.mk, Measure.add_apply, add_apply, add_eq_zero, add_zero, all_goals, exacts, totalVariation
-/
theorem totalVariation_absolutelyContinuous_iff (s : SignedMeasure α) (μ : Measure α) :
    s.totalVariation ≪ μ ↔
      s.toJordanDecomposition.posPart ≪ μ ∧ s.toJordanDecomposition.negPart ≪ μ := by
  constructor <;> intro h
  · constructor
    all_goals
      refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
      have := h hS₂
      rw [totalVariation]; rw [Measure.add_apply]; rw [add_eq_zero] at this
    exacts [this.1, this.2]
  · refine Measure.AbsolutelyContinuous.mk fun S _ hS₂ => ?_
    rw [totalVariation]; rw [Measure.add_apply]; rw [h.1 hS₂]; rw [h.2 hS₂]; rw [add_zero]

-- TODO: Generalize to vector measures once total variation on vector measures is defined
/--
theorem `mutuallySingular_iff` / 定理 `mutuallySingular_iff`

English:
theorem mutuallySingular_iff
  given: (s t : SignedMeasure α)
  proof: by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hipos, hineg⟩ := s.toJordanDecomposition_spec
    obtain ⟨j, hj₁, hj₂, hj₃, hjpos, hjneg⟩ := t.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hipos, hineg, toMeasureO

中文:
定理 mutuallySingular_iff
  条件: (s t : SignedMeasure α)
  证明: by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hipos, hineg⟩ := s.toJordanDecomposition_spec
    obtain ⟨j, hj₁, hj₂, hj₃, hjpos, hjneg⟩ := t.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hipos, hineg, toMeasureO

Depends on / 依赖: Measure, Measure.add_apply, Set.inter_subset_right, add_apply, hmeas.compl, inter_subset_right, s.toJordanDecomposition_spec, t.toJordanDecomposition_spec, toJordanDecomposition_spec, toMeasureOfLEZero_appl, toMeasureOfLEZero_apply, toMeasureOfZeroLE_apply, totalVariation
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

/--
theorem `mutuallySingular_ennreal_iff` / 定理 `mutuallySingular_ennreal_iff`

English:
theorem mutuallySingular_ennreal_iff
  given: (s : SignedMeasure α) (μ : VectorMeasure α Real>=0∞)
  proof: by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hpos, hneg, toMeasureOfZeroLE_apply _ _ _ hmeas,
        toMeasureOfLEZero_apply _ _ _ hmeas]
      si

中文:
定理 mutuallySingular_ennreal_iff
  条件: (s : SignedMeasure α) (μ : VectorMeasure α 实数>=0∞)
  证明: by
  constructor
  · rintro ⟨u, hmeas, hu₁, hu₂⟩
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
    refine ⟨u, hmeas, ?_, ?_⟩
    · rw [totalVariation, Measure.add_apply, hpos, hneg, toMeasureOfZeroLE_apply _ _ _ hmeas,
        toMeasureOfLEZero_apply _ _ _ hmeas]
      si

Depends on / 依赖: Measure, Measure.add_apply, MutuallySingular, Set.Subset.refl, Set.inter_subset_right, Subset, VectorMeasure, VectorMeasure.MutuallySingular.mk, VectorMeasure.ennrealToMeasure_apply, add_apply, ennrealToMeasure_apply, hmeas.compl, inter_subset_right, null_of_total, s.toJordanDecomposition_spec, toJordanDecomposition_spec, toMeasureOfLEZero_apply, toMeasureOfZeroLE_apply, totalVariation
-/
theorem mutuallySingular_ennreal_iff (s : SignedMeasure α) (μ : VectorMeasure α Real>=0∞) :
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

/--
theorem `totalVariation_mutuallySingular_iff` / 定理 `totalVariation_mutuallySingular_iff`

English:
theorem totalVariation_mutuallySingular_iff
  given: (s : SignedMeasure α) (μ : Measure α)
  proof: Measure.MutuallySingular.add_left_iff

中文:
定理 totalVariation_mutuallySingular_iff
  条件: (s : SignedMeasure α) (μ : Measure α)
  证明: Measure.MutuallySingular.add_left_iff

Depends on / 依赖: Measure, Measure.MutuallySingular.add_left_iff, MutuallySingular, add_left_iff
-/
theorem totalVariation_mutuallySingular_iff (s : SignedMeasure α) (μ : Measure α) :
    s.totalVariation ⟂ₘ μ ↔
      s.toJordanDecomposition.posPart ⟂ₘ μ ∧ s.toJordanDecomposition.negPart ⟂ₘ μ :=
  Measure.MutuallySingular.add_left_iff

end SignedMeasure

end MeasureTheory
