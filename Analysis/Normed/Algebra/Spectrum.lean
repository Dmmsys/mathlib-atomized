/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Real.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.
Theorems specific to *complex* Banach algebras, such as *Gelfand's formula* can be found in
`Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`.

## Main definitions

* `spectralRadius : ℝ≥0∞`: supremum of `‖k‖₊` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `spectrum.isOpen_resolventSet`: the resolvent set is open.
* `spectrum.isClosed`: the spectrum is closed.
* `spectrum.subset_closedBall_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.isCompact`: the spectrum is compact.
* `spectrum.spectralRadius_le_nnnorm`: the spectral radius is bounded above by the norm.

-/

@[expose] public section

assert_not_exists ProbabilityTheory.cond
assert_not_exists HasFDerivAt

open NormedSpace Topology -- For `NormedSpace.exp`.
open scoped ENNReal NNReal

/-- The *spectral radius* is the supremum of the `nnnorm` (`‖·‖₊`) of elements in the spectrum,
coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
case, `spectralRadius a = 0`. It is also possible that `spectrum 𝕜 a` be unbounded (though
not for Banach algebras, see `spectrum.isBounded`, below). In this case,
`spectralRadius a = ∞`. -/
@[wikidata Q249748]
/--
Definition of `spectralRadius` / `spectralRadius` 的定义

English:
definition spectralRadius
  signature: (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
  body: ⨆ k in spectrum 𝕜 a, ‖k‖₊

中文:
定义 spectralRadius
  签名: (𝕜 : 类型) {A : 类型} [赋范域 𝕜] [环 A] [代数 𝕜 A]
  定义体: ⨆ k in spectrum 𝕜 a, ‖k‖₊

Depends on / 依赖: spectrum
-/
noncomputable def spectralRadius (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) : Real>=0∞ :=
  ⨆ k in spectrum 𝕜 a, ‖k‖₊

variable {𝕜 : Type*} {A : Type*}

namespace spectrum

section SpectrumCompact

open Filter

variable [NormedField 𝕜]

local notation "σ" => spectrum 𝕜
local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

section Algebra

variable [Ring A] [Algebra 𝕜 A]

@[simp]
/--
theorem `SpectralRadius.of_subsingleton` / 定理 `SpectralRadius.of_subsingleton`

English:
theorem SpectralRadius.of_subsingleton
  given: [Subsingleton A] (a : A)
  proof: by
  simp [spectralRadius]

@[simp]

中文:
定理 SpectralRadius.of_subsingleton
  条件: [子单例 A] (a : A)
  证明: by
  simp [spectralRadius]

@[simp]

Depends on / 依赖: spectralRadius
-/
theorem SpectralRadius.of_subsingleton [Subsingleton A] (a : A) :
    spectralRadius 𝕜 a = 0 := by
  simp [spectralRadius]

@[simp]
/--
theorem `spectralRadius_zero` / 定理 `spectralRadius_zero`

English:
theorem spectralRadius_zero
  statement: spectralRadius 𝕜 (0 : A) = 0
  proof: by
  nontriviality A
  simp [spectralRadius]

@[simp]

中文:
定理 spectralRadius_zero
  结论: spectralRadius 𝕜 (0 : A) = 0
  证明: by
  nontriviality A
  simp [spectralRadius]

@[simp]

Depends on / 依赖: nontriviality, spectralRadius
-/
theorem spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0 := by
  nontriviality A
  simp [spectralRadius]

@[simp]
/--
theorem `spectralRadius_one` / 定理 `spectralRadius_one`

English:
theorem spectralRadius_one
  given: [Nontrivial A]
  proof: by
  simp [spectralRadius]

中文:
定理 spectralRadius_one
  条件: [非平凡 A]
  证明: by
  simp [spectralRadius]

Depends on / 依赖: spectralRadius
-/
theorem spectralRadius_one [Nontrivial A] :
    spectralRadius 𝕜 (1 : A) = 1 := by
  simp [spectralRadius]

/--
theorem `mem_resolventSet_of_spectralRadius_lt` / 定理 `mem_resolventSet_of_spectralRadius_lt`

English:
theorem mem_resolventSet_of_spectralRadius_lt
  statement: {a : A} {k : 𝕜}
  proof: Classical.not_not.mp fun hn => h.not_ge le_iSup₂ (α := Real>=0∞) k hn

中文:
定理 mem_resolventSet_of_spectralRadius_lt
  结论: {a : A} {k : 𝕜}
  证明: Classical.not_not.mp fun hn => h.not_ge le_iSup₂ (α := Real>=0∞) k hn

Depends on / 依赖: Classical, Classical.not_not.mp, h.not_ge, not_ge, not_not
-/
theorem mem_resolventSet_of_spectralRadius_lt {a : A} {k : 𝕜}
    (h : spectralRadius 𝕜 a < ‖k‖₊) : k in ρ a :=
Classical.not_not.mp fun hn => h.not_ge le_iSup₂ (α := Real>=0∞) k hn

/--
lemma `spectralRadius_pow_le` / 引理 `spectralRadius_pow_le`

English:
lemma spectralRadius_pow_le
  given: (a : A) (n : Nat) (hn : n != 0)
  proof: by
  simp only [spectralRadius, ENNReal.iSup₂_pow_of_ne_zero _ hn]
  refine iSup₂_le fun x hx => ?_
  apply le_iSup₂_of_le (x ^ n) (spectrum.pow_mem_pow a n hx)
  simp

中文:
引理 spectralRadius_pow_le
  条件: (a : A) (n : 自然数) (hn : n != 0)
  证明: by
  simp only [spectralRadius, ENNReal.iSup₂_pow_of_ne_zero _ hn]
  refine iSup₂_le fun x hx => ?_
  apply le_iSup₂_of_le (x ^ n) (spectrum.pow_mem_pow a n hx)
  simp

Depends on / 依赖: ENNReal, ENNReal.iSup, pow_mem_pow, spectralRadius, spectrum, spectrum.pow_mem_pow
-/
lemma spectralRadius_pow_le (a : A) (n : Nat) (hn : n != 0) :
    (spectralRadius 𝕜 a) ^ n <= spectralRadius 𝕜 (a ^ n) := by
  simp only [spectralRadius, ENNReal.iSup₂_pow_of_ne_zero _ hn]
  refine iSup₂_le fun x hx => ?_
  apply le_iSup₂_of_le (x ^ n) (spectrum.pow_mem_pow a n hx)
  simp

/--
lemma `spectralRadius_pow_le'` / 引理 `spectralRadius_pow_le'`

English:
lemma spectralRadius_pow_le'
  given: [Nontrivial A] (a : A) (n : Nat)
  proof: by
  cases n
  · simp
  · exact spectralRadius_pow_le a _ (by simp)

中文:
引理 spectralRadius_pow_le'
  条件: [非平凡 A] (a : A) (n : 自然数)
  证明: by
  cases n
  · simp
  · exact spectralRadius_pow_le a _ (by simp)

Depends on / 依赖: spectralRadius_pow_le
-/
lemma spectralRadius_pow_le' [Nontrivial A] (a : A) (n : Nat) :
    (spectralRadius 𝕜 a) ^ n <= spectralRadius 𝕜 (a ^ n) := by
  cases n
  · simp
  · exact spectralRadius_pow_le a _ (by simp)

end Algebra

variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/--
theorem `isOpen_resolventSet` / 定理 `isOpen_resolventSet`

English:
theorem isOpen_resolventSet
  given: (a : A)
  statement: IsOpen (ρ a)
  proof: Units.isOpen.preimage (by fun_prop)

@[simp]

中文:
定理 isOpen_resolventSet
  条件: (a : A)
  结论: 是开集 (ρ a)
  证明: Units.isOpen.preimage (by fun_prop)

@[simp]

Depends on / 依赖: Units.isOpen.preimage, fun_prop, isOpen, preimage
-/
theorem isOpen_resolventSet (a : A) : IsOpen (ρ a) :=
  Units.isOpen.preimage (by fun_prop)

@[simp]
/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: (a : A)
  statement: IsClosed (σ a)
  proof: (isOpen_resolventSet a).isClosed_compl

中文:
定理 isClosed
  条件: (a : A)
  结论: 是闭集 (σ a)
  证明: (isOpen_resolventSet a).isClosed_compl
-/
protected theorem isClosed (a : A) : IsClosed (σ a) :=
  (isOpen_resolventSet a).isClosed_compl

/--
theorem `mem_resolventSet_of_norm_lt_mul` / 定理 `mem_resolventSet_of_norm_lt_mul`

English:
theorem mem_resolventSet_of_norm_lt_mul
  given: {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖)
  statement: k in ρ a
  proof: by
  rw [resolventSet]; rw [Set.mem_ofPred_eq]; rw [Algebra.algebraMap_eq_smul_one]
  nontriviality A
  have hk : k != 0 :=
    ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne'
  let ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  rw [← inv_inv ‖(1 : A)‖]; rw [mul_inv_lt_iff₀' (inv_pos.2 <| norm_pos_iff.2 (one_ne_zero : (1 : A) != 0))] at h
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : A)‖⁻¹ := by simpa [ku, norm_algebraMap] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit

中文:
定理 mem_resolventSet_of_norm_lt_mul
  条件: {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖)
  结论: k in ρ a
  证明: by
  rw [resolventSet]; rw [Set.mem_ofPred_eq]; rw [Algebra.algebraMap_eq_smul_one]
  nontriviality A
  have hk : k != 0 :=
    ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne'
  let ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  rw [← inv_inv ‖(1 : A)‖]; rw [mul_inv_lt_iff₀' (inv_pos.2 <| norm_pos_iff.2 (one_ne_zero : (1 : A) != 0))] at h
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : A)‖⁻¹ := by simpa [ku, norm_algebraMap] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_on, Algebra.algebraMap_eq_smul_one, Set.mem_ofPred_eq, Units.map, Units.mk0, algebraMap_eq_smul_on, algebraMap_eq_smul_one, inv_inv, inv_pos, mem_ofPred_eq, mul_nonneg, ne_zero_of_norm_ne_zero, nontriviality, norm_algebraMap, norm_nonneg, norm_pos_iff, one_ne_zero, resolventSet, sub_eq_add_neg
-/
theorem mem_resolventSet_of_norm_lt_mul {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k in ρ a := by
  rw [resolventSet]; rw [Set.mem_ofPred_eq]; rw [Algebra.algebraMap_eq_smul_one]
  nontriviality A
  have hk : k != 0 :=
    ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne'
  let ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  rw [← inv_inv ‖(1 : A)‖]; rw [mul_inv_lt_iff₀' (inv_pos.2 <| norm_pos_iff.2 (one_ne_zero : (1 : A) != 0))] at h
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : A)‖⁻¹ := by simpa [ku, norm_algebraMap] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit

/--
theorem `mem_resolventSet_of_norm_lt` / 定理 `mem_resolventSet_of_norm_lt`

English:
theorem mem_resolventSet_of_norm_lt
  given: [NormOneClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖)
  statement: k in ρ a
  proof: mem_resolventSet_of_norm_lt_mul (by rwa [norm_one, mul_one])

中文:
定理 mem_resolventSet_of_norm_lt
  条件: [NormOne类 A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖)
  结论: k in ρ a
  证明: mem_resolventSet_of_norm_lt_mul (by rwa [norm_one, mul_one])

Depends on / 依赖: mem_resolventSet_of_norm_lt_mul, mul_one, norm_one
-/
theorem mem_resolventSet_of_norm_lt [NormOneClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖) : k in ρ a :=
  mem_resolventSet_of_norm_lt_mul (by rwa [norm_one, mul_one])

/--
theorem `norm_le_norm_mul_of_mem` / 定理 `norm_le_norm_mul_of_mem`

English:
theorem norm_le_norm_mul_of_mem
  given: {a : A} {k : 𝕜} (hk : k in σ a)
  statement: ‖k‖ <= ‖a‖ * ‖(1 : A)‖
  proof: le_of_not_gt mt mem_resolventSet_of_norm_lt_mul hk

中文:
定理 norm_le_norm_mul_of_mem
  条件: {a : A} {k : 𝕜} (hk : k in σ a)
  结论: ‖k‖ <= ‖a‖ * ‖(1 : A)‖
  证明: le_of_not_gt mt mem_resolventSet_of_norm_lt_mul hk

Depends on / 依赖: le_of_not_gt, mem_resolventSet_of_norm_lt_mul
-/
theorem norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖ * ‖(1 : A)‖ :=
le_of_not_gt mt mem_resolventSet_of_norm_lt_mul hk

/--
theorem `norm_le_norm_of_mem` / 定理 `norm_le_norm_of_mem`

English:
theorem norm_le_norm_of_mem
  given: [NormOneClass A] {a : A} {k : 𝕜} (hk : k in σ a)
  statement: ‖k‖ <= ‖a‖
  proof: le_of_not_gt mt mem_resolventSet_of_norm_lt hk

中文:
定理 norm_le_norm_of_mem
  条件: [NormOne类 A] {a : A} {k : 𝕜} (hk : k in σ a)
  结论: ‖k‖ <= ‖a‖
  证明: le_of_not_gt mt mem_resolventSet_of_norm_lt hk

Depends on / 依赖: le_of_not_gt, mem_resolventSet_of_norm_lt
-/
theorem norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖ :=
le_of_not_gt mt mem_resolventSet_of_norm_lt hk

/--
theorem `subset_closedBall_norm_mul` / 定理 `subset_closedBall_norm_mul`

English:
theorem subset_closedBall_norm_mul
  given: (a : A)
  statement: σ a subseteq Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖)
  proof: fun k hk => by simp [norm_le_norm_mul_of_mem hk]

中文:
定理 subset_closedBall_norm_mul
  条件: (a : A)
  结论: σ a subseteq Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖)
  证明: fun k hk => by simp [norm_le_norm_mul_of_mem hk]

Depends on / 依赖: norm_le_norm_mul_of_mem
-/
theorem subset_closedBall_norm_mul (a : A) : σ a subseteq Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖) :=
  fun k hk => by simp [norm_le_norm_mul_of_mem hk]

/--
theorem `subset_closedBall_norm` / 定理 `subset_closedBall_norm`

English:
theorem subset_closedBall_norm
  given: [NormOneClass A] (a : A)
  statement: σ a subseteq Metric.closedBall (0 : 𝕜) ‖a‖
  proof: fun k hk => by simp [norm_le_norm_of_mem hk]

@[simp]

中文:
定理 subset_closedBall_norm
  条件: [NormOne类 A] (a : A)
  结论: σ a subseteq Metric.closedBall (0 : 𝕜) ‖a‖
  证明: fun k hk => by simp [norm_le_norm_of_mem hk]

@[simp]

Depends on / 依赖: norm_le_norm_of_mem
-/
theorem subset_closedBall_norm [NormOneClass A] (a : A) : σ a subseteq Metric.closedBall (0 : 𝕜) ‖a‖ :=
  fun k hk => by simp [norm_le_norm_of_mem hk]

@[simp]
/--
theorem `isBounded` / 定理 `isBounded`

English:
theorem isBounded
  given: (a : A)
  statement: Bornology.IsBounded (σ a)
  proof: Metric.isBounded_closedBall.subset (subset_closedBall_norm_mul a)

@[simp]

中文:
定理 isBounded
  条件: (a : A)
  结论: 有界结构.IsBounded (σ a)
  证明: Metric.isBounded_closedBall.subset (subset_closedBall_norm_mul a)

@[simp]

Depends on / 依赖: Metric, Metric.isBounded_closedBall.subset, isBounded_closedBall, subset, subset_closedBall_norm_mul
-/
theorem isBounded (a : A) : Bornology.IsBounded (σ a) :=
  Metric.isBounded_closedBall.subset (subset_closedBall_norm_mul a)

@[simp]
/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: [ProperSpace 𝕜] (a : A)
  statement: IsCompact (σ a)
  proof: Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed a) (isBounded a)

grind_pattern spectrum.isCompact => IsCompact (spectrum 𝕜 a)

中文:
定理 isCompact
  条件: [真空间 𝕜] (a : A)
  结论: 是紧集 (σ a)
  证明: Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed a) (isBounded a)

grind_pattern spectrum.isCompact => IsCompact (spectrum 𝕜 a)
-/
protected theorem isCompact [ProperSpace 𝕜] (a : A) : IsCompact (σ a) :=
  Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed a) (isBounded a)

grind_pattern spectrum.isCompact => IsCompact (spectrum 𝕜 a)

/--
Instance `instCompactSpace` / 实例 `instCompactSpace`

English:
instance instCompactSpace
  signature: [ProperSpace 𝕜] (a : A)
  body: isCompact_iff_compactSpace.mp spectrum.isCompact a

中文:
实例 instCompactSpace
  签名: [真空间 𝕜] (a : A)
  定义体: isCompact_iff_compactSpace.mp spectrum.isCompact a

Depends on / 依赖: isCompact, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, spectrum, spectrum.isCompact
-/
instance instCompactSpace [ProperSpace 𝕜] (a : A) : CompactSpace (spectrum 𝕜 a) :=
isCompact_iff_compactSpace.mp spectrum.isCompact a

/--
Instance `instCompactSpaceNNReal` / 实例 `instCompactSpaceNNReal`

English:
instance instCompactSpaceNNReal
  signature: {A : Type*} [NormedRing A] [NormedAlgebra Real A]
  body: by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap Real]
exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage by assumption

@[simp]

中文:
实例 instCompactSpaceNN实数
  签名: {A : 类型} [赋范环 A] [赋范代数 实数 A]
  定义体: by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap Real]
exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage by assumption

@[simp]

Depends on / 依赖: isClosedEmbedding_subtypeVal, isClosed_nonneg, isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage, isCompact_iff_compactSpace, isCompact_preimage, preimage_algebraMap
-/
instance instCompactSpaceNNReal {A : Type*} [NormedRing A] [NormedAlgebra Real A]
    (a : A) [CompactSpace (spectrum Real a)] : CompactSpace (spectrum Real>=0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap Real]
exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage by assumption

@[simp]
/--
theorem `isCompact_nnreal` / 定理 `isCompact_nnreal`

English:
theorem isCompact_nnreal
  statement: {A : Type*} [NormedRing A] [NormedAlgebra Real A]
  proof: by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern isCompact_nnreal => IsCompact (spectrum Real>=0 a)

中文:
定理 isCompact_nnreal
  结论: {A : 类型} [赋范环 A] [赋范代数 实数 A]
  证明: by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern isCompact_nnreal => IsCompact (spectrum Real>=0 a)

Depends on / 依赖: infer_instance, isCompact_iff_compactSpace
-/
theorem isCompact_nnreal {A : Type*} [NormedRing A] [NormedAlgebra Real A]
    (a : A) [CompactSpace (spectrum Real a)] : IsCompact (spectrum Real>=0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern isCompact_nnreal => IsCompact (spectrum Real>=0 a)

section QuasispectrumCompact

variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [CompleteSpace B]
variable [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [ProperSpace 𝕜]

@[simp]
/--
theorem `_root_.quasispectrum.isCompact` / 定理 `_root_.quasispectrum.isCompact`

English:
theorem _root_.quasispectrum.isCompact
  given: (a : B)
  statement: IsCompact (quasispectrum 𝕜 a)
  proof: by
  rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜]; rw [← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 B)]
  exact spectrum.isCompact _

grind_pattern quasispectrum.isCompact => IsCompact (quasispectrum 𝕜 a)

中文:
定理 _root_.quasispectrum.isCompact
  条件: (a : B)
  结论: 是紧集 (quasispectrum 𝕜 a)
  证明: by
  rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜]; rw [← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 B)]
  exact spectrum.isCompact _

grind_pattern quasispectrum.isCompact => IsCompact (quasispectrum 𝕜 a)

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, Unitization, Unitization.quasispectrum_eq_spectrum_inr, WithLp, WithLp.unitizationAlgEquiv, isCompact, quasispectrum_eq_spectrum_inr, spectrum, spectrum.isCompact, spectrum_eq, unitizationAlgEquiv
-/
theorem _root_.quasispectrum.isCompact (a : B) : IsCompact (quasispectrum 𝕜 a) := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜]; rw [← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 B)]
  exact spectrum.isCompact _

grind_pattern quasispectrum.isCompact => IsCompact (quasispectrum 𝕜 a)

/--
Instance `_root_.quasispectrum.instCompactSpace` / 实例 `_root_.quasispectrum.instCompactSpace`

English:
instance _root_.quasispectrum.instCompactSpace
  signature: (a : B)
  body: isCompact_iff_compactSpace.mp quasispectrum.isCompact a

中文:
实例 _root_.quasispectrum.instCompactSpace
  签名: (a : B)
  定义体: isCompact_iff_compactSpace.mp quasispectrum.isCompact a

Depends on / 依赖: isCompact, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, quasispectrum, quasispectrum.isCompact
-/
instance _root_.quasispectrum.instCompactSpace (a : B) :
    CompactSpace (quasispectrum 𝕜 a) :=
isCompact_iff_compactSpace.mp quasispectrum.isCompact a

/--
Instance `_root_.quasispectrum.instCompactSpaceNNReal` / 实例 `_root_.quasispectrum.instCompactSpaceNNReal`

English:
instance _root_.quasispectrum.instCompactSpaceNNReal
  signature: [NormedSpace Real B] [IsScalarTower Real B B]
  body: by
  rw [← isCompact_iff_compactSpace] at *
  rw [← quasispectrum.preimage_algebraMap Real]
exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage by assumption

omit [CompleteSpace B] in
@[simp]

中文:
实例 _root_.quasispectrum.instCompactSpaceNN实数
  签名: [赋范空间 实数 B] [标量塔 实数 B B]
  定义体: by
  rw [← isCompact_iff_compactSpace] at *
  rw [← quasispectrum.preimage_algebraMap Real]
exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage by assumption

omit [CompleteSpace B] in
@[simp]

Depends on / 依赖: isClosedEmbedding_subtypeVal, isClosed_nonneg, isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage, isCompact_iff_compactSpace, isCompact_preimage, preimage_algebraMap, quasispectrum, quasispectrum.preimage_algebraMap
-/
instance _root_.quasispectrum.instCompactSpaceNNReal [NormedSpace Real B] [IsScalarTower Real B B]
    [SMulCommClass Real B B] (a : B) [CompactSpace (quasispectrum Real a)] :
    CompactSpace (quasispectrum Real>=0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← quasispectrum.preimage_algebraMap Real]
exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage by assumption

omit [CompleteSpace B] in
@[simp]
/--
theorem `_root_.quasispectrum.isCompact_nnreal` / 定理 `_root_.quasispectrum.isCompact_nnreal`

English:
theorem _root_.quasispectrum.isCompact_nnreal
  statement: [NormedSpace Real B] [IsScalarTower Real B B]
  proof: by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern quasispectrum.isCompact_nnreal => IsCompact (quasispectrum Real>=0 a)

中文:
定理 _root_.quasispectrum.isCompact_nnreal
  结论: [赋范空间 实数 B] [标量塔 实数 B B]
  证明: by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern quasispectrum.isCompact_nnreal => IsCompact (quasispectrum Real>=0 a)

Depends on / 依赖: infer_instance, isCompact_iff_compactSpace
-/
theorem _root_.quasispectrum.isCompact_nnreal [NormedSpace Real B] [IsScalarTower Real B B]
    [SMulCommClass Real B B] (a : B) [CompactSpace (quasispectrum Real a)] :
    IsCompact (quasispectrum Real>=0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern quasispectrum.isCompact_nnreal => IsCompact (quasispectrum Real>=0 a)

end QuasispectrumCompact

section NNReal

open NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra Real A] [CompleteSpace A] [NormOneClass A]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `le_nnnorm_of_mem` / 定理 `le_nnnorm_of_mem`

English:
theorem le_nnnorm_of_mem
  given: {a : A} {r : Real>=0} (hr : r in spectrum Real>=0 a)
  proof: calc
  r <= ‖(r : Real)‖ := Real.le_norm_self _
  _ <= ‖a‖ := norm_le_norm_of_mem hr

中文:
定理 le_nnnorm_of_mem
  条件: {a : A} {r : 实数>=0} (hr : r in spectrum 实数>=0 a)
  证明: calc
  r <= ‖(r : Real)‖ := Real.le_norm_self _
  _ <= ‖a‖ := norm_le_norm_of_mem hr
-/
theorem le_nnnorm_of_mem {a : A} {r : Real>=0} (hr : r in spectrum Real>=0 a) :
    r <= ‖a‖₊ := calc
  r <= ‖(r : Real)‖ := Real.le_norm_self _
  _ <= ‖a‖ := norm_le_norm_of_mem hr

/--
theorem `coe_le_norm_of_mem` / 定理 `coe_le_norm_of_mem`

English:
theorem coe_le_norm_of_mem
  given: {a : A} {r : Real>=0} (hr : r in spectrum Real>=0 a)
  proof: coe_mono le_nnnorm_of_mem hr

中文:
定理 coe_le_norm_of_mem
  条件: {a : A} {r : 实数>=0} (hr : r in spectrum 实数>=0 a)
  证明: coe_mono le_nnnorm_of_mem hr

Depends on / 依赖: coe_mono, le_nnnorm_of_mem
-/
theorem coe_le_norm_of_mem {a : A} {r : Real>=0} (hr : r in spectrum Real>=0 a) :
    r <= ‖a‖ :=
coe_mono le_nnnorm_of_mem hr

end NNReal

/--
theorem `spectralRadius_le_nnnorm` / 定理 `spectralRadius_le_nnnorm`

English:
theorem spectralRadius_le_nnnorm
  given: [NormOneClass A] (a : A)
  statement: spectralRadius 𝕜 a <= ‖a‖₊
  proof: by
  refine iSup₂_le fun k hk => ?_
  exact mod_cast norm_le_norm_of_mem hk

中文:
定理 spectralRadius_le_nnnorm
  条件: [NormOne类 A] (a : A)
  结论: spectralRadius 𝕜 a <= ‖a‖₊
  证明: by
  refine iSup₂_le fun k hk => ?_
  exact mod_cast norm_le_norm_of_mem hk

Depends on / 依赖: mod_cast, norm_le_norm_of_mem
-/
theorem spectralRadius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a <= ‖a‖₊ := by
  refine iSup₂_le fun k hk => ?_
  exact mod_cast norm_le_norm_of_mem hk

/--
theorem `exists_nnnorm_eq_spectralRadius_of_nonempty` / 定理 `exists_nnnorm_eq_spectralRadius_of_nonempty`

English:
theorem exists_nnnorm_eq_spectralRadius_of_nonempty
  given: [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty)
  proof: by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact a).exists_isMaxOn ha continuous_nnnorm.continuousOn
  exact ⟨k, hk, le_antisymm (le_iSup₂ (α := Real>=0∞) k hk) (iSup₂_le <| mod_cast h)⟩

中文:
定理 存在_nnnorm_eq_spectralRadius_of_nonempty
  条件: [真空间 𝕜] {a : A} (ha : (σ a).非空)
  证明: by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact a).exists_isMaxOn ha continuous_nnnorm.continuousOn
  exact ⟨k, hk, le_antisymm (le_iSup₂ (α := Real>=0∞) k hk) (iSup₂_le <| mod_cast h)⟩

Depends on / 依赖: continuousOn, continuous_nnnorm, continuous_nnnorm.continuousOn, exists_isMaxOn, isCompact, le_antisymm, mod_cast, spectrum, spectrum.isCompact
-/
theorem exists_nnnorm_eq_spectralRadius_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty) :
    exists k in σ a, (‖k‖₊ : Real>=0∞) = spectralRadius 𝕜 a := by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact a).exists_isMaxOn ha continuous_nnnorm.continuousOn
  exact ⟨k, hk, le_antisymm (le_iSup₂ (α := Real>=0∞) k hk) (iSup₂_le <| mod_cast h)⟩

/--
theorem `spectralRadius_lt_of_forall_lt_of_nonempty` / 定理 `spectralRadius_lt_of_forall_lt_of_nonempty`

English:
theorem spectralRadius_lt_of_forall_lt_of_nonempty
  statement: [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty)
  proof: sSup_image.symm.trans_lt ((spectrum.isCompact a).sSup_lt_iff_of_continuous ha
    continuous_enorm.continuousOn (r : Real>=0∞)).mpr (by simpa using hr)

中文:
定理 spectralRadius_lt_of_对任意_lt_of_nonempty
  结论: [真空间 𝕜] {a : A} (ha : (σ a).非空)
  证明: sSup_image.symm.trans_lt ((spectrum.isCompact a).sSup_lt_iff_of_continuous ha
    continuous_enorm.continuousOn (r : Real>=0∞)).mpr (by simpa using hr)

Depends on / 依赖: continuousOn, continuous_enorm, continuous_enorm.continuousOn, isCompact, sSup_image, sSup_image.symm.trans_lt, sSup_lt_iff_of_continuous, spectrum, spectrum.isCompact, trans_lt
-/
theorem spectralRadius_lt_of_forall_lt_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty)
    {r : Real>=0} (hr : forall k in σ a, ‖k‖₊ < r) : spectralRadius 𝕜 a < r :=
sSup_image.symm.trans_lt ((spectrum.isCompact a).sSup_lt_iff_of_continuous ha
    continuous_enorm.continuousOn (r : Real>=0∞)).mpr (by simpa using hr)

open ENNReal Polynomial

variable (𝕜)

/--
theorem `spectralRadius_le_pow_nnnorm_pow_one_div` / 定理 `spectralRadius_le_pow_nnnorm_pow_one_div`

English:
theorem spectralRadius_le_pow_nnnorm_pow_one_div
  given: (a : A) (n : Nat)
  proof: by
  refine iSup₂_le fun k hk => ?_
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) in σ (a ^ (n + 1)) := by
    simpa only [one_mul, Algebra.algebraMap_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (@monomial 𝕜 _ (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have nnnorm_pow_le : (↑(‖k‖₊ ^ (n + 1)) : Real>=0∞) <= ‖a ^ (n + 1)‖₊ * ‖(1 : A)‖₊ := by
    simpa only [Real.toNNReal_mul (norm_nonneg _), norm_toNNReal, nnnorm_pow k (n + 1),
      ENNReal.coe_mul] using coe_mono (Real.toNNReal_mono (norm_le_norm_mul_of_mem pow_mem))
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < ((n + 1 : Nat) : Real) := mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le
  all_goals dsimp
  · rw [one_div, pow_rpow_inv_natCast]
    positivity
  rw [Nat.cast_succ]; rw [ENNReal.coe_mul_rpow]

中文:
定理 spectralRadius_le_pow_nnnorm_pow_one_div
  条件: (a : A) (n : 自然数)
  证明: by
  refine iSup₂_le fun k hk => ?_
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) in σ (a ^ (n + 1)) := by
    simpa only [one_mul, Algebra.algebraMap_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (@monomial 𝕜 _ (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have nnnorm_pow_le : (↑(‖k‖₊ ^ (n + 1)) : Real>=0∞) <= ‖a ^ (n + 1)‖₊ * ‖(1 : A)‖₊ := by
    simpa only [Real.toNNReal_mul (norm_nonneg _), norm_toNNReal, nnnorm_pow k (n + 1),
      ENNReal.coe_mul] using coe_mono (Real.toNNReal_mono (norm_le_norm_mul_of_mem pow_mem))
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < ((n + 1 : Nat) : Real) := mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le
  all_goals dsimp
  · rw [one_div, pow_rpow_inv_natCast]
    positivity
  rw [Nat.cast_succ]; rw [ENNReal.coe_mul_rpow]
-/
theorem spectralRadius_le_pow_nnnorm_pow_one_div (a : A) (n : Nat) :
    spectralRadius 𝕜 a <= (‖a ^ (n + 1)‖₊ : Real>=0∞) ^ (1 / (n + 1) : Real) *
      (‖(1 : A)‖₊ : Real>=0∞) ^ (1 / (n + 1) : Real) := by
  refine iSup₂_le fun k hk => ?_
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) in σ (a ^ (n + 1)) := by
    simpa only [one_mul, Algebra.algebraMap_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (@monomial 𝕜 _ (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have nnnorm_pow_le : (↑(‖k‖₊ ^ (n + 1)) : Real>=0∞) <= ‖a ^ (n + 1)‖₊ * ‖(1 : A)‖₊ := by
    simpa only [Real.toNNReal_mul (norm_nonneg _), norm_toNNReal, nnnorm_pow k (n + 1),
      ENNReal.coe_mul] using coe_mono (Real.toNNReal_mono (norm_le_norm_mul_of_mem pow_mem))
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < ((n + 1 : Nat) : Real) := mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le
  all_goals dsimp
  · rw [one_div, pow_rpow_inv_natCast]
    positivity
  rw [Nat.cast_succ]; rw [ENNReal.coe_mul_rpow]

/--
theorem `spectralRadius_le_liminf_pow_nnnorm_pow_one_div` / 定理 `spectralRadius_le_liminf_pow_nnnorm_pow_one_div`

English:
theorem spectralRadius_le_liminf_pow_nnnorm_pow_one_div
  given: (a : A)
  proof: by
  refine ENNReal.le_of_forall_lt_one_mul_le fun ε hε => ?_
  by_cases h : ε = 0
  · simp [h]
  simp only [ENNReal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_iSup_iInf_of_nat', ENNReal.iSup_mul]
  conv_rhs => arg 1; intro i; rw [ENNReal.iInf_mul (by simp [h])]
  rw [← ENNReal.inv_lt_inv]; rw [inv_one] at hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ENNReal.eventually_pow_one_div_le (ENNReal.coe_ne_top : ↑‖(1 : A)‖₊ != ∞) hε)
  refine le_trans ?_ (le_iSup _ (N + 1))
  refine le_iInf fun n => ?_
  simp only [← add_assoc]
  refine (spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans ?_
  norm_cast
  grw [hN (n + N + 1) (by lia)]

中文:
定理 spectralRadius_le_liminf_pow_nnnorm_pow_one_div
  条件: (a : A)
  证明: by
  refine ENNReal.le_of_forall_lt_one_mul_le fun ε hε => ?_
  by_cases h : ε = 0
  · simp [h]
  simp only [ENNReal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_iSup_iInf_of_nat', ENNReal.iSup_mul]
  conv_rhs => arg 1; intro i; rw [ENNReal.iInf_mul (by simp [h])]
  rw [← ENNReal.inv_lt_inv]; rw [inv_one] at hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ENNReal.eventually_pow_one_div_le (ENNReal.coe_ne_top : ↑‖(1 : A)‖₊ != ∞) hε)
  refine le_trans ?_ (le_iSup _ (N + 1))
  refine le_iInf fun n => ?_
  simp only [← add_assoc]
  refine (spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans ?_
  norm_cast
  grw [hN (n + N + 1) (by lia)]

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.eventually_pow_one_div_le, ENNReal.iInf_mul, ENNReal.iSup_mul, ENNReal.inv_lt_inv, ENNReal.le_of_forall_lt_one_mul_le, ENNReal.mul_le_iff_le_inv, coe_ne_top, conv_rhs, eventually_atTop, eventually_atTop.mp, eventually_pow_one_div_le, iInf_mul, iSup_mul, inv_lt_inv, inv_one, le_iInf, le_iSup, le_of_forall_lt_one_mul_le
-/
theorem spectralRadius_le_liminf_pow_nnnorm_pow_one_div (a : A) :
    spectralRadius 𝕜 a <= atTop.liminf fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real) := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun ε hε => ?_
  by_cases h : ε = 0
  · simp [h]
  simp only [ENNReal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_iSup_iInf_of_nat', ENNReal.iSup_mul]
  conv_rhs => arg 1; intro i; rw [ENNReal.iInf_mul (by simp [h])]
  rw [← ENNReal.inv_lt_inv]; rw [inv_one] at hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ENNReal.eventually_pow_one_div_le (ENNReal.coe_ne_top : ↑‖(1 : A)‖₊ != ∞) hε)
  refine le_trans ?_ (le_iSup _ (N + 1))
  refine le_iInf fun n => ?_
  simp only [← add_assoc]
  refine (spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans ?_
  norm_cast
  grw [hN (n + N + 1) (by lia)]

end SpectrumCompact

section resolvent

open Filter Asymptotics Bornology Topology

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

/--
theorem `eventually_isUnit_resolvent` / 定理 `eventually_isUnit_resolvent`

English:
theorem eventually_isUnit_resolvent
  given: (a : A)
  statement: forallᶠ z in cobounded 𝕜, IsUnit (resolvent a z)
  proof: by
  rw [atTop_basis_Ioi.cobounded_of_norm.eventually_iff]
  exact ⟨‖a‖ * ‖(1 : A)‖, trivial, fun _ => isUnit_resolvent.mp ∘ mem_resolventSet_of_norm_lt_mul⟩

中文:
定理 eventually_isUnit_resolvent
  条件: (a : A)
  结论: 对任意ᶠ z in cobounded 𝕜, 是单位 (resolvent a z)
  证明: by
  rw [atTop_basis_Ioi.cobounded_of_norm.eventually_iff]
  exact ⟨‖a‖ * ‖(1 : A)‖, trivial, fun _ => isUnit_resolvent.mp ∘ mem_resolventSet_of_norm_lt_mul⟩

Depends on / 依赖: atTop_basis_Ioi, atTop_basis_Ioi.cobounded_of_norm.eventually_iff, cobounded_of_norm, eventually_iff, isUnit_resolvent, isUnit_resolvent.mp, mem_resolventSet_of_norm_lt_mul
-/
theorem eventually_isUnit_resolvent (a : A) : forallᶠ z in cobounded 𝕜, IsUnit (resolvent a z) := by
  rw [atTop_basis_Ioi.cobounded_of_norm.eventually_iff]
  exact ⟨‖a‖ * ‖(1 : A)‖, trivial, fun _ => isUnit_resolvent.mp ∘ mem_resolventSet_of_norm_lt_mul⟩

/--
theorem `resolvent_isBigO_inv` / 定理 `resolvent_isBigO_inv`

English:
theorem resolvent_isBigO_inv
  given: (a : A)
  statement: resolvent a =O[cobounded 𝕜] Inv.inv
  proof: have h : (fun z => resolvent (z⁻¹ • a) (1 : 𝕜)) =O[cobounded 𝕜] (fun _ => (1 : Real)) := by
    simpa [Function.comp_def, resolvent] using
      (NormedRing.inverse_one_sub_norm (R := A)).comp_tendsto
        (by simpa using (tendsto_inv₀_cobounded (α := 𝕜)).smul_const a)
  calc
    resolvent a =ᶠ[cobounded 𝕜] fun z => z⁻¹ • resolvent (z⁻¹ • a) (1 : 𝕜) := by
      filter_upwards [isBounded_singleton (x := 0)] with z hz
      lift z to 𝕜ˣ using Ne.isUnit hz
      simpa [Units.smul_def] using congr(z⁻¹ • $(units_smul_resolvent_self (r := z) (a := a)))
_ =O[cobounded 𝕜] (· ⁻¹) := .of_norm_right by
      simpa using (isBigO_refl (· ⁻¹) (cobounded 𝕜)).norm_right.smul h

中文:
定理 resolvent_isBigO_inv
  条件: (a : A)
  结论: resolvent a =O[cobounded 𝕜] 取逆.inv
  证明: have h : (fun z => resolvent (z⁻¹ • a) (1 : 𝕜)) =O[cobounded 𝕜] (fun _ => (1 : Real)) := by
    simpa [Function.comp_def, resolvent] using
      (NormedRing.inverse_one_sub_norm (R := A)).comp_tendsto
        (by simpa using (tendsto_inv₀_cobounded (α := 𝕜)).smul_const a)
  calc
    resolvent a =ᶠ[cobounded 𝕜] fun z => z⁻¹ • resolvent (z⁻¹ • a) (1 : 𝕜) := by
      filter_upwards [isBounded_singleton (x := 0)] with z hz
      lift z to 𝕜ˣ using Ne.isUnit hz
      simpa [Units.smul_def] using congr(z⁻¹ • $(units_smul_resolvent_self (r := z) (a := a)))
_ =O[cobounded 𝕜] (· ⁻¹) := .of_norm_right by
      simpa using (isBigO_refl (· ⁻¹) (cobounded 𝕜)).norm_right.smul h

Depends on / 依赖: Function, Function.comp_def, Ne.isUnit, NormedRing, NormedRing.inverse_one_sub_norm, Units.smul_def, cobounded, comp_def, comp_tendsto, filter_upwards, inverse_one_sub_norm, isBounded_singleton, isUnit, resolvent, smul_const, smul_def, units_smul_resolvent_self
-/
theorem resolvent_isBigO_inv (a : A) : resolvent a =O[cobounded 𝕜] Inv.inv :=
  have h : (fun z => resolvent (z⁻¹ • a) (1 : 𝕜)) =O[cobounded 𝕜] (fun _ => (1 : Real)) := by
    simpa [Function.comp_def, resolvent] using
      (NormedRing.inverse_one_sub_norm (R := A)).comp_tendsto
        (by simpa using (tendsto_inv₀_cobounded (α := 𝕜)).smul_const a)
  calc
    resolvent a =ᶠ[cobounded 𝕜] fun z => z⁻¹ • resolvent (z⁻¹ • a) (1 : 𝕜) := by
      filter_upwards [isBounded_singleton (x := 0)] with z hz
      lift z to 𝕜ˣ using Ne.isUnit hz
      simpa [Units.smul_def] using congr(z⁻¹ • $(units_smul_resolvent_self (r := z) (a := a)))
_ =O[cobounded 𝕜] (· ⁻¹) := .of_norm_right by
      simpa using (isBigO_refl (· ⁻¹) (cobounded 𝕜)).norm_right.smul h

/--
theorem `resolvent_tendsto_cobounded` / 定理 `resolvent_tendsto_cobounded`

English:
theorem resolvent_tendsto_cobounded
  given: (a : A)
  statement: Tendsto (resolvent a) (cobounded 𝕜) (𝓝 0)
  proof: .trans_tendsto tendsto_inv₀_cobounded resolvent_isBigO_inv a

中文:
定理 resolvent_tendsto_cobounded
  条件: (a : A)
  结论: 收敛 (resolvent a) (cobounded 𝕜) (𝓝 0)
  证明: .trans_tendsto tendsto_inv₀_cobounded resolvent_isBigO_inv a

Depends on / 依赖: resolvent_isBigO_inv, trans_tendsto
-/
theorem resolvent_tendsto_cobounded (a : A) : Tendsto (resolvent a) (cobounded 𝕜) (𝓝 0) :=
.trans_tendsto tendsto_inv₀_cobounded resolvent_isBigO_inv a

end resolvent

section OneSubSMul

open ContinuousMultilinearMap ENNReal FormalMultilinearSeries

open scoped NNReal ENNReal

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable (𝕜) in
/--
theorem `hasFPowerSeriesOnBall_inverse_one_sub_smul` / 定理 `hasFPowerSeriesOnBall_inverse_one_sub_smul`

English:
theorem hasFPowerSeriesOnBall_inverse_one_sub_smul
  given: [HasSummableGeomSeries A] (a : A)
  proof: { r_le := by
      refine le_of_forall_nnreal_lt fun r hr =>
        le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => ?_
      rw [← norm_toNNReal]; rw [norm_mkPiRing]; rw [norm_toNNReal]
      rcases n with - | n
      · simp
      · grw [nnnorm_pow_le' a n.succ_pos, ← le_max_left]
        by_cases h : ‖a‖₊ = 0
        · simp [h, pow_succ']
        · rw [← coe_inv h, coe_lt_coe, NNReal.lt_inv_iff_mul_lt h] at hr
          simpa only [← mul_pow, mul_comm] using! pow_le_one' hr.le n.succ
    r_pos := ENNReal.inv_pos.mpr coe_ne_top
    hasSum := fun {y} hy => by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.eball_coe] using! hy
          rwa [← coe_nnnorm, ← Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_one, nnnorm_smul,
            ← NNReal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (summable_geometric_of_norm_lt_one norm_lt).hasSum_iff] using!
        (NormedRing.inverse_one_sub _ norm_lt).symm }

中文:
定理 hasFPowerSeriesOnBall_inverse_one_sub_smul
  条件: [有SummableGeomSeries A] (a : A)
  证明: { r_le := by
      refine le_of_forall_nnreal_lt fun r hr =>
        le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => ?_
      rw [← norm_toNNReal]; rw [norm_mkPiRing]; rw [norm_toNNReal]
      rcases n with - | n
      · simp
      · grw [nnnorm_pow_le' a n.succ_pos, ← le_max_left]
        by_cases h : ‖a‖₊ = 0
        · simp [h, pow_succ']
        · rw [← coe_inv h, coe_lt_coe, NNReal.lt_inv_iff_mul_lt h] at hr
          simpa only [← mul_pow, mul_comm] using! pow_le_one' hr.le n.succ
    r_pos := ENNReal.inv_pos.mpr coe_ne_top
    hasSum := fun {y} hy => by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.eball_coe] using! hy
          rwa [← coe_nnnorm, ← Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_one, nnnorm_smul,
            ← NNReal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (summable_geometric_of_norm_lt_one norm_lt).hasSum_iff] using!
        (NormedRing.inverse_one_sub _ norm_lt).symm }

Depends on / 依赖: ENNReal, ENNReal.inv_pos.mpr, NNReal, NNReal.lt_inv_iff_mul_lt, coe_inv, coe_lt_coe, coe_ne_top, hasSum, hr.le, inv_pos, le_max_left, le_of_forall_nnreal_lt, le_radius_of_bound_nnreal, lt_inv_iff_mul_lt, mul_comm, mul_pow, n.succ, n.succ_pos, nnnorm_pow_le, norm_mkPiRing
-/
theorem hasFPowerSeriesOnBall_inverse_one_sub_smul [HasSummableGeomSeries A] (a : A) :
    HasFPowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) 0 ‖a‖₊⁻¹ :=
  { r_le := by
      refine le_of_forall_nnreal_lt fun r hr =>
        le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => ?_
      rw [← norm_toNNReal]; rw [norm_mkPiRing]; rw [norm_toNNReal]
      rcases n with - | n
      · simp
      · grw [nnnorm_pow_le' a n.succ_pos, ← le_max_left]
        by_cases h : ‖a‖₊ = 0
        · simp [h, pow_succ']
        · rw [← coe_inv h, coe_lt_coe, NNReal.lt_inv_iff_mul_lt h] at hr
          simpa only [← mul_pow, mul_comm] using! pow_le_one' hr.le n.succ
    r_pos := ENNReal.inv_pos.mpr coe_ne_top
    hasSum := fun {y} hy => by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.eball_coe] using! hy
          rwa [← coe_nnnorm, ← Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_one, nnnorm_smul,
            ← NNReal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (summable_geometric_of_norm_lt_one norm_lt).hasSum_iff] using!
        (NormedRing.inverse_one_sub _ norm_lt).symm }

/--
theorem `isUnit_one_sub_smul_of_lt_inv_radius` / 定理 `isUnit_one_sub_smul_of_lt_inv_radius`

English:
theorem isUnit_one_sub_smul_of_lt_inv_radius
  given: {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹)
  proof: by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • (1 : A) - a) by
      rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu
    rw [Units.smul_def]; rw [← Algebra.algebraMap_eq_smul_one]; rw [← mem_resolventSet_iff]
    refine mem_resolventSet_of_spectralRadius_lt ?_
    rwa [Units.val_inv_eq_inv_val, nnnorm_inv,
      coe_inv (nnnorm_ne_zero_iff.mpr (Units.val_mk0 hz ▸ hz : (u : 𝕜) != 0)), lt_inv_iff_lt_inv]

中文:
定理 isUnit_one_sub_smul_of_lt_inv_radius
  条件: {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹)
  证明: by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • (1 : A) - a) by
      rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu
    rw [Units.smul_def]; rw [← Algebra.algebraMap_eq_smul_one]; rw [← mem_resolventSet_iff]
    refine mem_resolventSet_of_spectralRadius_lt ?_
    rwa [Units.val_inv_eq_inv_val, nnnorm_inv,
      coe_inv (nnnorm_ne_zero_iff.mpr (Units.val_mk0 hz ▸ hz : (u : 𝕜) != 0)), lt_inv_iff_lt_inv]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsUnit, IsUnit.smul_sub_iff_sub_inv_smul, Units.mk0, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, algebraMap_eq_smul_one, coe_inv, inv_inv, isUnit_one, lt_inv_iff_lt_inv, mem_resolventSet_iff, mem_resolventSet_of_spectralRadius_lt, nnnorm_inv, nnnorm_ne_zero_iff, nnnorm_ne_zero_iff.mpr, smul_def, smul_sub_iff_sub_inv_smul
-/
theorem isUnit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • (1 : A) - a) by
      rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu
    rw [Units.smul_def]; rw [← Algebra.algebraMap_eq_smul_one]; rw [← mem_resolventSet_iff]
    refine mem_resolventSet_of_spectralRadius_lt ?_
    rwa [Units.val_inv_eq_inv_val, nnnorm_inv,
      coe_inv (nnnorm_ne_zero_iff.mpr (Units.val_mk0 hz ▸ hz : (u : 𝕜) != 0)), lt_inv_iff_lt_inv]

end OneSubSMul


section ExpMapping

local notation "↑ₐ" => algebraMap 𝕜 A

/--
theorem `exp_mem_exp` / 定理 `exp_mem_exp`

English:
theorem exp_mem_exp
  statement: [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  proof: by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat 𝕜 A
  have hexpmul : exp a = exp (a - ↑ₐ z) * ↑ₐ (exp z) := by
    rw [algebraMap_exp_comm z]; rw [← exp_add_of_commute (Algebra.commutes z (a - ↑ₐ z)).symm]; rw [sub_add_cancel]
  let b := ∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : Nat => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖a - ↑ₐ z‖) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul]; rw [mul_comm]; rw [norm_inv]; rw [RCLike.norm_natCast]; rw [← div_eq_mul_inv]
    gcongr
    · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
    · exact n.le_succ
  have h₀ : (∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [mul_smul_comm, pow_succ'] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [pow_succ, Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum 𝕜]
    convert! (expSeries_summable' (𝕂 := 𝕜) (a - ↑ₐ z)).tsum_eq_zero_add
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    · exact h₀.symm
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [← one_mul (↑ₐ (exp z))]; rw [hexpmul]; rw [← _root_.sub_mul]; rw [Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - ↑ₐ z) - 1)).symm]; rw [sub_eq_iff_eq_add'.mpr h₃]; rw [Commute.isUnit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

中文:
定理 exp_mem_exp
  结论: [RCLike 𝕜] [赋范环 A] [赋范代数 𝕜 A] [完备空间 A]
  证明: by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat 𝕜 A
  have hexpmul : exp a = exp (a - ↑ₐ z) * ↑ₐ (exp z) := by
    rw [algebraMap_exp_comm z]; rw [← exp_add_of_commute (Algebra.commutes z (a - ↑ₐ z)).symm]; rw [sub_add_cancel]
  let b := ∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : Nat => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖a - ↑ₐ z‖) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul]; rw [mul_comm]; rw [norm_inv]; rw [RCLike.norm_natCast]; rw [← div_eq_mul_inv]
    gcongr
    · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
    · exact n.le_succ
  have h₀ : (∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [mul_smul_comm, pow_succ'] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [pow_succ, Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum 𝕜]
    convert! (expSeries_summable' (𝕂 := 𝕜) (a - ↑ₐ z)).tsum_eq_zero_add
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    · exact h₀.symm
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [← one_mul (↑ₐ (exp z))]; rw [hexpmul]; rw [← _root_.sub_mul]; rw [Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - ↑ₐ z) - 1)).symm]; rw [sub_eq_iff_eq_add'.mpr h₃]; rw [Commute.isUnit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

Depends on / 依赖: Algebra, Algebra.commutes, Filter, Filter.eventually_co, NormedAlgebra, Real.summable_pow_div_factorial, Summable, algebraMap_exp_comm, commutes, eventually_co, exp_add_of_commute, factorial, filter_upwards, hexpmul, nondep, of_norm_bounded_eventually, restrictScalars, sub_add_cancel, summable_pow_div_factorial
-/
theorem exp_mem_exp [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    (a : A) {z : 𝕜} (hz : z in spectrum 𝕜 a) : exp z in spectrum 𝕜 (exp a) := by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat 𝕜 A
  have hexpmul : exp a = exp (a - ↑ₐ z) * ↑ₐ (exp z) := by
    rw [algebraMap_exp_comm z]; rw [← exp_add_of_commute (Algebra.commutes z (a - ↑ₐ z)).symm]; rw [sub_add_cancel]
  let b := ∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : Nat => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖a - ↑ₐ z‖) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul]; rw [mul_comm]; rw [norm_inv]; rw [RCLike.norm_natCast]; rw [← div_eq_mul_inv]
    gcongr
    · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
    · exact n.le_succ
  have h₀ : (∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [mul_smul_comm, pow_succ'] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : Nat, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [pow_succ, Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum 𝕜]
    convert! (expSeries_summable' (𝕂 := 𝕜) (a - ↑ₐ z)).tsum_eq_zero_add
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    · exact h₀.symm
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [← one_mul (↑ₐ (exp z))]; rw [hexpmul]; rw [← _root_.sub_mul]; rw [Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - ↑ₐ z) - 1)).symm]; rw [sub_eq_iff_eq_add'.mpr h₃]; rw [Commute.isUnit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

end ExpMapping

end spectrum

namespace AlgHom

section NormedField

variable {F : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

instance (priority := 100) [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] :
    ContinuousLinearMapClass F 𝕜 A 𝕜 :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ ‖(1 : A)‖ fun a =>
        mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ _) }

/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: (φ : A ->ₐ[𝕜] 𝕜)
  body: { φ.toLinearMap with }

@[simp]

中文:
定义 toContinuousLinearMap
  签名: (φ : A ->ₐ[𝕜] 𝕜)
  定义体: { φ.toLinearMap with }

@[simp]

Depends on / 依赖: toLinearMap
-/
def toContinuousLinearMap (φ : A ->ₐ[𝕜] 𝕜) : StrongDual 𝕜 A :=
  { φ.toLinearMap with }

@[simp]
/--
theorem `coe_toContinuousLinearMap` / 定理 `coe_toContinuousLinearMap`

English:
theorem coe_toContinuousLinearMap
  given: (φ : A ->ₐ[𝕜] 𝕜)
  statement: ⇑φ.toContinuousLinearMap = φ
  proof: rfl

中文:
定理 coe_toContinuousLinearMap
  条件: (φ : A ->ₐ[𝕜] 𝕜)
  结论: ⇑φ.toContinuousLinearMap = φ
  证明: rfl
-/
theorem coe_toContinuousLinearMap (φ : A ->ₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ :=
  rfl

/--
theorem `norm_apply_le_self_mul_norm_one` / 定理 `norm_apply_le_self_mul_norm_one`

English:
theorem norm_apply_le_self_mul_norm_one
  given: [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A)
  proof: spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)

中文:
定理 norm_apply_le_self_mul_norm_one
  条件: [函数状 F A 𝕜] [代数态射类 F 𝕜 A 𝕜] (f : F) (a : A)
  证明: spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)

Depends on / 依赖: apply_mem_spectrum, norm_le_norm_mul_of_mem, spectrum, spectrum.norm_le_norm_mul_of_mem
-/
theorem norm_apply_le_self_mul_norm_one [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A) :
    ‖f a‖ <= ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)

/--
theorem `norm_apply_le_self` / 定理 `norm_apply_le_self`

English:
theorem norm_apply_le_self
  statement: [NormOneClass A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]
  proof: spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)

中文:
定理 norm_apply_le_self
  结论: [NormOne类 A] [函数状 F A 𝕜] [代数态射类 F 𝕜 A 𝕜]
  证明: spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)

Depends on / 依赖: apply_mem_spectrum, norm_le_norm_of_mem, spectrum, spectrum.norm_le_norm_of_mem
-/
theorem norm_apply_le_self [NormOneClass A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]
    (f : F) (a : A) : ‖f a‖ <= ‖a‖ :=
  spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
/--
theorem `toContinuousLinearMap_norm` / 定理 `toContinuousLinearMap_norm`

English:
theorem toContinuousLinearMap_norm
  given: [NormOneClass A] (φ : A ->ₐ[𝕜] 𝕜)
  proof: ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one
    (fun a => (one_mul ‖a‖).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
    fun _ _ h => by simpa only [coe_toContinuousLinearMap, map_one, norm_one, mul_one] using h 1

中文:
定理 toContinuousLinearMap_norm
  条件: [NormOne类 A] (φ : A ->ₐ[𝕜] 𝕜)
  证明: ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one
    (fun a => (one_mul ‖a‖).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
    fun _ _ h => by simpa only [coe_toContinuousLinearMap, map_one, norm_one, mul_one] using h 1

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_eq_of_bounds, apply_mem_spectrum, coe_toContinuousLinearMap, map_one, mul_one, norm_le_norm_of_mem, norm_one, one_mul, opNorm_eq_of_bounds, spectrum, spectrum.norm_le_norm_of_mem, zero_le_one
-/
theorem toContinuousLinearMap_norm [NormOneClass A] (φ : A ->ₐ[𝕜] 𝕜) :
    ‖φ.toContinuousLinearMap‖ = 1 :=
  ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one
    (fun a => (one_mul ‖a‖).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
    fun _ _ h => by simpa only [coe_toContinuousLinearMap, map_one, norm_one, mul_one] using h 1

end NontriviallyNormedField

end AlgHom

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [CompleteSpace A]
variable [NormedAlgebra 𝕜 A]

/--
Definition of `equivAlgHom` / `equivAlgHom` 的定义

English:
definition equivAlgHom
  signature: : characterSpace 𝕜 A ≃ (A ->ₐ[𝕜] 𝕜) where
  body: toAlgHom
  invFun f :=
    { val := f.toContinuousLinearMap
      property := by rw [eq_set_map_one_map_mul]; exact ⟨map_one f, map_mul f⟩ }

@[simp]

中文:
定义 equivAlgHom
  签名: : characterSpace 𝕜 A ≃ (A ->ₐ[𝕜] 𝕜) where
  定义体: toAlgHom
  invFun f :=
    { val := f.toContinuousLinearMap
      property := by rw [eq_set_map_one_map_mul]; exact ⟨map_one f, map_mul f⟩ }

@[simp]

Depends on / 依赖: toAlgHom
-/
noncomputable def equivAlgHom : characterSpace 𝕜 A ≃ (A ->ₐ[𝕜] 𝕜) where
  toFun := toAlgHom
  invFun f :=
    { val := f.toContinuousLinearMap
      property := by rw [eq_set_map_one_map_mul]; exact ⟨map_one f, map_mul f⟩ }

@[simp]
/--
theorem `equivAlgHom_coe` / 定理 `equivAlgHom_coe`

English:
theorem equivAlgHom_coe
  given: (f : characterSpace 𝕜 A)
  statement: ⇑(equivAlgHom f) = f
  proof: rfl

@[simp]

中文:
定理 equivAlgHom_coe
  条件: (f : characterSpace 𝕜 A)
  结论: ⇑(equivAlgHom f) = f
  证明: rfl

@[simp]
-/
theorem equivAlgHom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f :=
  rfl

@[simp]
/--
theorem `equivAlgHom_symm_coe` / 定理 `equivAlgHom_symm_coe`

English:
theorem equivAlgHom_symm_coe
  given: (f : A ->ₐ[𝕜] 𝕜)
  statement: ⇑(equivAlgHom.symm f) = f
  proof: rfl

中文:
定理 equivAlgHom_symm_coe
  条件: (f : A ->ₐ[𝕜] 𝕜)
  结论: ⇑(equivAlgHom.symm f) = f
  证明: rfl
-/
theorem equivAlgHom_symm_coe (f : A ->ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f :=
  rfl

end CharacterSpace

end WeakDual

section BoundarySpectrum

local notation "σ" => spectrum

variable {𝕜 A SA : Type*} [NormedRing A] [CompleteSpace A] [SetLike SA A] [SubringClass SA A]

open Topology Filter Set

section NormedField

variable [NormedField 𝕜] [NormedAlgebra 𝕜 A] [instSMulMem : SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

set_option backward.isDefEq.respectTransparency.types false in
open SubalgebraClass in
include instSMulMem in
/--
lemma `_root_.Subalgebra.isUnit_of_isUnit_val_of_eventually` / 引理 `_root_.Subalgebra.isUnit_of_isUnit_val_of_eventually`

English:
lemma _root_.Subalgebra.isUnit_of_isUnit_val_of_eventually
  statement: {l : Filter S} {a : S}
  proof: by
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑ha.unit⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
exact (NormedRing.inverse_continuousAt _).tendsto.comp
continuousAt_subtype_val.tendsto.comp map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) in S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mono fun x hx => ?_
  suffices Ring.inverse (val S x) = (val S ↑hx.unit⁻¹) from this ▸ Subtype.property _
  rw [← (hx.map (val S)).unit_spec]; rw [Ring.inverse_unit (hx.map (val S)).unit]; rw [val]
  apply Units.mul_eq_one_iff_inv_eq.mp
  simpa [-IsUnit.mul_val_inv] using congr(($hx.mul_val_inv : A))

中文:
引理 _root_.子代数.isUnit_of_isUnit_val_of_eventually
  结论: {l : 滤子 S} {a : S}
  证明: by
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑ha.unit⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
exact (NormedRing.inverse_continuousAt _).tendsto.comp
continuousAt_subtype_val.tendsto.comp map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) in S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mono fun x hx => ?_
  suffices Ring.inverse (val S x) = (val S ↑hx.unit⁻¹) from this ▸ Subtype.property _
  rw [← (hx.map (val S)).unit_spec]; rw [Ring.inverse_unit (hx.map (val S)).unit]; rw [val]
  apply Units.mul_eq_one_iff_inv_eq.mp
  simpa [-IsUnit.mul_val_inv] using congr(($hx.mul_val_inv : A))

Depends on / 依赖: Filter, Filter.eventually_map, NormedRing, NormedRing.inverse_continuousAt, Ring.inverse, Ring.inverse_unit, Subtype, Subtype.property, Tendsto, all_goals, continuousAt_subtype_val, continuousAt_subtype_val.tendsto.comp, eventually_map, hS.mem_of_tendsto, ha.unit, hl.mono, hx.unit, inverse, inverse_continuousAt, inverse_unit
-/
lemma _root_.Subalgebra.isUnit_of_isUnit_val_of_eventually {l : Filter S} {a : S}
    (ha : IsUnit (a : A)) (hla : l <= 𝓝 a) (hl : forallᶠ x in l, IsUnit x) (hl' : l.NeBot) :
    IsUnit a := by
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑ha.unit⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
exact (NormedRing.inverse_continuousAt _).tendsto.comp
continuousAt_subtype_val.tendsto.comp map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) in S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mono fun x hx => ?_
  suffices Ring.inverse (val S x) = (val S ↑hx.unit⁻¹) from this ▸ Subtype.property _
  rw [← (hx.map (val S)).unit_spec]; rw [Ring.inverse_unit (hx.map (val S)).unit]; rw [val]
  apply Units.mul_eq_one_iff_inv_eq.mp
  simpa [-IsUnit.mul_val_inv] using congr(($hx.mul_val_inv : A))

/--
lemma `_root_.Subalgebra.frontier_spectrum` / 引理 `_root_.Subalgebra.frontier_spectrum`

English:
lemma _root_.Subalgebra.frontier_spectrum
  statement: frontier (σ 𝕜 x) subseteq σ 𝕜 (x : A)
  proof: by
  have : CompleteSpace S := hS.completeSpace_coe
  intro μ hμ
  by_contra h
  rw [spectrum.notMem_iff] at h
  rw [← frontier_compl]; rw [(spectrum.isClosed _).isOpen_compl.frontier_eq]; rw [Set.mem_sdiff] at hμ
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff]; rw [spectrum.notMem_iff]
refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ .map hμ₁ (algebraMap 𝕜 S · - x)
  · calc
      _ <= map _ (𝓝 μ) := map_mono (by simp)
      _ <= _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.notMem_iff]

中文:
引理 _root_.子代数.frontier_spectrum
  结论: frontier (σ 𝕜 x) subseteq σ 𝕜 (x : A)
  证明: by
  have : CompleteSpace S := hS.completeSpace_coe
  intro μ hμ
  by_contra h
  rw [spectrum.notMem_iff] at h
  rw [← frontier_compl]; rw [(spectrum.isClosed _).isOpen_compl.frontier_eq]; rw [Set.mem_sdiff] at hμ
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff]; rw [spectrum.notMem_iff]
refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ .map hμ₁ (algebraMap 𝕜 S · - x)
  · calc
      _ <= map _ (𝓝 μ) := map_mono (by simp)
      _ <= _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.notMem_iff]

Depends on / 依赖: CompleteSpace, Filter, Filter.Tendsto, Set.mem_sdiff, Subalgebra, Subalgebra.isUnit_of_isUnit_val_of_eventually, Tendsto, algebraMap, completeSpace_coe, frontier_compl, frontier_eq, hS.completeSpace_coe, isClosed, isOpen_compl, isOpen_compl.frontier_eq, isUnit_of_isUnit_val_of_eventually, map_mono, mem_closure_iff_clusterPt, mem_compl_iff, mem_sdiff
-/
lemma _root_.Subalgebra.frontier_spectrum : frontier (σ 𝕜 x) subseteq σ 𝕜 (x : A) := by
  have : CompleteSpace S := hS.completeSpace_coe
  intro μ hμ
  by_contra h
  rw [spectrum.notMem_iff] at h
  rw [← frontier_compl]; rw [(spectrum.isClosed _).isOpen_compl.frontier_eq]; rw [Set.mem_sdiff] at hμ
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff]; rw [spectrum.notMem_iff]
refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ .map hμ₁ (algebraMap 𝕜 S · - x)
  · calc
      _ <= map _ (𝓝 μ) := map_mono (by simp)
      _ <= _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.notMem_iff]

/--
lemma `Subalgebra.frontier_subset_frontier` / 引理 `Subalgebra.frontier_subset_frontier`

English:
lemma Subalgebra.frontier_subset_frontier
  proof: by
  rw [frontier_eq_closure_inter_closure (s := σ 𝕜 (x : A))]; rw [(spectrum.isClosed (x : A)).closure_eq]
  apply subset_inter (frontier_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  grw [inter_subset_right, spectrum.subset_subalgebra]

中文:
引理 子代数.frontier_subset_frontier
  证明: by
  rw [frontier_eq_closure_inter_closure (s := σ 𝕜 (x : A))]; rw [(spectrum.isClosed (x : A)).closure_eq]
  apply subset_inter (frontier_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  grw [inter_subset_right, spectrum.subset_subalgebra]

Depends on / 依赖: closure_eq, frontier_eq_closure_inter_closure, frontier_spectrum, inter_subset_right, isClosed, spectrum, spectrum.isClosed, spectrum.subset_subalgebra, subset_inter, subset_subalgebra
-/
lemma Subalgebra.frontier_subset_frontier :
    frontier (σ 𝕜 x) subseteq frontier (σ 𝕜 (x : A)) := by
  rw [frontier_eq_closure_inter_closure (s := σ 𝕜 (x : A))]; rw [(spectrum.isClosed (x : A)).closure_eq]
  apply subset_inter (frontier_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  grw [inter_subset_right, spectrum.subset_subalgebra]

open Set Notation

/--
lemma `Subalgebra.spectrum_sUnion_connectedComponentIn` / 引理 `Subalgebra.spectrum_sUnion_connectedComponentIn`

English:
lemma Subalgebra.spectrum_sUnion_connectedComponentIn
  proof: by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓inter (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn (sdiff_subset_compl _ _)]; rw [union_sdiff_cancel (spectrum.subset_subalgebra x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq]; rw [closure_eq_interior_union_frontier]; rw [union_sdiff_distrib]; rw [sdiff_eq_empty.mpr (frontier_spectrum S x)]; rw [sdiff_eq_compl_inter]; rw [union_empty]
    exact (spectrum.isClosed _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) subseteq frontier (σ 𝕜 (x : A)) from
disjoint_of_subset_left h_frontier disjoint_compl_right.frontier_left
      (spectrum.isClosed _).isOpen_compl
  grw [sdiff_eq_compl_inter, frontier_inter_subset, inter_subset_left, inter_subset_right,
    frontier_compl, frontier_subset_frontier, union_self]

中文:
引理 子代数.spectrum_sUnion_connectedComponentIn
  证明: by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓inter (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn (sdiff_subset_compl _ _)]; rw [union_sdiff_cancel (spectrum.subset_subalgebra x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq]; rw [closure_eq_interior_union_frontier]; rw [union_sdiff_distrib]; rw [sdiff_eq_empty.mpr (frontier_spectrum S x)]; rw [sdiff_eq_compl_inter]; rw [union_empty]
    exact (spectrum.isClosed _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) subseteq frontier (σ 𝕜 (x : A)) from
disjoint_of_subset_left h_frontier disjoint_compl_right.frontier_left
      (spectrum.isClosed _).isOpen_compl
  grw [sdiff_eq_compl_inter, frontier_inter_subset, inter_subset_left, inter_subset_right,
    frontier_compl, frontier_subset_frontier, union_self]

Depends on / 依赖: CompleteSpace, IsClopen, IsOpen, biUnion_connectedComponentIn, closure_eq, closure_eq_interior_union_frontier, completeSpace_coe, frontier_spectrum, hS.completeSpace_coe, h_open, isClosed, sdiff_eq_compl_inter, sdiff_eq_empty, sdiff_eq_empty.mpr, sdiff_subset_compl, spectrum, spectrum.isClosed, spectrum.subset_subalgebra, subset_subalgebra, this.biUnion_connectedComponentIn
-/
lemma Subalgebra.spectrum_sUnion_connectedComponentIn :
    σ 𝕜 x = σ 𝕜 (x : A) union (⋃ z in (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓inter (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn (sdiff_subset_compl _ _)]; rw [union_sdiff_cancel (spectrum.subset_subalgebra x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq]; rw [closure_eq_interior_union_frontier]; rw [union_sdiff_distrib]; rw [sdiff_eq_empty.mpr (frontier_spectrum S x)]; rw [sdiff_eq_compl_inter]; rw [union_empty]
    exact (spectrum.isClosed _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) subseteq frontier (σ 𝕜 (x : A)) from
disjoint_of_subset_left h_frontier disjoint_compl_right.frontier_left
      (spectrum.isClosed _).isOpen_compl
  grw [sdiff_eq_compl_inter, frontier_inter_subset, inter_subset_left, inter_subset_right,
    frontier_compl, frontier_subset_frontier, union_self]

/--
lemma `Subalgebra.spectrum_isBounded_connectedComponentIn` / 引理 `Subalgebra.spectrum_isBounded_connectedComponentIn`

English:
lemma Subalgebra.spectrum_isBounded_connectedComponentIn
  given: {z : 𝕜} (hz : z in σ 𝕜 x)
  proof: by
  by_cases hz' : z in σ 𝕜 (x : A)
  · simp [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
  · have : CompleteSpace S := hS.completeSpace_coe
.subset this suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z subseteq σ 𝕜 x from spectrum.isBounded x
    rw [spectrum_sUnion_connectedComponentIn S]
.trans subset_union_right exact subset_biUnion_of_mem (mem_sdiff_of_mem hz hz')

中文:
引理 子代数.spectrum_isBounded_connectedComponentIn
  条件: {z : 𝕜} (hz : z in σ 𝕜 x)
  证明: by
  by_cases hz' : z in σ 𝕜 (x : A)
  · simp [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
  · have : CompleteSpace S := hS.completeSpace_coe
.subset this suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z subseteq σ 𝕜 x from spectrum.isBounded x
    rw [spectrum_sUnion_connectedComponentIn S]
.trans subset_union_right exact subset_biUnion_of_mem (mem_sdiff_of_mem hz hz')

Depends on / 依赖: CompleteSpace, completeSpace_coe, connectedComponentIn, connectedComponentIn_eq_empty, hS.completeSpace_coe, isBounded, mem_sdiff_of_mem, not_not, not_not.mpr, spectrum, spectrum.isBounded, spectrum_sUnion_connectedComponentIn, subset, subset_biUnion_of_mem, subset_union_right, subseteq
-/
lemma Subalgebra.spectrum_isBounded_connectedComponentIn {z : 𝕜} (hz : z in σ 𝕜 x) :
    Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  by_cases hz' : z in σ 𝕜 (x : A)
  · simp [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
  · have : CompleteSpace S := hS.completeSpace_coe
.subset this suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z subseteq σ 𝕜 x from spectrum.isBounded x
    rw [spectrum_sUnion_connectedComponentIn S]
.trans subset_union_right exact subset_biUnion_of_mem (mem_sdiff_of_mem hz hz')

end NormedField

variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A] [SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

/--
lemma `Subalgebra.spectrum_eq_of_isPreconnected_compl` / 引理 `Subalgebra.spectrum_eq_of_isPreconnected_compl`

English:
lemma Subalgebra.spectrum_eq_of_isPreconnected_compl
  given: (h : IsPreconnected (σ 𝕜 (x : A))ᶜ)
  proof: by
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_sUnion_connectedComponentIn]; rw [this]
    simp
  refine eq_empty_of_forall_notMem fun z hz => NormedSpace.unbounded_univ 𝕜 𝕜 ?_
.mp hz obtain ⟨hz, hz'⟩ := mem_sdiff _
have := (spectrum.isBounded (x : A)).union
    h.connectedComponentIn hz' ▸ spectrum_isBounded_connectedComponentIn S x hz
  simpa

中文:
引理 子代数.spectrum_eq_of_isPreconnected_compl
  条件: (h : 是预连通 (σ 𝕜 (x : A))ᶜ)
  证明: by
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_sUnion_connectedComponentIn]; rw [this]
    simp
  refine eq_empty_of_forall_notMem fun z hz => NormedSpace.unbounded_univ 𝕜 𝕜 ?_
.mp hz obtain ⟨hz, hz'⟩ := mem_sdiff _
have := (spectrum.isBounded (x : A)).union
    h.connectedComponentIn hz' ▸ spectrum_isBounded_connectedComponentIn S x hz
  simpa

Depends on / 依赖: NormedSpace, NormedSpace.unbounded_univ, connectedComponentIn, eq_empty_of_forall_notMem, h.connectedComponentIn, isBounded, mem_sdiff, spectrum, spectrum.isBounded, spectrum_isBounded_connectedComponentIn, spectrum_sUnion_connectedComponentIn, unbounded_univ
-/
lemma Subalgebra.spectrum_eq_of_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x : A))ᶜ) :
    σ 𝕜 x = σ 𝕜 (x : A) := by
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_sUnion_connectedComponentIn]; rw [this]
    simp
  refine eq_empty_of_forall_notMem fun z hz => NormedSpace.unbounded_univ 𝕜 𝕜 ?_
.mp hz obtain ⟨hz, hz'⟩ := mem_sdiff _
have := (spectrum.isBounded (x : A)).union
    h.connectedComponentIn hz' ▸ spectrum_isBounded_connectedComponentIn S x hz
  simpa

end BoundarySpectrum

namespace SpectrumRestricts

open NNReal ENNReal

/--
lemma `spectralRadius_eq` / 引理 `spectralRadius_eq`

English:
lemma spectralRadius_eq
  statement: {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  proof: by
  rw [spectralRadius]; rw [spectralRadius]
.nnnorm_map_of_map_zero (map_zero _) have := algebraMap_isometry 𝕜₁ 𝕜₂
  apply le_antisymm
  all_goals apply iSup₂_le fun x hx => ?_
.symm.trans_le le_iSup₂ (α := Real>=0∞) _ ?_ · refine congr_arg ((↑) : Real>=0 -> Real>=0∞) (this x)
    exact (spectrum.algebraMap_mem_iff _).mpr hx
  · have ⟨y, hy, hy'⟩ := h.algebraMap_image.symm ▸ hx
    subst hy'
    exact this y ▸ le_iSup₂ (α := Real>=0∞) y hy

中文:
引理 spectralRadius_eq
  结论: {𝕜₁ 𝕜₂ A : 类型} [赋范域 𝕜₁] [赋范域 𝕜₂]
  证明: by
  rw [spectralRadius]; rw [spectralRadius]
.nnnorm_map_of_map_zero (map_zero _) have := algebraMap_isometry 𝕜₁ 𝕜₂
  apply le_antisymm
  all_goals apply iSup₂_le fun x hx => ?_
.symm.trans_le le_iSup₂ (α := Real>=0∞) _ ?_ · refine congr_arg ((↑) : Real>=0 -> Real>=0∞) (this x)
    exact (spectrum.algebraMap_mem_iff _).mpr hx
  · have ⟨y, hy, hy'⟩ := h.algebraMap_image.symm ▸ hx
    subst hy'
    exact this y ▸ le_iSup₂ (α := Real>=0∞) y hy

Depends on / 依赖: algebraMap_image, algebraMap_isometry, algebraMap_mem_iff, all_goals, congr_arg, h.algebraMap_image.symm, le_antisymm, map_zero, nnnorm_map_of_map_zero, spectralRadius, spectrum, spectrum.algebraMap_mem_iff, symm.trans_le, trans_le
-/
lemma spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAlgebra 𝕜₂ A] [NormedAlgebra 𝕜₁ 𝕜₂]
    [IsScalarTower 𝕜₁ 𝕜₂ A] {f : 𝕜₂ -> 𝕜₁} {a : A} (h : SpectrumRestricts a f) :
    spectralRadius 𝕜₁ a = spectralRadius 𝕜₂ a := by
  rw [spectralRadius]; rw [spectralRadius]
.nnnorm_map_of_map_zero (map_zero _) have := algebraMap_isometry 𝕜₁ 𝕜₂
  apply le_antisymm
  all_goals apply iSup₂_le fun x hx => ?_
.symm.trans_le le_iSup₂ (α := Real>=0∞) _ ?_ · refine congr_arg ((↑) : Real>=0 -> Real>=0∞) (this x)
    exact (spectrum.algebraMap_mem_iff _).mpr hx
  · have ⟨y, hy, hy'⟩ := h.algebraMap_image.symm ▸ hx
    subst hy'
    exact this y ▸ le_iSup₂ (α := Real>=0∞) y hy

variable {A : Type*} [Ring A]

/--
lemma `nnreal_iff_spectralRadius_le` / 引理 `nnreal_iff_spectralRadius_le`

English:
lemma nnreal_iff_spectralRadius_le
  given: [Algebra Real A] {a : A} {t : Real>=0} (ht : spectralRadius Real a <= t)
  proof: by
  have : spectrum Real a subseteq Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc]; rw [← abs_le]; rw [← Real.norm_eq_abs]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe]; rw [← ENNReal.coe_le_coe]
.trans ht exact le_iSup₂ (α := Real>=0∞) x hx
  rw [nnreal_iff]
  refine ⟨fun h => iSup₂_le fun x hx => ?_, fun h => ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : exists y in spectrum Real a, ↑t - y = x := by simpa using hx
obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp this hy
    lift y to Real>=0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : forall x in spectrum Real a, ‖t - x‖₊ <= t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    peel h with x hx h_le
    rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [Real.norm_eq_abs]; rw [abs_le] at h_le
    linarith [h_le.2]

中文:
引理 nnreal_iff_spectralRadius_le
  条件: [代数 实数 A] {a : A} {t : 实数>=0} (ht : spectralRadius 实数 a <= t)
  证明: by
  have : spectrum Real a subseteq Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc]; rw [← abs_le]; rw [← Real.norm_eq_abs]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe]; rw [← ENNReal.coe_le_coe]
.trans ht exact le_iSup₂ (α := Real>=0∞) x hx
  rw [nnreal_iff]
  refine ⟨fun h => iSup₂_le fun x hx => ?_, fun h => ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : exists y in spectrum Real a, ↑t - y = x := by simpa using hx
obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp this hy
    lift y to Real>=0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : forall x in spectrum Real a, ‖t - x‖₊ <= t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    peel h with x hx h_le
    rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [Real.norm_eq_abs]; rw [abs_le] at h_le
    linarith [h_le.2]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, NNReal, NNReal.coe_le_coe, Real.norm_eq_abs, Set.Icc, Set.mem_Icc, Set.mem_Icc.mp, abs_le, coe_le_coe, coe_nnnorm, mem_Icc, nnreal_iff, norm_eq_abs, singleton_sub_eq, spectrum, spectrum.singleton_sub_eq, subseteq
-/
lemma nnreal_iff_spectralRadius_le [Algebra Real A] {a : A} {t : Real>=0} (ht : spectralRadius Real a <= t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔
      spectralRadius Real (algebraMap Real A t - a) <= t := by
  have : spectrum Real a subseteq Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc]; rw [← abs_le]; rw [← Real.norm_eq_abs]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe]; rw [← ENNReal.coe_le_coe]
.trans ht exact le_iSup₂ (α := Real>=0∞) x hx
  rw [nnreal_iff]
  refine ⟨fun h => iSup₂_le fun x hx => ?_, fun h => ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : exists y in spectrum Real a, ↑t - y = x := by simpa using hx
obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp this hy
    lift y to Real>=0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : forall x in spectrum Real a, ‖t - x‖₊ <= t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    peel h with x hx h_le
    rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [Real.norm_eq_abs]; rw [abs_le] at h_le
    linarith [h_le.2]

/--
lemma `_root_.NNReal.spectralRadius_mem_spectrum` / 引理 `_root_.NNReal.spectralRadius_mem_spectrum`

English:
lemma _root_.NNReal.spectralRadius_mem_spectrum
  statement: {A : Type*} [NormedRing A] [NormedAlgebra Real A]
  proof: by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  rw [← hx₂]; rw [ENNReal.toNNReal_coe]; rw [← spectrum.algebraMap_mem_iff Real]; rw [NNReal.algebraMap_eq_coe]
  have : 0 <= x := ha'.rightInvOn hx₁ ▸ NNReal.zero_le_coe
  convert! hx₁
  simpa

中文:
引理 _root_.非负实数.spectralRadius_mem_spectrum
  结论: {A : 类型} [赋范环 A] [赋范代数 实数 A]
  证明: by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  rw [← hx₂]; rw [ENNReal.toNNReal_coe]; rw [← spectrum.algebraMap_mem_iff Real]; rw [NNReal.algebraMap_eq_coe]
  have : 0 <= x := ha'.rightInvOn hx₁ ▸ NNReal.zero_le_coe
  convert! hx₁
  simpa

Depends on / 依赖: ENNReal, ENNReal.toNNReal_coe, NNReal, NNReal.algebraMap_eq_coe, NNReal.zero_le_coe, algebraMap_eq_coe, algebraMap_mem_iff, convert, exists_nnnorm_eq_spectralRadius_of_nonempty, rightInvOn, spectrum, spectrum.algebraMap_mem_iff, spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty, toNNReal_coe, zero_le_coe
-/
lemma _root_.NNReal.spectralRadius_mem_spectrum {A : Type*} [NormedRing A] [NormedAlgebra Real A]
    [CompleteSpace A] {a : A} (ha : (spectrum Real a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius Real a).toNNReal in spectrum Real>=0 a := by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  rw [← hx₂]; rw [ENNReal.toNNReal_coe]; rw [← spectrum.algebraMap_mem_iff Real]; rw [NNReal.algebraMap_eq_coe]
  have : 0 <= x := ha'.rightInvOn hx₁ ▸ NNReal.zero_le_coe
  convert! hx₁
  simpa

/--
lemma `_root_.Real.spectralRadius_mem_spectrum` / 引理 `_root_.Real.spectralRadius_mem_spectrum`

English:
lemma _root_.Real.spectralRadius_mem_spectrum
  statement: {A : Type*} [NormedRing A] [NormedAlgebra Real A]
  proof: NNReal.spectralRadius_mem_spectrum ha ha'

中文:
引理 _root_.实数.spectralRadius_mem_spectrum
  结论: {A : 类型} [赋范环 A] [赋范代数 实数 A]
  证明: NNReal.spectralRadius_mem_spectrum ha ha'

Depends on / 依赖: NNReal, NNReal.spectralRadius_mem_spectrum, spectralRadius_mem_spectrum
-/
lemma _root_.Real.spectralRadius_mem_spectrum {A : Type*} [NormedRing A] [NormedAlgebra Real A]
    [CompleteSpace A] {a : A} (ha : (spectrum Real a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius Real a).toReal in spectrum Real a :=
  NNReal.spectralRadius_mem_spectrum ha ha'

/--
lemma `_root_.Real.spectralRadius_mem_spectrum_or` / 引理 `_root_.Real.spectralRadius_mem_spectrum_or`

English:
lemma _root_.Real.spectralRadius_mem_spectrum_or
  statement: {A : Type*} [NormedRing A] [NormedAlgebra Real A]
  proof: by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  simp only [← hx₂, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs]
.imp (fun h => by rwa [h]) (fun h => by simpa [h]) exact abs_choice x

中文:
引理 _root_.实数.spectralRadius_mem_spectrum_or
  结论: {A : 类型} [赋范环 A] [赋范代数 实数 A]
  证明: by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  simp only [← hx₂, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs]
.imp (fun h => by rwa [h]) (fun h => by simpa [h]) exact abs_choice x

Depends on / 依赖: ENNReal, ENNReal.coe_toReal, Real.norm_eq_abs, abs_choice, coe_nnnorm, coe_toReal, exists_nnnorm_eq_spectralRadius_of_nonempty, norm_eq_abs, spectrum, spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
-/
lemma _root_.Real.spectralRadius_mem_spectrum_or {A : Type*} [NormedRing A] [NormedAlgebra Real A]
    [CompleteSpace A] {a : A} (ha : (spectrum Real a).Nonempty) :
    (spectralRadius Real a).toReal in spectrum Real a ∨ -(spectralRadius Real a).toReal in spectrum Real a := by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  simp only [← hx₂, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs]
.imp (fun h => by rwa [h]) (fun h => by simpa [h]) exact abs_choice x

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal
local notation "σₙ" => quasispectrum

/--
lemma `compactSpace` / 引理 `compactSpace`

English:
lemma compactSpace
  statement: {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
  proof: by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

中文:
引理 compactSpace
  结论: {R S A : 类型} [半域 R] [域 S] [非幺环 A]
  证明: by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

Depends on / 依赖: h.image, h_cpct, h_cpct.image, isCompact_iff_compactSpace, map_continuous
-/
lemma compactSpace {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [TopologicalSpace R] [TopologicalSpace S] {a : A} (f : C(S, R))
    (h : QuasispectrumRestricts a f) [h_cpct : CompactSpace (σₙ S a)] :
    CompactSpace (σₙ R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

end QuasispectrumRestricts

section UpperHemicontinuous

open Filter Set Topology

variable (𝕜 A)

/--
lemma `upperHemicontinuous_spectrum` / 引理 `upperHemicontinuous_spectrum`

English:
lemma upperHemicontinuous_spectrum
  statement: [NormedField 𝕜] [ProperSpace 𝕜]
  proof: by
  /- It suffices to use the sequential characterization of upper hemicontinuity.
  Suppose that `a : ℕ → A` converges to `a₀`, `x : ℕ → 𝕜` converges to `x₀`, and for all `n`,
  `x n ∈ spectrum 𝕜 (a n)`. -/
  rw [upperHemicontinuous_iff]
  refine fun a₀ => .of_sequences
(isCompact_closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)).isSeqCompact ?_
    fun a ha x hx_mem x₀ hx => ?_
  /- We must show that `spectrum 𝕜 (a n)` is eventually contained in some fixed compact set
  (we've chosen `closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)`). This follows since the spectrum of any
  `b` is bounded `‖b‖ * ‖1‖` and `a` converges to `a₀`. -/
  · filter_upwards [Metric.closedBall_mem_nhds a₀ zero_lt_one] with a ha
.trans Metric.closedBall_subset_closedBall ?_ apply spectrum.subset_closedBall_norm_mul a
    gcongr
.trans apply norm_le_norm_add_norm_sub' a a₀
    gcongr
    simpa [dist_eq_norm] using ha
  /- Finally, `x₀ ∈ spectrum 𝕜 a₀` since `algebraMap 𝕜 A x₀ - a₀` is not invertible, being itself
  the limit of the non-invertible elements `algebraMap 𝕜 A (x n) - (a n)`. -/
  · exact nonunits.isClosed.mem_of_tendsto
(continuous_algebraMap 𝕜 A |>.tendsto x₀ |>.comp hx |>.sub ha) .of_forall hx_mem

中文:
引理 upperHemicontinuous_spectrum
  结论: [赋范域 𝕜] [真空间 𝕜]
  证明: by
  /- It suffices to use the sequential characterization of upper hemicontinuity.
  Suppose that `a : ℕ → A` converges to `a₀`, `x : ℕ → 𝕜` converges to `x₀`, and for all `n`,
  `x n ∈ spectrum 𝕜 (a n)`. -/
  rw [upperHemicontinuous_iff]
  refine fun a₀ => .of_sequences
(isCompact_closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)).isSeqCompact ?_
    fun a ha x hx_mem x₀ hx => ?_
  /- We must show that `spectrum 𝕜 (a n)` is eventually contained in some fixed compact set
  (we've chosen `closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)`). This follows since the spectrum of any
  `b` is bounded `‖b‖ * ‖1‖` and `a` converges to `a₀`. -/
  · filter_upwards [Metric.closedBall_mem_nhds a₀ zero_lt_one] with a ha
.trans Metric.closedBall_subset_closedBall ?_ apply spectrum.subset_closedBall_norm_mul a
    gcongr
.trans apply norm_le_norm_add_norm_sub' a a₀
    gcongr
    simpa [dist_eq_norm] using ha
  /- Finally, `x₀ ∈ spectrum 𝕜 a₀` since `algebraMap 𝕜 A x₀ - a₀` is not invertible, being itself
  the limit of the non-invertible elements `algebraMap 𝕜 A (x n) - (a n)`. -/
  · exact nonunits.isClosed.mem_of_tendsto
(continuous_algebraMap 𝕜 A |>.tendsto x₀ |>.comp hx |>.sub ha) .of_forall hx_mem
-/
lemma upperHemicontinuous_spectrum [NormedField 𝕜] [ProperSpace 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] :
    UpperHemicontinuous (spectrum 𝕜 : A -> Set 𝕜) := by
  /- It suffices to use the sequential characterization of upper hemicontinuity.
  Suppose that `a : ℕ → A` converges to `a₀`, `x : ℕ → 𝕜` converges to `x₀`, and for all `n`,
  `x n ∈ spectrum 𝕜 (a n)`. -/
  rw [upperHemicontinuous_iff]
  refine fun a₀ => .of_sequences
(isCompact_closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)).isSeqCompact ?_
    fun a ha x hx_mem x₀ hx => ?_
  /- We must show that `spectrum 𝕜 (a n)` is eventually contained in some fixed compact set
  (we've chosen `closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)`). This follows since the spectrum of any
  `b` is bounded `‖b‖ * ‖1‖` and `a` converges to `a₀`. -/
  · filter_upwards [Metric.closedBall_mem_nhds a₀ zero_lt_one] with a ha
.trans Metric.closedBall_subset_closedBall ?_ apply spectrum.subset_closedBall_norm_mul a
    gcongr
.trans apply norm_le_norm_add_norm_sub' a a₀
    gcongr
    simpa [dist_eq_norm] using ha
  /- Finally, `x₀ ∈ spectrum 𝕜 a₀` since `algebraMap 𝕜 A x₀ - a₀` is not invertible, being itself
  the limit of the non-invertible elements `algebraMap 𝕜 A (x n) - (a n)`. -/
  · exact nonunits.isClosed.mem_of_tendsto
(continuous_algebraMap 𝕜 A |>.tendsto x₀ |>.comp hx |>.sub ha) .of_forall hx_mem

/--
theorem `upperHemicontinuous_spectrum_nnreal` / 定理 `upperHemicontinuous_spectrum_nnreal`

English:
theorem upperHemicontinuous_spectrum_nnreal
  given: [NormedRing A] [NormedAlgebra Real A] [CompleteSpace A]
  proof: by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : Real>=0 -> Real) := NNReal.isClosedEmbedding_coe
.isInducing_comp h₁ h₂ exact upperHemicontinuous_spectrum Real A

中文:
定理 upperHemicontinuous_spectrum_nnreal
  条件: [赋范环 A] [赋范代数 实数 A] [完备空间 A]
  证明: by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : Real>=0 -> Real) := NNReal.isClosedEmbedding_coe
.isInducing_comp h₁ h₂ exact upperHemicontinuous_spectrum Real A

Depends on / 依赖: IsClosedEmbedding, NNReal, NNReal.isClosedEmbedding_coe, isClosedEmbedding_coe, isInducing_comp, upperHemicontinuous_spectrum
-/
theorem upperHemicontinuous_spectrum_nnreal [NormedRing A] [NormedAlgebra Real A] [CompleteSpace A] :
    UpperHemicontinuous (spectrum Real>=0 : A -> Set Real>=0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : Real>=0 -> Real) := NNReal.isClosedEmbedding_coe
.isInducing_comp h₁ h₂ exact upperHemicontinuous_spectrum Real A

open WithLp in
/--
theorem `upperHemicontinuous_quasispectrum` / 定理 `upperHemicontinuous_quasispectrum`

English:
theorem upperHemicontinuous_quasispectrum
  statement: [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  proof: by
  convert!
.comp upperHemicontinuous_spectrum 𝕜 (WithLp 1 (Unitization 𝕜 A))
      unitization_isometry_inr.continuous
  ext1 a
  rw [Unitization.quasispectrum_eq_spectrum_inr]; rw [← AlgEquiv.spectrum_eq (unitizationAlgEquiv 𝕜 (𝕜 := 𝕜) (A := A) |>.symm)]
  congr

中文:
定理 upperHemicontinuous_quasispectrum
  结论: [NontriviallyNormedField 𝕜] [真空间 𝕜]
  证明: by
  convert!
.comp upperHemicontinuous_spectrum 𝕜 (WithLp 1 (Unitization 𝕜 A))
      unitization_isometry_inr.continuous
  ext1 a
  rw [Unitization.quasispectrum_eq_spectrum_inr]; rw [← AlgEquiv.spectrum_eq (unitizationAlgEquiv 𝕜 (𝕜 := 𝕜) (A := A) |>.symm)]
  congr

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, Unitization, Unitization.quasispectrum_eq_spectrum_inr, WithLp, continuous, convert, quasispectrum_eq_spectrum_inr, spectrum_eq, unitizationAlgEquiv, unitization_isometry_inr, unitization_isometry_inr.continuous, upperHemicontinuous_spectrum
-/
theorem upperHemicontinuous_quasispectrum [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
    [CompleteSpace A] :
    UpperHemicontinuous (quasispectrum 𝕜 : A -> Set 𝕜) := by
  convert!
.comp upperHemicontinuous_spectrum 𝕜 (WithLp 1 (Unitization 𝕜 A))
      unitization_isometry_inr.continuous
  ext1 a
  rw [Unitization.quasispectrum_eq_spectrum_inr]; rw [← AlgEquiv.spectrum_eq (unitizationAlgEquiv 𝕜 (𝕜 := 𝕜) (A := A) |>.symm)]
  congr

/--
theorem `upperHemicontinuous_quasispectrum_nnreal` / 定理 `upperHemicontinuous_quasispectrum_nnreal`

English:
theorem upperHemicontinuous_quasispectrum_nnreal
  statement: [NonUnitalNormedRing A]
  proof: by
  obtain ⟨⟨h₁, -⟩, h₂⟩ := NNReal.isClosedEmbedding_coe
  simpa [← NNReal.algebraMap_eq_coe] using
.isInducing_comp h₁ h₂ upperHemicontinuous_quasispectrum Real A

中文:
定理 upperHemicontinuous_quasispectrum_nnreal
  结论: [非幺赋范环 A]
  证明: by
  obtain ⟨⟨h₁, -⟩, h₂⟩ := NNReal.isClosedEmbedding_coe
  simpa [← NNReal.algebraMap_eq_coe] using
.isInducing_comp h₁ h₂ upperHemicontinuous_quasispectrum Real A

Depends on / 依赖: NNReal, NNReal.algebraMap_eq_coe, NNReal.isClosedEmbedding_coe, algebraMap_eq_coe, isClosedEmbedding_coe, isInducing_comp, upperHemicontinuous_quasispectrum
-/
theorem upperHemicontinuous_quasispectrum_nnreal [NonUnitalNormedRing A]
    [NormedSpace Real A] [SMulCommClass Real A A] [IsScalarTower Real A A] [CompleteSpace A] :
    UpperHemicontinuous (quasispectrum Real>=0 : A -> Set Real>=0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ := NNReal.isClosedEmbedding_coe
  simpa [← NNReal.algebraMap_eq_coe] using
.isInducing_comp h₁ h₂ upperHemicontinuous_quasispectrum Real A

end UpperHemicontinuous
