/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Scalar multiplication on ℒp space
-/

public noncomputable section

open Filter

open scoped ENNReal

namespace MeasureTheory

variable {α F : Type*} {m : MeasurableSpace α} {p : Real>=0∞} {q : Real} {μ : Measure α}
  [NormedAddCommGroup F] {f : α -> F}

section Lp

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {c : 𝕜}

/--
theorem `eLpNorm'_const_smul_le` / 定理 `eLpNorm'_const_smul_le`

English:
theorem eLpNorm'_const_smul_le
  given: (hq : 0 < q)
  statement: eLpNorm' (c • f) q μ <= ‖c‖ₑ * eLpNorm' f q μ
  proof: eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le ..) hq

中文:
定理 eLpNorm'_const_smul_le
  条件: (hq : 0 < q)
  结论: eLpNorm' (c • f) q μ <= ‖c‖ₑ * eLpNorm' f q μ
  证明: eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le ..) hq
-/
theorem eLpNorm'_const_smul_le (hq : 0 < q) : eLpNorm' (c • f) q μ <= ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le ..) hq

/--
theorem `eLpNormEssSup_const_smul_le` / 定理 `eLpNormEssSup_const_smul_le`

English:
theorem eLpNormEssSup_const_smul_le
  statement: eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEssSup f μ
  proof: eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])

中文:
定理 eLpNormEssSup_const_smul_le
  结论: eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEssSup f μ
  证明: eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul, nnnorm_smul_le, of_forall
-/
theorem eLpNormEssSup_const_smul_le : eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])

/--
theorem `eLpNorm_const_smul_le` / 定理 `eLpNorm_const_smul_le`

English:
theorem eLpNorm_const_smul_le
  statement: eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
  proof: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _

中文:
定理 eLpNorm_const_smul_le
  结论: eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
  证明: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul, nnnorm_smul_le, of_forall
-/
theorem eLpNorm_const_smul_le : eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _

/--
theorem `MemLp.const_smul` / 定理 `MemLp.const_smul`

English:
theorem MemLp.const_smul
  given: (hf : MemLp f p μ) (c : 𝕜)
  statement: MemLp (c • f) p μ
  proof: ⟨hf.1.const_smul c, eLpNorm_const_smul_le.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

中文:
定理 MemLp.const_smul
  条件: (hf : MemLp f p μ) (c : 𝕜)
  结论: MemLp (c • f) p μ
  证明: ⟨hf.1.const_smul c, eLpNorm_const_smul_le.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, coe_lt_top, const_smul, eLpNorm_const_smul_le, eLpNorm_const_smul_le.trans_lt, mul_lt_top, trans_lt
-/
theorem MemLp.const_smul (hf : MemLp f p μ) (c : 𝕜) : MemLp (c • f) p μ :=
  ⟨hf.1.const_smul c, eLpNorm_const_smul_le.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

/--
theorem `MemLp.const_mul` / 定理 `MemLp.const_mul`

English:
theorem MemLp.const_mul
  given: {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜)
  statement: MemLp (fun x => c * f x) p μ
  proof: hf.const_smul c

中文:
定理 MemLp.const_mul
  条件: {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜)
  结论: MemLp (fun x => c * f x) p μ
  证明: hf.const_smul c

Depends on / 依赖: const_smul, hf.const_smul
-/
theorem MemLp.const_mul {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

/--
theorem `MemLp.mul_const` / 定理 `MemLp.mul_const`

English:
theorem MemLp.mul_const
  given: {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜)
  proof: hf.const_smul (MulOpposite.op c)

中文:
定理 MemLp.mul_const
  条件: {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜)
  证明: hf.const_smul (MulOpposite.op c)

Depends on / 依赖: MulOpposite, MulOpposite.op, const_smul, hf.const_smul
-/
theorem MemLp.mul_const {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (fun x => f x * c) p μ :=
  hf.const_smul (MulOpposite.op c)

end IsBoundedSMul

section ENormSMulClass

variable {𝕜 : Type*} [NormedRing 𝕜]
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMul 𝕜 ε] [ENormSMulClass 𝕜 ε]
  {c : 𝕜} {f : α -> ε}

/--
theorem `eLpNorm'_const_smul_le'` / 定理 `eLpNorm'_const_smul_le'`

English:
theorem eLpNorm'_const_smul_le'
  given: (hq : 0 < q)
  statement: eLpNorm' (c • f) q μ <= ‖c‖ₑ * eLpNorm' f q μ
  proof: eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) hq

中文:
定理 eLpNorm'_const_smul_le'
  条件: (hq : 0 < q)
  结论: eLpNorm' (c • f) q μ <= ‖c‖ₑ * eLpNorm' f q μ
  证明: eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) hq
-/
theorem eLpNorm'_const_smul_le' (hq : 0 < q) : eLpNorm' (c • f) q μ <= ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) hq

/--
theorem `eLpNormEssSup_const_smul_le'` / 定理 `eLpNormEssSup_const_smul_le'`

English:
theorem eLpNormEssSup_const_smul_le'
  statement: eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEssSup f μ
  proof: eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])

中文:
定理 eLpNormEssSup_const_smul_le'
  结论: eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEssSup f μ
  证明: eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul, enorm_smul, of_forall
-/
theorem eLpNormEssSup_const_smul_le' : eLpNormEssSup (c • f) μ <= ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])

/--
theorem `eLpNorm_const_smul_le'` / 定理 `eLpNorm_const_smul_le'`

English:
theorem eLpNorm_const_smul_le'
  statement: eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
  proof: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _

中文:
定理 eLpNorm_const_smul_le'
  结论: eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ
  证明: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul, enorm_smul, le_of_eq, of_forall
-/
theorem eLpNorm_const_smul_le' : eLpNorm (c • f) p μ <= ‖c‖ₑ * eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _

/--
theorem `MemLp.const_smul'` / 定理 `MemLp.const_smul'`

English:
theorem MemLp.const_smul'
  given: [ContinuousConstSMul 𝕜 ε] (hf : MemLp f p μ) (c : 𝕜)
  proof: ⟨hf.1.const_smul c, eLpNorm_const_smul_le'.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

中文:
定理 MemLp.const_smul'
  条件: [ContinuousConstSMul 𝕜 ε] (hf : MemLp f p μ) (c : 𝕜)
  证明: ⟨hf.1.const_smul c, eLpNorm_const_smul_le'.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, coe_lt_top, const_smul, eLpNorm_const_smul_le, mul_lt_top, trans_lt
-/
theorem MemLp.const_smul' [ContinuousConstSMul 𝕜 ε] (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (c • f) p μ :=
  ⟨hf.1.const_smul c, eLpNorm_const_smul_le'.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

/--
theorem `MemLp.const_mul'` / 定理 `MemLp.const_mul'`

English:
theorem MemLp.const_mul'
  given: {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜)
  statement: MemLp (fun x => c * f x) p μ
  proof: hf.const_smul c

中文:
定理 MemLp.const_mul'
  条件: {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜)
  结论: MemLp (fun x => c * f x) p μ
  证明: hf.const_smul c

Depends on / 依赖: const_smul, hf.const_smul
-/
theorem MemLp.const_mul' {f : α -> 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

end ENormSMulClass

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.

TODO: do these results hold for any `NormedRing` assuming `NormSMulClass`?
-/

section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]

/--
theorem `eLpNorm'_const_smul` / 定理 `eLpNorm'_const_smul`

English:
theorem eLpNorm'_const_smul
  given: {f : α -> F} (c : 𝕜) (hq_pos : 0 < q)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm'_eq_lintegral_enorm, hq_pos]
refine le_antisymm (eLpNorm'_const_smul_le hq_pos) ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm'_const_smul_le (c := c⁻¹) (f := c • f) hq_pos

中文:
定理 eLpNorm'_const_smul
  条件: {f : α -> F} (c : 𝕜) (hq_pos : 0 < q)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm'_eq_lintegral_enorm, hq_pos]
refine le_antisymm (eLpNorm'_const_smul_le hq_pos) ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm'_const_smul_le (c := c⁻¹) (f := c • f) hq_pos
-/
theorem eLpNorm'_const_smul {f : α -> F} (c : 𝕜) (hq_pos : 0 < q) :
    eLpNorm' (c • f) q μ = ‖c‖ₑ * eLpNorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm'_eq_lintegral_enorm, hq_pos]
refine le_antisymm (eLpNorm'_const_smul_le hq_pos) ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm'_const_smul_le (c := c⁻¹) (f := c • f) hq_pos

/--
theorem `eLpNormEssSup_const_smul` / 定理 `eLpNormEssSup_const_smul`

English:
theorem eLpNormEssSup_const_smul
  given: (c : 𝕜) (f : α -> F)
  proof: by
  simp_rw [eLpNormEssSup_eq_essSup_enorm, Pi.smul_apply, enorm_smul,
    ENNReal.essSup_const_mul]

中文:
定理 eLpNormEssSup_const_smul
  条件: (c : 𝕜) (f : α -> F)
  证明: by
  simp_rw [eLpNormEssSup_eq_essSup_enorm, Pi.smul_apply, enorm_smul,
    ENNReal.essSup_const_mul]

Depends on / 依赖: ENNReal, ENNReal.essSup_const_mul, Pi.smul_apply, eLpNormEssSup_eq_essSup_enorm, enorm_smul, essSup_const_mul, simp_rw, smul_apply
-/
theorem eLpNormEssSup_const_smul (c : 𝕜) (f : α -> F) :
    eLpNormEssSup (c • f) μ = ‖c‖ₑ * eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup_eq_essSup_enorm, Pi.smul_apply, enorm_smul,
    ENNReal.essSup_const_mul]

/--
theorem `eLpNorm_const_smul` / 定理 `eLpNorm_const_smul`

English:
theorem eLpNorm_const_smul
  given: (c : 𝕜) (f : α -> F) (p : Real>=0∞) (μ : Measure α)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simp
refine le_antisymm eLpNorm_const_smul_le ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm_const_smul_le (c := c⁻¹) (f := c • f)

中文:
定理 eLpNorm_const_smul
  条件: (c : 𝕜) (f : α -> F) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simp
refine le_antisymm eLpNorm_const_smul_le ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm_const_smul_le (c := c⁻¹) (f := c • f)

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.mul_le_of_le_div, div_eq_inv_mul, eLpNorm_const_smul_le, enorm_inv, eq_or_ne, le_antisymm, mul_le_of_le_div
-/
theorem eLpNorm_const_smul (c : 𝕜) (f : α -> F) (p : Real>=0∞) (μ : Measure α) :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
refine le_antisymm eLpNorm_const_smul_le ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm_const_smul_le (c := c⁻¹) (f := c • f)

/--
lemma `eLpNorm_nsmul` / 引理 `eLpNorm_nsmul`

English:
lemma eLpNorm_nsmul
  given: [NormedSpace Real F] (n : Nat) (f : α -> F)
  proof: by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : Real) f ..

中文:
引理 eLpNorm_nsmul
  条件: [NormedSpace 实数 F] (n : 自然数) (f : α -> F)
  证明: by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : Real) f ..

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, eLpNorm_const_smul
-/
lemma eLpNorm_nsmul [NormedSpace Real F] (n : Nat) (f : α -> F) :
    eLpNorm (n • f) p μ = n * eLpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : Real) f ..

end NormedSpace

end Lp
end MeasureTheory
