/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# `L¹` space

In this file we establish an API between `Integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `MeasureSpace` and `β` is a
  `NormedAddCommGroup`. `f : α →ₘ β` is a "function" in `L¹`.
  In comments, `[f]` is also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Tags

function space, l1

-/

@[expose] public section

noncomputable section

open EMetric ENNReal Filter MeasureTheory NNReal Set

variable {α β ε ε' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}
variable [NormedAddCommGroup β] [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

namespace MeasureTheory

namespace AEEqFun

section

/--
Definition of `Integrable` / `Integrable` 的定义

English:
definition Integrable
  signature: (f : α ->ₘ[μ] ε)
  body: MeasureTheory.Integrable f μ

中文:
定义 Integrable
  签名: (f : α ->ₘ[μ] ε)
  定义体: MeasureTheory.Integrable f μ

Depends on / 依赖: Integrable, MeasureTheory, MeasureTheory.Integrable
-/
def Integrable (f : α ->ₘ[μ] ε) : Prop :=
  MeasureTheory.Integrable f μ

/--
theorem `integrable_mk` / 定理 `integrable_mk`

English:
theorem integrable_mk
  given: {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  proof: by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf

中文:
定理 integrable_mk
  条件: {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  证明: by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf

Depends on / 依赖: Integrable, coeFn_mk, integrable_congr
-/
theorem integrable_mk {f : α -> ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (mk f hf : α ->ₘ[μ] ε) ↔ MeasureTheory.Integrable f μ := by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf

/--
theorem `integrable_coeFn` / 定理 `integrable_coeFn`

English:
theorem integrable_coeFn
  given: {f : α ->ₘ[μ] ε}
  statement: MeasureTheory.Integrable f μ ↔ Integrable f
  proof: by
  rw [← integrable_mk f.aestronglyMeasurable]; rw [mk_coeFn]

中文:
定理 integrable_coeFn
  条件: {f : α ->ₘ[μ] ε}
  结论: MeasureTheory.整数egrable f μ ↔ 整数egrable f
  证明: by
  rw [← integrable_mk f.aestronglyMeasurable]; rw [mk_coeFn]

Depends on / 依赖: aestronglyMeasurable, f.aestronglyMeasurable, integrable_mk, mk_coeFn
-/
theorem integrable_coeFn {f : α ->ₘ[μ] ε} : MeasureTheory.Integrable f μ ↔ Integrable f := by
  rw [← integrable_mk f.aestronglyMeasurable]; rw [mk_coeFn]

/--
theorem `integrable_zero` / 定理 `integrable_zero`

English:
theorem integrable_zero
  statement: Integrable (0 : α ->ₘ[μ] ε')
  proof: (MeasureTheory.integrable_zero α ε' μ).congr (coeFn_mk _ _).symm

中文:
定理 integrable_zero
  结论: 整数egrable (0 : α ->ₘ[μ] ε')
  证明: (MeasureTheory.integrable_zero α ε' μ).congr (coeFn_mk _ _).symm

Depends on / 依赖: MeasureTheory, MeasureTheory.integrable_zero, coeFn_mk, integrable_zero
-/
theorem integrable_zero : Integrable (0 : α ->ₘ[μ] ε') :=
  (MeasureTheory.integrable_zero α ε' μ).congr (coeFn_mk _ _).symm

end

section

/--
theorem `Integrable.neg` / 定理 `Integrable.neg`

English:
theorem Integrable.neg
  given: {f : α ->ₘ[μ] β}
  statement: Integrable f -> Integrable (-f)
  proof: induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

中文:
定理 Integrable.neg
  条件: {f : α ->ₘ[μ] β}
  结论: 整数egrable f -> 整数egrable (-f)
  证明: induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg
-/
theorem Integrable.neg {f : α ->ₘ[μ] β} : Integrable f -> Integrable (-f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section

/--
theorem `integrable_iff_mem_L1` / 定理 `integrable_iff_mem_L1`

English:
theorem integrable_iff_mem_L1
  given: {f : α ->ₘ[μ] β}
  statement: Integrable f ↔ f in (α ->₁[μ] β)
  proof: by
  rw [← integrable_coeFn]; rw [← memLp_one_iff_integrable]; rw [Lp.mem_Lp_iff_memLp]

中文:
定理 integrable_iff_mem_L1
  条件: {f : α ->ₘ[μ] β}
  结论: 整数egrable f ↔ f in (α ->₁[μ] β)
  证明: by
  rw [← integrable_coeFn]; rw [← memLp_one_iff_integrable]; rw [Lp.mem_Lp_iff_memLp]

Depends on / 依赖: Lp.mem_Lp_iff_memLp, integrable_coeFn, memLp_one_iff_integrable, mem_Lp_iff_memLp
-/
theorem integrable_iff_mem_L1 {f : α ->ₘ[μ] β} : Integrable f ↔ f in (α ->₁[μ] β) := by
  rw [← integrable_coeFn]; rw [← memLp_one_iff_integrable]; rw [Lp.mem_Lp_iff_memLp]

-- TODO: generalise these lemmas to `ENormedSpace` or similar
/--
theorem `Integrable.add` / 定理 `Integrable.add`

English:
theorem Integrable.add
  given: {f g : α ->ₘ[μ] β}
  statement: Integrable f -> Integrable g -> Integrable (f + g)
  proof: by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi

中文:
定理 Integrable.add
  条件: {f g : α ->ₘ[μ] β}
  结论: 整数egrable f -> 整数egrable g -> 整数egrable (f + g)
  证明: by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi
-/
theorem Integrable.add {f g : α ->ₘ[μ] β} : Integrable f -> Integrable g -> Integrable (f + g) := by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi

/--
theorem `Integrable.sub` / 定理 `Integrable.sub`

English:
theorem Integrable.sub
  given: {f g : α ->ₘ[μ] β} (hf : Integrable f) (hg : Integrable g)
  proof: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

中文:
定理 Integrable.sub
  条件: {f g : α ->ₘ[μ] β} (hf : 整数egrable f) (hg : 整数egrable g)
  证明: (sub_eq_add_neg f g).symm ▸ hf.add hg.neg
-/
theorem Integrable.sub {f g : α ->ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) :
    Integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

/--
theorem `Integrable.smul` / 定理 `Integrable.smul`

English:
theorem Integrable.smul
  given: {c : 𝕜} {f : α ->ₘ[μ] β}
  statement: Integrable f -> Integrable (c • f)
  proof: induction_on f fun _f hfm hfi => (integrable_mk _).2
    by simpa using! ((integrable_mk hfm).1 hfi).smul c

中文:
定理 Integrable.smul
  条件: {c : 𝕜} {f : α ->ₘ[μ] β}
  结论: 整数egrable f -> 整数egrable (c • f)
  证明: induction_on f fun _f hfm hfi => (integrable_mk _).2
    by simpa using! ((integrable_mk hfm).1 hfi).smul c
-/
theorem Integrable.smul {c : 𝕜} {f : α ->ₘ[μ] β} : Integrable f -> Integrable (c • f) :=
induction_on f fun _f hfm hfi => (integrable_mk _).2
    by simpa using! ((integrable_mk hfm).1 hfi).smul c

end IsBoundedSMul

end

end AEEqFun

namespace L1

@[fun_prop]
/--
theorem `integrable_coeFn` / 定理 `integrable_coeFn`

English:
theorem integrable_coeFn
  given: (f : α ->₁[μ] β)
  statement: Integrable f μ
  proof: by
  rw [← memLp_one_iff_integrable]
  exact Lp.memLp f

中文:
定理 integrable_coeFn
  条件: (f : α ->₁[μ] β)
  结论: 整数egrable f μ
  证明: by
  rw [← memLp_one_iff_integrable]
  exact Lp.memLp f

Depends on / 依赖: Lp.memLp, memLp_one_iff_integrable
-/
theorem integrable_coeFn (f : α ->₁[μ] β) : Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact Lp.memLp f

/--
theorem `hasFiniteIntegral_coeFn` / 定理 `hasFiniteIntegral_coeFn`

English:
theorem hasFiniteIntegral_coeFn
  given: (f : α ->₁[μ] β)
  statement: HasFiniteIntegral f μ
  proof: (integrable_coeFn f).hasFiniteIntegral

@[fun_prop]

中文:
定理 hasFiniteIntegral_coeFn
  条件: (f : α ->₁[μ] β)
  结论: HasFinite整数egral f μ
  证明: (integrable_coeFn f).hasFiniteIntegral

@[fun_prop]

Depends on / 依赖: hasFiniteIntegral, integrable_coeFn
-/
theorem hasFiniteIntegral_coeFn (f : α ->₁[μ] β) : HasFiniteIntegral f μ :=
  (integrable_coeFn f).hasFiniteIntegral

@[fun_prop]
/--
theorem `stronglyMeasurable_coeFn` / 定理 `stronglyMeasurable_coeFn`

English:
theorem stronglyMeasurable_coeFn
  given: (f : α ->₁[μ] β)
  statement: StronglyMeasurable f
  proof: Lp.stronglyMeasurable f

@[fun_prop]

中文:
定理 stronglyMeasurable_coeFn
  条件: (f : α ->₁[μ] β)
  结论: StronglyMeasurable f
  证明: Lp.stronglyMeasurable f

@[fun_prop]

Depends on / 依赖: Lp.stronglyMeasurable, stronglyMeasurable
-/
theorem stronglyMeasurable_coeFn (f : α ->₁[μ] β) : StronglyMeasurable f :=
  Lp.stronglyMeasurable f

@[fun_prop]
/--
theorem `measurable_coeFn` / 定理 `measurable_coeFn`

English:
theorem measurable_coeFn
  given: [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β)
  statement: Measurable f
  proof: (Lp.stronglyMeasurable f).measurable

@[fun_prop]

中文:
定理 measurable_coeFn
  条件: [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β)
  结论: Measurable f
  证明: (Lp.stronglyMeasurable f).measurable

@[fun_prop]

Depends on / 依赖: Lp.stronglyMeasurable, measurable, stronglyMeasurable
-/
theorem measurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β) : Measurable f :=
  (Lp.stronglyMeasurable f).measurable

@[fun_prop]
/--
theorem `aestronglyMeasurable_coeFn` / 定理 `aestronglyMeasurable_coeFn`

English:
theorem aestronglyMeasurable_coeFn
  given: (f : α ->₁[μ] β)
  statement: AEStronglyMeasurable f μ
  proof: Lp.aestronglyMeasurable f

@[fun_prop]

中文:
定理 aestronglyMeasurable_coeFn
  条件: (f : α ->₁[μ] β)
  结论: AEStronglyMeasurable f μ
  证明: Lp.aestronglyMeasurable f

@[fun_prop]

Depends on / 依赖: Lp.aestronglyMeasurable, aestronglyMeasurable
-/
theorem aestronglyMeasurable_coeFn (f : α ->₁[μ] β) : AEStronglyMeasurable f μ :=
  Lp.aestronglyMeasurable f

@[fun_prop]
/--
theorem `aemeasurable_coeFn` / 定理 `aemeasurable_coeFn`

English:
theorem aemeasurable_coeFn
  given: [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β)
  statement: AEMeasurable f μ
  proof: (Lp.stronglyMeasurable f).measurable.aemeasurable

中文:
定理 aemeasurable_coeFn
  条件: [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β)
  结论: AEMeasurable f μ
  证明: (Lp.stronglyMeasurable f).measurable.aemeasurable

Depends on / 依赖: Lp.stronglyMeasurable, aemeasurable, measurable, measurable.aemeasurable, stronglyMeasurable
-/
theorem aemeasurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β) : AEMeasurable f μ :=
  (Lp.stronglyMeasurable f).measurable.aemeasurable

/--
theorem `edist_def` / 定理 `edist_def`

English:
theorem edist_def
  given: (f g : α ->₁[μ] β)
  statement: edist f g = ∫⁻ a, edist (f a) (g a) ∂μ
  proof: by
  simp only [Lp.edist_def, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm, Pi.sub_apply,
    toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

中文:
定理 edist_def
  条件: (f g : α ->₁[μ] β)
  结论: edist f g = ∫⁻ a, edist (f a) (g a) ∂μ
  证明: by
  simp only [Lp.edist_def, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm, Pi.sub_apply,
    toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

Depends on / 依赖: ENNReal, ENNReal.rpow_one, Lp.edist_def, Pi.sub_apply, _eq_lintegral_enorm, div_self, eLpNorm, edist_def, edist_eq_enorm_sub, ite_false, ne_eq, not_false_eq_true, one_ne_zero, rpow_one, sub_apply, toReal_one
-/
theorem edist_def (f g : α ->₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [Lp.edist_def, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm, Pi.sub_apply,
    toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

/--
theorem `dist_def` / 定理 `dist_def`

English:
theorem dist_def
  given: (f g : α ->₁[μ] β)
  statement: dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal
  proof: by
  simp_rw [dist_edist, edist_def]

中文:
定理 dist_def
  条件: (f g : α ->₁[μ] β)
  结论: dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).to实数
  证明: by
  simp_rw [dist_edist, edist_def]

Depends on / 依赖: dist_edist, edist_def, simp_rw
-/
theorem dist_def (f g : α ->₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  simp_rw [dist_edist, edist_def]

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (f : α ->₁[μ] β)
  statement: ‖f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal
  proof: by
  simp [Lp.norm_def, eLpNorm, eLpNorm'_eq_lintegral_enorm]

中文:
定理 norm_def
  条件: (f : α ->₁[μ] β)
  结论: ‖f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).to实数
  证明: by
  simp [Lp.norm_def, eLpNorm, eLpNorm'_eq_lintegral_enorm]

Depends on / 依赖: Lp.norm_def, _eq_lintegral_enorm, eLpNorm, norm_def
-/
theorem norm_def (f : α ->₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal := by
  simp [Lp.norm_def, eLpNorm, eLpNorm'_eq_lintegral_enorm]

/--
theorem `norm_sub_eq_lintegral` / 定理 `norm_sub_eq_lintegral`

English:
theorem norm_sub_eq_lintegral
  given: (f g : α ->₁[μ] β)
  statement: ‖f - g‖ = (∫⁻ x, ‖f x - g x‖ₑ ∂μ).toReal
  proof: by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

中文:
定理 norm_sub_eq_lintegral
  条件: (f g : α ->₁[μ] β)
  结论: ‖f - g‖ = (∫⁻ x, ‖f x - g x‖ₑ ∂μ).to实数
  证明: by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

Depends on / 依赖: Lp.coeFn_sub, Pi.sub_apply, coeFn_sub, filter_upwards, lintegral_congr_ae, norm_def, sub_apply
-/
theorem norm_sub_eq_lintegral (f g : α ->₁[μ] β) : ‖f - g‖ = (∫⁻ x, ‖f x - g x‖ₑ ∂μ).toReal := by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

/--
theorem `ofReal_norm_eq_lintegral` / 定理 `ofReal_norm_eq_lintegral`

English:
theorem ofReal_norm_eq_lintegral
  given: (f : α ->₁[μ] β)
  statement: ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ
  proof: by
  rw [norm_def]; rw [ENNReal.ofReal_toReal]
  exact ne_of_lt (hasFiniteIntegral_coeFn f)

中文:
定理 ofReal_norm_eq_lintegral
  条件: (f : α ->₁[μ] β)
  结论: ENN实数.of实数 ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ
  证明: by
  rw [norm_def]; rw [ENNReal.ofReal_toReal]
  exact ne_of_lt (hasFiniteIntegral_coeFn f)

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, hasFiniteIntegral_coeFn, ne_of_lt, norm_def, ofReal_toReal
-/
theorem ofReal_norm_eq_lintegral (f : α ->₁[μ] β) : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [norm_def]; rw [ENNReal.ofReal_toReal]
  exact ne_of_lt (hasFiniteIntegral_coeFn f)

/--
theorem `ofReal_norm_sub_eq_lintegral` / 定理 `ofReal_norm_sub_eq_lintegral`

English:
theorem ofReal_norm_sub_eq_lintegral
  given: (f g : α ->₁[μ] β)
  proof: by
  simp_rw [ofReal_norm_eq_lintegral, ← edist_zero_right]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

中文:
定理 ofReal_norm_sub_eq_lintegral
  条件: (f g : α ->₁[μ] β)
  证明: by
  simp_rw [ofReal_norm_eq_lintegral, ← edist_zero_right]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

Depends on / 依赖: Lp.coeFn_sub, Pi.sub_apply, coeFn_sub, edist_zero_right, filter_upwards, lintegral_congr_ae, ofReal_norm_eq_lintegral, simp_rw, sub_apply
-/
theorem ofReal_norm_sub_eq_lintegral (f g : α ->₁[μ] β) :
    ENNReal.ofReal ‖f - g‖ = ∫⁻ x, ‖f x - g x‖ₑ ∂μ := by
  simp_rw [ofReal_norm_eq_lintegral, ← edist_zero_right]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

end L1

namespace Integrable


/--
Definition of `toL1` / `toL1` 的定义

English:
definition toL1
  signature: (f : α -> β) (hf : Integrable f μ)
  body: (memLp_one_iff_integrable.2 hf).toLp f

@[simp]

中文:
定义 toL1
  签名: (f : α -> β) (hf : 整数egrable f μ)
  定义体: (memLp_one_iff_integrable.2 hf).toLp f

@[simp]

Depends on / 依赖: memLp_one_iff_integrable
-/
def toL1 (f : α -> β) (hf : Integrable f μ) : α ->₁[μ] β :=
  (memLp_one_iff_integrable.2 hf).toLp f

@[simp]
/--
theorem `toL1_coeFn` / 定理 `toL1_coeFn`

English:
theorem toL1_coeFn
  given: (f : α ->₁[μ] β) (hf : Integrable f μ)
  statement: hf.toL1 f = f
  proof: by
  simp [Integrable.toL1]

中文:
定理 toL1_coeFn
  条件: (f : α ->₁[μ] β) (hf : 整数egrable f μ)
  结论: hf.toL1 f = f
  证明: by
  simp [Integrable.toL1]

Depends on / 依赖: Integrable, Integrable.toL1
-/
theorem toL1_coeFn (f : α ->₁[μ] β) (hf : Integrable f μ) : hf.toL1 f = f := by
  simp [Integrable.toL1]

/--
theorem `coeFn_toL1` / 定理 `coeFn_toL1`

English:
theorem coeFn_toL1
  given: {f : α -> β} (hf : Integrable f μ)
  statement: hf.toL1 f =ᵐ[μ] f
  proof: AEEqFun.coeFn_mk _ _

@[simp]

中文:
定理 coeFn_toL1
  条件: {f : α -> β} (hf : 整数egrable f μ)
  结论: hf.toL1 f =ᵐ[μ] f
  证明: AEEqFun.coeFn_mk _ _

@[simp]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, coeFn_mk
-/
theorem coeFn_toL1 {f : α -> β} (hf : Integrable f μ) : hf.toL1 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

@[simp]
/--
theorem `toL1_zero` / 定理 `toL1_zero`

English:
theorem toL1_zero
  given: (h : Integrable (0 : α -> β) μ)
  statement: h.toL1 0 = 0
  proof: rfl

@[simp]

中文:
定理 toL1_zero
  条件: (h : 整数egrable (0 : α -> β) μ)
  结论: h.toL1 0 = 0
  证明: rfl

@[simp]
-/
theorem toL1_zero (h : Integrable (0 : α -> β) μ) : h.toL1 0 = 0 :=
  rfl

@[simp]
/--
theorem `toL1_eq_mk` / 定理 `toL1_eq_mk`

English:
theorem toL1_eq_mk
  given: (f : α -> β) (hf : Integrable f μ)
  proof: rfl

@[simp]

中文:
定理 toL1_eq_mk
  条件: (f : α -> β) (hf : 整数egrable f μ)
  证明: rfl

@[simp]
-/
theorem toL1_eq_mk (f : α -> β) (hf : Integrable f μ) :
    (hf.toL1 f : α ->ₘ[μ] β) = AEEqFun.mk f hf.aestronglyMeasurable :=
  rfl

@[simp]
/--
theorem `toL1_eq_toL1_iff` / 定理 `toL1_eq_toL1_iff`

English:
theorem toL1_eq_toL1_iff
  given: (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ)
  proof: MemLp.toLp_eq_toLp_iff _ _

中文:
定理 toL1_eq_toL1_iff
  条件: (f g : α -> β) (hf : 整数egrable f μ) (hg : 整数egrable g μ)
  证明: MemLp.toLp_eq_toLp_iff _ _

Depends on / 依赖: MemLp.toLp_eq_toLp_iff, toLp_eq_toLp_iff
-/
theorem toL1_eq_toL1_iff (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 f hf = toL1 g hg ↔ f =ᵐ[μ] g :=
  MemLp.toLp_eq_toLp_iff _ _

/--
theorem `toL1_add` / 定理 `toL1_add`

English:
theorem toL1_add
  given: (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ)
  proof: rfl

中文:
定理 toL1_add
  条件: (f g : α -> β) (hf : 整数egrable f μ) (hg : 整数egrable g μ)
  证明: rfl
-/
theorem toL1_add (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f + g) (hf.add hg) = toL1 f hf + toL1 g hg :=
  rfl

/--
theorem `toL1_neg` / 定理 `toL1_neg`

English:
theorem toL1_neg
  given: (f : α -> β) (hf : Integrable f μ)
  statement: toL1 (-f) (Integrable.neg hf) = -toL1 f hf
  proof: rfl

中文:
定理 toL1_neg
  条件: (f : α -> β) (hf : 整数egrable f μ)
  结论: toL1 (-f) (整数egrable.neg hf) = -toL1 f hf
  证明: rfl
-/
theorem toL1_neg (f : α -> β) (hf : Integrable f μ) : toL1 (-f) (Integrable.neg hf) = -toL1 f hf :=
  rfl

/--
theorem `toL1_sub` / 定理 `toL1_sub`

English:
theorem toL1_sub
  given: (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ)
  proof: rfl

中文:
定理 toL1_sub
  条件: (f g : α -> β) (hf : 整数egrable f μ) (hg : 整数egrable g μ)
  证明: rfl
-/
theorem toL1_sub (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f - g) (hf.sub hg) = toL1 f hf - toL1 g hg :=
  rfl

/--
theorem `norm_toL1` / 定理 `norm_toL1`

English:
theorem norm_toL1
  given: (f : α -> β) (hf : Integrable f μ)
  proof: by
  simp [toL1, Lp.norm_toLp, eLpNorm, eLpNorm'_eq_lintegral_enorm]

中文:
定理 norm_toL1
  条件: (f : α -> β) (hf : 整数egrable f μ)
  证明: by
  simp [toL1, Lp.norm_toLp, eLpNorm, eLpNorm'_eq_lintegral_enorm]

Depends on / 依赖: Lp.norm_toLp, _eq_lintegral_enorm, eLpNorm, norm_toLp
-/
theorem norm_toL1 (f : α -> β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = (∫⁻ a, edist (f a) 0 ∂μ).toReal := by
  simp [toL1, Lp.norm_toLp, eLpNorm, eLpNorm'_eq_lintegral_enorm]

/--
theorem `enorm_toL1` / 定理 `enorm_toL1`

English:
theorem enorm_toL1
  given: {f : α -> β} (hf : Integrable f μ)
  statement: ‖hf.toL1 f‖ₑ = ∫⁻ a, ‖f a‖ₑ ∂μ
  proof: by
  simp only [Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  simp [eLpNorm, eLpNorm']

中文:
定理 enorm_toL1
  条件: {f : α -> β} (hf : 整数egrable f μ)
  结论: ‖hf.toL1 f‖ₑ = ∫⁻ a, ‖f a‖ₑ ∂μ
  证明: by
  simp only [Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  simp [eLpNorm, eLpNorm']

Depends on / 依赖: Lp.enorm_def, eLpNorm, eLpNorm_aeeqFun, enorm_def, toL1_eq_mk
-/
theorem enorm_toL1 {f : α -> β} (hf : Integrable f μ) : ‖hf.toL1 f‖ₑ = ∫⁻ a, ‖f a‖ₑ ∂μ := by
  simp only [Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  simp [eLpNorm, eLpNorm']

/--
theorem `norm_toL1_eq_lintegral_norm` / 定理 `norm_toL1_eq_lintegral_norm`

English:
theorem norm_toL1_eq_lintegral_norm
  given: (f : α -> β) (hf : Integrable f μ)
  proof: by
  rw [norm_toL1]; rw [lintegral_norm_eq_lintegral_edist]

中文:
定理 norm_toL1_eq_lintegral_norm
  条件: (f : α -> β) (hf : 整数egrable f μ)
  证明: by
  rw [norm_toL1]; rw [lintegral_norm_eq_lintegral_edist]

Depends on / 依赖: lintegral_norm_eq_lintegral_edist, norm_toL1
-/
theorem norm_toL1_eq_lintegral_norm (f : α -> β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  rw [norm_toL1]; rw [lintegral_norm_eq_lintegral_edist]

/--
theorem `norm_toL1_eq_lintegral_enorm` / 定理 `norm_toL1_eq_lintegral_enorm`

English:
theorem norm_toL1_eq_lintegral_enorm
  given: (f : α -> β) (hf : Integrable f μ)
  proof: by
  simp_rw [norm_toL1, edist_zero_right]

@[simp]

中文:
定理 norm_toL1_eq_lintegral_enorm
  条件: (f : α -> β) (hf : 整数egrable f μ)
  证明: by
  simp_rw [norm_toL1, edist_zero_right]

@[simp]

Depends on / 依赖: edist_zero_right, norm_toL1, simp_rw
-/
theorem norm_toL1_eq_lintegral_enorm (f : α -> β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal := by
  simp_rw [norm_toL1, edist_zero_right]

@[simp]
/--
theorem `edist_toL1_toL1` / 定理 `edist_toL1_toL1`

English:
theorem edist_toL1_toL1
  given: (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  simp only [toL1, Lp.edist_toLp_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm,
    Pi.sub_apply, toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

中文:
定理 edist_toL1_toL1
  条件: (f g : α -> β) (hf : 整数egrable f μ) (hg : 整数egrable g μ)
  证明: by
  simp only [toL1, Lp.edist_toLp_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm,
    Pi.sub_apply, toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

Depends on / 依赖: ENNReal, ENNReal.rpow_one, Lp.edist_toLp_toLp, Pi.sub_apply, _eq_lintegral_enorm, div_self, eLpNorm, edist_eq_enorm_sub, edist_toLp_toLp, ite_false, ne_eq, not_false_eq_true, one_ne_zero, rpow_one, sub_apply, toReal_one
-/
theorem edist_toL1_toL1 (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (hf.toL1 f) (hg.toL1 g) = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [toL1, Lp.edist_toLp_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm,
    Pi.sub_apply, toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

/--
theorem `edist_toL1_zero` / 定理 `edist_toL1_zero`

English:
theorem edist_toL1_zero
  given: (f : α -> β) (hf : Integrable f μ)
  proof: by
  simp only [edist_zero_right, Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  apply eLpNorm_one_eq_lintegral_enorm

中文:
定理 edist_toL1_zero
  条件: (f : α -> β) (hf : 整数egrable f μ)
  证明: by
  simp only [edist_zero_right, Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  apply eLpNorm_one_eq_lintegral_enorm

Depends on / 依赖: Lp.enorm_def, eLpNorm_aeeqFun, eLpNorm_one_eq_lintegral_enorm, edist_zero_right, enorm_def, toL1_eq_mk
-/
theorem edist_toL1_zero (f : α -> β) (hf : Integrable f μ) :
    edist (hf.toL1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [edist_zero_right, Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  apply eLpNorm_one_eq_lintegral_enorm

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

/--
theorem `toL1_smul` / 定理 `toL1_smul`

English:
theorem toL1_smul
  given: (f : α -> β) (hf : Integrable f μ) (k : 𝕜)
  proof: rfl

中文:
定理 toL1_smul
  条件: (f : α -> β) (hf : 整数egrable f μ) (k : 𝕜)
  证明: rfl
-/
theorem toL1_smul (f : α -> β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (fun a => k • f a) (hf.smul k) = k • toL1 f hf :=
  rfl

/--
theorem `toL1_smul'` / 定理 `toL1_smul'`

English:
theorem toL1_smul'
  given: (f : α -> β) (hf : Integrable f μ) (k : 𝕜)
  proof: rfl

中文:
定理 toL1_smul'
  条件: (f : α -> β) (hf : 整数egrable f μ) (k : 𝕜)
  证明: rfl
-/
theorem toL1_smul' (f : α -> β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (k • f) (hf.smul k) = k • toL1 f hf :=
  rfl

end Integrable

end MeasureTheory
