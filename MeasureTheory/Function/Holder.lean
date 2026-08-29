/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Continuous bilinear maps on `MeasureTheory.Lp` spaces

Given a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] G`, we define an associated map
`ContinuousLinearMap.holder : Lp E p μ → Lp F q μ → Lp G r μ` where `p q r` are a Hölder triple.
We bundle this into a bilinear map `ContinuousLinearMap.holderₗ` and a continuous
bilinear map `ContinuousLinearMap.holderL` under some additional assumptions.

We also declare a heterogeneous scalar multiplication (`HSMul`) instance on `MeasureTheory.Lp`
spaces. Although this could use the `ContinuousLinearMap.holder` construction above, we opt not to
do so in order to minimize the necessary type class assumptions.

When `p q : ℝ≥0∞` are Hölder conjugate (i.e., `HolderConjugate p q`), we also construct the
natural map `ContinuousLinearMap.lpPairing : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G` given by
`fun f g ↦ ∫ x, B (f x) (g x) ∂μ`. When `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, this
is the natural map `Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)`.
-/

@[expose] public section

open ENNReal MeasureTheory Lp
open scoped NNReal

noncomputable section

/-! ### Induced bilinear maps -/

section Bilinear

variable {α 𝕜 E F G : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ENNReal} [hpqr : HolderTriple p q r] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (B : E ->L[𝕜] F ->L[𝕜] G)

namespace ContinuousLinearMap

variable (r) in
/--
theorem `memLp_of_bilin` / 定理 `memLp_of_bilin`

English:
theorem memLp_of_bilin
  given: {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : MemLp g q μ)
  proof: MeasureTheory.MemLp.of_bilin (r := r) (B · ·) ‖B‖₊ hf hg
    (B.aestronglyMeasurable_comp₂ hf.1 hg.1) (.of_forall fun _ => B.le_opNorm₂ _ _)

中文:
定理 memLp_of_bilin
  条件: {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : MemLp g q μ)
  证明: MeasureTheory.MemLp.of_bilin (r := r) (B · ·) ‖B‖₊ hf hg
    (B.aestronglyMeasurable_comp₂ hf.1 hg.1) (.of_forall fun _ => B.le_opNorm₂ _ _)

Depends on / 依赖: B.aestronglyMeasurable_comp, B.le_opNorm, MeasureTheory, MeasureTheory.MemLp.of_bilin, of_bilin, of_forall
-/
theorem memLp_of_bilin {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    MemLp (fun x => B (f x) (g x)) r μ :=
  MeasureTheory.MemLp.of_bilin (r := r) (B · ·) ‖B‖₊ hf hg
    (B.aestronglyMeasurable_comp₂ hf.1 hg.1) (.of_forall fun _ => B.le_opNorm₂ _ _)

/--
theorem `integrable_of_bilin_of_bdd_left` / 定理 `integrable_of_bilin_of_bdd_left`

English:
theorem integrable_of_bilin_of_bdd_left
  statement: {f : α -> E} {g : α -> F} (C : Real)
  proof: memLp_one_iff_integrable.1 B.memLp_of_bilin 1 (memLp_top_of_bound hf1 C hf2)
    (memLp_one_iff_integrable.2 hg)

中文:
定理 integrable_of_bilin_of_bdd_left
  结论: {f : α -> E} {g : α -> F} (C : 实数)
  证明: memLp_one_iff_integrable.1 B.memLp_of_bilin 1 (memLp_top_of_bound hf1 C hf2)
    (memLp_one_iff_integrable.2 hg)

Depends on / 依赖: B.memLp_of_bilin, memLp_of_bilin, memLp_one_iff_integrable, memLp_top_of_bound
-/
theorem integrable_of_bilin_of_bdd_left {f : α -> E} {g : α -> F} (C : Real)
    (hf1 : AEStronglyMeasurable f μ) (hf2 : forallᵐ a ∂μ, ‖f a‖ <= C) (hg : Integrable g μ) :
    Integrable (fun x => B (f x) (g x)) μ :=
memLp_one_iff_integrable.1 B.memLp_of_bilin 1 (memLp_top_of_bound hf1 C hf2)
    (memLp_one_iff_integrable.2 hg)

/--
theorem `integrable_of_bilin_of_bdd_right` / 定理 `integrable_of_bilin_of_bdd_right`

English:
theorem integrable_of_bilin_of_bdd_right
  statement: {f : α -> E} {g : α -> F} (C : Real)
  proof: B.flip.integrable_of_bilin_of_bdd_left C hg1 hg2 hf

中文:
定理 integrable_of_bilin_of_bdd_right
  结论: {f : α -> E} {g : α -> F} (C : 实数)
  证明: B.flip.integrable_of_bilin_of_bdd_left C hg1 hg2 hf

Depends on / 依赖: B.flip.integrable_of_bilin_of_bdd_left, integrable_of_bilin_of_bdd_left
-/
theorem integrable_of_bilin_of_bdd_right {f : α -> E} {g : α -> F} (C : Real)
    (hf : Integrable f μ) (hg1 : AEStronglyMeasurable g μ) (hg2 : forallᵐ a ∂μ, ‖g a‖ <= C) :
    Integrable (fun x => B (f x) (g x)) μ :=
  B.flip.integrable_of_bilin_of_bdd_left C hg1 hg2 hf

variable (r) in
/--
Definition of `holder` / `holder` 的定义

English:
definition holder
  signature: (f : Lp E p μ) (g : Lp F q μ)
  body: (B.memLp_of_bilin r (Lp.memLp f) (Lp.memLp g)).toLp

中文:
定义 holder
  签名: (f : Lp E p μ) (g : Lp F q μ)
  定义体: (B.memLp_of_bilin r (Lp.memLp f) (Lp.memLp g)).toLp

Depends on / 依赖: B.memLp_of_bilin, Lp.memLp, memLp_of_bilin
-/
def holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ :=
  (B.memLp_of_bilin r (Lp.memLp f) (Lp.memLp g)).toLp

/--
lemma `coeFn_holder` / 引理 `coeFn_holder`

English:
lemma coeFn_holder
  given: (f : Lp E p μ) (g : Lp F q μ)
  proof: by
  rw [holder]
  exact MemLp.coeFn_toLp _

中文:
引理 coeFn_holder
  条件: (f : Lp E p μ) (g : Lp F q μ)
  证明: by
  rw [holder]
  exact MemLp.coeFn_toLp _

Depends on / 依赖: MemLp.coeFn_toLp, coeFn_toLp, holder
-/
lemma coeFn_holder (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f g =ᵐ[μ] fun x => B (f x) (g x) := by
  rw [holder]
  exact MemLp.coeFn_toLp _

/--
lemma `nnnorm_holder_apply_apply_le` / 引理 `nnnorm_holder_apply_apply_le`

English:
lemma nnnorm_holder_apply_apply_le
  given: (f : Lp E p μ) (g : Lp F q μ)
  proof: by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
.trans_le apply eLpNorm_congr_ae (coeFn_holder B f g)
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memLp f).1 (Lp.memLp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ => B.le_opNorm₂ _ _)

中文:
引理 nnnorm_holder_apply_apply_le
  条件: (f : Lp E p μ) (g : Lp F q μ)
  证明: by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
.trans_le apply eLpNorm_congr_ae (coeFn_holder B f g)
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memLp f).1 (Lp.memLp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ => B.le_opNorm₂ _ _)

Depends on / 依赖: B.le_opNorm, ENNReal, ENNReal.coe_le_coe, ENNReal.coe_mul, Lp.enorm_def, Lp.memLp, coeFn_holder, coe_le_coe, coe_mul, eLpNorm_congr_ae, eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm, enorm_def, enorm_eq_nnnorm, of_forall, simp_rw, trans_le
-/
lemma nnnorm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖₊ <= ‖B‖₊ * ‖f‖₊ * ‖g‖₊ := by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
.trans_le apply eLpNorm_congr_ae (coeFn_holder B f g)
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memLp f).1 (Lp.memLp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ => B.le_opNorm₂ _ _)

/--
lemma `norm_holder_apply_apply_le` / 引理 `norm_holder_apply_apply_le`

English:
lemma norm_holder_apply_apply_le
  given: (f : Lp E p μ) (g : Lp F q μ)
  proof: NNReal.coe_le_coe.mpr nnnorm_holder_apply_apply_le B f g

中文:
引理 norm_holder_apply_apply_le
  条件: (f : Lp E p μ) (g : Lp F q μ)
  证明: NNReal.coe_le_coe.mpr nnnorm_holder_apply_apply_le B f g

Depends on / 依赖: NNReal, NNReal.coe_le_coe.mpr, coe_le_coe, nnnorm_holder_apply_apply_le
-/
lemma norm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖ <= ‖B‖ * ‖f‖ * ‖g‖ :=
NNReal.coe_le_coe.mpr nnnorm_holder_apply_apply_le B f g

/--
lemma `holder_add_left` / 引理 `holder_add_left`

English:
lemma holder_add_left
  given: (f₁ f₂ : Lp E p μ) (g : Lp F q μ)
  proof: by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

中文:
引理 holder_add_left
  条件: (f₁ f₂ : Lp E p μ) (g : Lp F q μ)
  证明: by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_add, MemLp.toLp_add, MemLp.toLp_congr, coeFn_add, filter_upwards, holder, toLp_add, toLp_congr
-/
lemma holder_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) :
    B.holder r (f₁ + f₂) g = B.holder r f₁ g + B.holder r f₂ g := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

/--
lemma `holder_add_right` / 引理 `holder_add_right`

English:
lemma holder_add_right
  given: (f : Lp E p μ) (g₁ g₂ : Lp F q μ)
  proof: by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

中文:
引理 holder_add_right
  条件: (f : Lp E p μ) (g₁ g₂ : Lp F q μ)
  证明: by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_add, MemLp.toLp_add, MemLp.toLp_congr, coeFn_add, filter_upwards, holder, toLp_add, toLp_congr
-/
lemma holder_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) :
    B.holder r f (g₁ + g₂) = B.holder r f g₁ + B.holder r f g₂ := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

/--
lemma `holder_smul_left` / 引理 `holder_smul_left`

English:
lemma holder_smul_left
  given: (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ)
  proof: by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

中文:
引理 holder_smul_left
  条件: (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ)
  证明: by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

Depends on / 依赖: Lp.coeFn_smul, MemLp.toLp_congr, MemLp.toLp_const_smul, coeFn_smul, filter_upwards, holder, toLp_congr, toLp_const_smul
-/
lemma holder_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r (c • f) g = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

/--
lemma `holder_smul_right` / 引理 `holder_smul_right`

English:
lemma holder_smul_right
  given: (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ)
  proof: by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

中文:
引理 holder_smul_right
  条件: (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ)
  证明: by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

Depends on / 依赖: Lp.coeFn_smul, MemLp.toLp_congr, MemLp.toLp_const_smul, coeFn_smul, filter_upwards, holder, toLp_congr, toLp_const_smul
-/
lemma holder_smul_right (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f (c • g) = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a bilinear map. -/
@[simps! apply_apply]
/--
Definition of `holderₗ` / `holderₗ` 的定义

English:
definition holderₗ
  signature: : Lp E p μ ->ₗ[𝕜] Lp F q μ ->ₗ[𝕜] Lp G r μ
  body: .mk₂ 𝕜 (B.holder r) B.holder_add_left B.holder_smul_left
    B.holder_add_right B.holder_smul_right

中文:
定义 holderₗ
  签名: : Lp E p μ ->ₗ[𝕜] Lp F q μ ->ₗ[𝕜] Lp G r μ
  定义体: .mk₂ 𝕜 (B.holder r) B.holder_add_left B.holder_smul_left
    B.holder_add_right B.holder_smul_right

Depends on / 依赖: B.holder, B.holder_add_left, B.holder_add_right, B.holder_smul_left, B.holder_smul_right, holder, holder_add_left, holder_add_right, holder_smul_left, holder_smul_right
-/
def holderₗ : Lp E p μ ->ₗ[𝕜] Lp F q μ ->ₗ[𝕜] Lp G r μ :=
  .mk₂ 𝕜 (B.holder r) B.holder_add_left B.holder_smul_left
    B.holder_add_right B.holder_smul_right

variable [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a continuous bilinear map. -/
@[simps! apply_apply]
/--
Definition of `holderL` / `holderL` 的定义

English:
definition holderL
  signature: : Lp E p μ ->L[𝕜] Lp F q μ ->L[𝕜] Lp G r μ
  body: LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_holder_apply_apply_le B)

中文:
定义 holderL
  签名: : Lp E p μ ->L[𝕜] Lp F q μ ->L[𝕜] Lp G r μ
  定义体: LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_holder_apply_apply_le B)

Depends on / 依赖: B.holder, LinearMap, LinearMap.mkContinuous, norm_holder_apply_apply_le
-/
def holderL : Lp E p μ ->L[𝕜] Lp F q μ ->L[𝕜] Lp G r μ :=
  LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_holder_apply_apply_le B)

/--
lemma `norm_holderL_le` / 引理 `norm_holderL_le`

English:
lemma norm_holderL_le
  statement: ‖(B.holderL μ p q r)‖ <= ‖B‖
  proof: LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

中文:
引理 norm_holderL_le
  结论: ‖(B.holderL μ p q r)‖ <= ‖B‖
  证明: LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, norm_nonneg
-/
lemma norm_holderL_le : ‖(B.holderL μ p q r)‖ <= ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

variable [HolderConjugate p q] [NormedSpace Real G] [SMulCommClass Real 𝕜 G] [CompleteSpace G]

variable (μ p q) in
/--
Definition of `lpPairing` / `lpPairing` 的定义

English:
definition lpPairing
  signature: (B : E ->L[𝕜] F ->L[𝕜] G)
  body: (L1.integralCLM' 𝕜 |>.postcomp <| Lp F q μ) ∘L (B.holderL μ p q 1)

中文:
定义 lpPairing
  签名: (B : E ->L[𝕜] F ->L[𝕜] G)
  定义体: (L1.integralCLM' 𝕜 |>.postcomp <| Lp F q μ) ∘L (B.holderL μ p q 1)

Depends on / 依赖: B.holderL, L1.integralCLM, holderL, integralCLM, postcomp
-/
def lpPairing (B : E ->L[𝕜] F ->L[𝕜] G) : Lp E p μ ->L[𝕜] Lp F q μ ->L[𝕜] G :=
  (L1.integralCLM' 𝕜 |>.postcomp <| Lp F q μ) ∘L (B.holderL μ p q 1)

/--
lemma `lpPairing_eq_integral` / 引理 `lpPairing_eq_integral`

English:
lemma lpPairing_eq_integral
  given: (f : Lp E p μ) (g : Lp F q μ)
  proof: by
  simpa [lpPairing, ← L1.integral_eq', L1.integral_eq_integral] using
integral_congr_ae B.coeFn_holder _ _

中文:
引理 lpPairing_eq_integral
  条件: (f : Lp E p μ) (g : Lp F q μ)
  证明: by
  simpa [lpPairing, ← L1.integral_eq', L1.integral_eq_integral] using
integral_congr_ae B.coeFn_holder _ _

Depends on / 依赖: B.coeFn_holder, L1.integral_eq, L1.integral_eq_integral, coeFn_holder, integral_congr_ae, integral_eq, integral_eq_integral, lpPairing
-/
lemma lpPairing_eq_integral (f : Lp E p μ) (g : Lp F q μ) :
    B.lpPairing μ p q f g = ∫ x, B (f x) (g x) ∂μ := by
  simpa [lpPairing, ← L1.integral_eq', L1.integral_eq_integral] using
integral_congr_ae B.coeFn_holder _ _

end ContinuousLinearMap

end Bilinear

namespace MeasureTheory
namespace Lp

/-! ### Heterogeneous scalar multiplication

While the previous section is *nominally* more general than this one, and indeed, we could
use the constructions of the previous section to define the scalar multiplication herein,
we would lose some slight generality as we would need to require that `𝕜` is a nontrivially
normed field everywhere. Moreover, it would only simplify a few proofs.
-/

section SMul

variable {α 𝕜' 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : Real>=0∞} [hpqr : HolderTriple p q r]

section MulActionWithZero

variable [NormedRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ)
  body: (Lp.memLp g).smul (Lp.memLp f)

中文:
实例 :
  签名: 异质标量乘法 (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ)
  定义体: (Lp.memLp g).smul (Lp.memLp f)

Depends on / 依赖: Lp.memLp
-/
instance : HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ) where
.toLp (⇑f • ⇑g) hSMul f g := (Lp.memLp g).smul (Lp.memLp f)

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: {f : Lp 𝕜 p μ} {g : Lp E q μ}
  proof: rfl

中文:
引理 smul_def
  条件: {f : Lp 𝕜 p μ} {g : Lp E q μ}
  证明: rfl
-/
lemma smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} :
    f • g = ((Lp.memLp g).smul (Lp.memLp f)).toLp (⇑f • ⇑g) :=
  rfl

/--
lemma `coeFn_lpSMul` / 引理 `coeFn_lpSMul`

English:
lemma coeFn_lpSMul
  given: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  proof: by
  rw [smul_def]
  exact MemLp.coeFn_toLp _

中文:
引理 coeFn_lpSMul
  条件: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  证明: by
  rw [smul_def]
  exact MemLp.coeFn_toLp _

Depends on / 依赖: MemLp.coeFn_toLp, coeFn_toLp, smul_def
-/
lemma coeFn_lpSMul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f • g : Lp E r μ) =ᵐ[μ] ⇑f • g := by
  rw [smul_def]
  exact MemLp.coeFn_toLp _

/--
lemma `norm_smul_le` / 引理 `norm_smul_le`

English:
lemma norm_smul_le
  given: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  proof: by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by finiteness) ?_
  rw [eLpNorm_congr_ae (coeFn_lpSMul f g)]
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)

中文:
引理 norm_smul_le
  条件: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  证明: by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by finiteness) ?_
  rw [eLpNorm_congr_ae (coeFn_lpSMul f g)]
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)
-/
protected lemma norm_smul_le (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    ‖f • g‖ <= ‖f‖ * ‖g‖ := by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by finiteness) ?_
  rw [eLpNorm_congr_ae (coeFn_lpSMul f g)]
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)

end MulActionWithZero

section Module

variable [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
lemma `smul_add` / 引理 `smul_add`

English:
lemma smul_add
  given: (f₁ f₂ : Lp 𝕜 p μ) (g : Lp E q μ)
  proof: by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_smul]

中文:
引理 smul_add
  条件: (f₁ f₂ : Lp 𝕜 p μ) (g : Lp E q μ)
  证明: by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_smul]
-/
protected lemma smul_add (f₁ f₂ : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f₁ + f₂) • g = f₁ • g + f₂ • g := by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_smul]

/--
lemma `add_smul` / 引理 `add_smul`

English:
lemma add_smul
  given: (f : Lp 𝕜 p μ) (g₁ g₂ : Lp E q μ)
  proof: by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, smul_add]

中文:
引理 add_smul
  条件: (f : Lp 𝕜 p μ) (g₁ g₂ : Lp E q μ)
  证明: by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, smul_add]
-/
protected lemma add_smul (f : Lp 𝕜 p μ) (g₁ g₂ : Lp E q μ) :
    f • (g₁ + g₂) = f • g₁ + f • g₂ := by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, smul_add]

variable (E q) in
@[simp]
/--
lemma `smul_zero` / 引理 `smul_zero`

English:
lemma smul_zero
  given: (f : Lp 𝕜 p μ)
  proof: by
.toLp_zero convert! MemLp.zero (ε := E)
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero E q μ] with x hx
  rw [Pi.smul_apply']; rw [hx]
  simp

中文:
引理 smul_zero
  条件: (f : Lp 𝕜 p μ)
  证明: by
.toLp_zero convert! MemLp.zero (ε := E)
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero E q μ] with x hx
  rw [Pi.smul_apply']; rw [hx]
  simp
-/
protected lemma smul_zero (f : Lp 𝕜 p μ) :
    f • (0 : Lp E q μ) = (0 : Lp E r μ) := by
.toLp_zero convert! MemLp.zero (ε := E)
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero E q μ] with x hx
  rw [Pi.smul_apply']; rw [hx]
  simp

variable (𝕜 p) in
@[simp]
/--
lemma `zero_smul` / 引理 `zero_smul`

English:
lemma zero_smul
  given: (f : Lp E q μ)
  proof: by
.toLp_zero convert! MemLp.zero (ε := E)
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
  rw [Pi.smul_apply']; rw [hx]
  simp

@[simp]

中文:
引理 zero_smul
  条件: (f : Lp E q μ)
  证明: by
.toLp_zero convert! MemLp.zero (ε := E)
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
  rw [Pi.smul_apply']; rw [hx]
  simp

@[simp]
-/
protected lemma zero_smul (f : Lp E q μ) :
    (0 : Lp 𝕜 p μ) • f = (0 : Lp E r μ) := by
.toLp_zero convert! MemLp.zero (ε := E)
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
  rw [Pi.smul_apply']; rw [hx]
  simp

@[simp]
/--
lemma `smul_neg` / 引理 `smul_neg`

English:
lemma smul_neg
  given: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  proof: by
  simp [eq_neg_iff_add_eq_zero, ← Lp.add_smul]

@[simp]

中文:
引理 smul_neg
  条件: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  证明: by
  simp [eq_neg_iff_add_eq_zero, ← Lp.add_smul]

@[simp]
-/
protected lemma smul_neg (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    f • -g = -(f • g) := by
  simp [eq_neg_iff_add_eq_zero, ← Lp.add_smul]

@[simp]
/--
lemma `neg_smul` / 引理 `neg_smul`

English:
lemma neg_smul
  given: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  proof: by
  simp [eq_neg_iff_add_eq_zero, ← Lp.smul_add]

中文:
引理 neg_smul
  条件: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  证明: by
  simp [eq_neg_iff_add_eq_zero, ← Lp.smul_add]
-/
protected lemma neg_smul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    -f • g = -(f • g) := by
  simp [eq_neg_iff_add_eq_zero, ← Lp.smul_add]

/--
lemma `neg_smul_neg` / 引理 `neg_smul_neg`

English:
lemma neg_smul_neg
  given: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  proof: by
  simp

中文:
引理 neg_smul_neg
  条件: (f : Lp 𝕜 p μ) (g : Lp E q μ)
  证明: by
  simp
-/
protected lemma neg_smul_neg (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    -f • -g = f • g := by
  simp

variable [NormedRing 𝕜'] [Module 𝕜' E] [Module 𝕜' 𝕜] [IsBoundedSMul 𝕜' E] [IsBoundedSMul 𝕜' 𝕜]

/--
lemma `smul_assoc` / 引理 `smul_assoc`

English:
lemma smul_assoc
  statement: [IsScalarTower 𝕜' 𝕜 E]
  proof: by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [-smul_eq_mul, hx]

中文:
引理 smul_assoc
  结论: [标量塔 𝕜' 𝕜 E]
  证明: by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [-smul_eq_mul, hx]
-/
protected lemma smul_assoc [IsScalarTower 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (c • f) • g = c • (f • g) := by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [-smul_eq_mul, hx]

/--
lemma `smul_comm` / 引理 `smul_comm`

English:
lemma smul_comm
  statement: [SMulCommClass 𝕜' 𝕜 E]
  proof: by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hfx hgx
  simp [smul_comm, hgx]

中文:
引理 smul_comm
  结论: [标量交换类 𝕜' 𝕜 E]
  证明: by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hfx hgx
  simp [smul_comm, hgx]
-/
protected lemma smul_comm [SMulCommClass 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    c • f • g = f • c • g := by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hfx hgx
  simp [smul_comm, hgx]

end Module

end SMul

end Lp
end MeasureTheory
