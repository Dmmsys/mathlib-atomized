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
    (B : E →L[𝕜] F →L[𝕜] G)

namespace ContinuousLinearMap

variable (r) in
/-
**ContinuousLinearMap.memLp_of_bilin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：memLp_of_bilin {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : MemLp g 
q μ) : MemLp (fun x => B (f x) (g x)) r μ
参数：hf : MemLp f p μ；hg : MemLp g q μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.MemLp.of_bilin`：∀ {α : Type u_1} {E : Type u_2} {F : Type 
u_3} {G : Type u_4} {m : MeasurableSpace α} [inst : NormedAddCommGroup E]   [ins
t_1 : NormedAddCom…
· 使用定理 `ContinuousLinearMap.aestronglyMeasurable_comp₂`：ContinuousLinearMap.aest
ronglyMeasurable_comp₂ (L : E ->L[𝕜] F ->L[𝕜] G) {f : α -> E} {g : α -> F} (hf :
 AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖
-/
theorem memLp_of_bilin {f : α → E} {g : α → F} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    MemLp (fun x ↦ B (f x) (g x)) r μ :=
  MeasureTheory.MemLp.of_bilin (r := r) (B · ·) ‖B‖₊ hf hg
    (B.aestronglyMeasurable_comp₂ hf.1 hg.1) (.of_forall fun _ ↦ B.le_opNorm₂ _ _)
/-
**ContinuousLinearMap.integrable_of_bilin_of_bdd_left** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：integrable_of_bilin_of_bdd_left {f : α -> E} {g : α -> F} (C : Real) (hf1 
: AEStronglyMeasurable f μ) (hf2 : forallᵐ a ∂μ, ‖f a‖ <= C) (hg : Integrable g 
μ) : Integrable (fun x => B (f x) (g x)) μ
参数：C : Real；hf1 : AEStronglyMeasurable f μ；hf2 : forallᵐ a ∂μ, ‖f a‖ <= C；hg : I
ntegrable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ContinuousLinearMap.memLp_of_bilin`：memLp_of_bilin {f : α -> E} {g : α -
> F} (hf : MemLp f p μ) (hg : MemLp g q μ) : MemLp (fun x => B (f x) (g x)) r μ
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem integrable_of_bilin_of_bdd_left {f : α → E} {g : α → F} (C : ℝ)
    (hf1 : AEStronglyMeasurable f μ) (hf2 : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) (hg : Integrable g μ) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  memLp_one_iff_integrable.1 <| B.memLp_of_bilin 1 (memLp_top_of_bound hf1 C hf2)
    (memLp_one_iff_integrable.2 hg)
/-
**ContinuousLinearMap.integrable_of_bilin_of_bdd_right** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：integrable_of_bilin_of_bdd_right {f : α -> E} {g : α -> F} (C : Real) (hf 
: Integrable f μ) (hg1 : AEStronglyMeasurable g μ) (hg2 : forallᵐ a ∂μ, ‖g a‖ <=
 C) : Integrable (fun x => B (f x) (g x)) μ
参数：C : Real；hf : Integrable f μ；hg1 : AEStronglyMeasurable g μ；hg2 : forallᵐ a ∂
μ, ‖g a‖ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.integrable_of_bilin_of_bdd_left`：integrable_of_bilin
_of_bdd_left {f : α -> E} {g : α -> F} (C : Real) (hf1 : AEStronglyMeasurable f 
μ) (hf2 : forallᵐ a ∂μ, ‖f a‖ <= C) (hg :…
-/
theorem integrable_of_bilin_of_bdd_right {f : α → E} {g : α → F} (C : ℝ)
    (hf : Integrable f μ) (hg1 : AEStronglyMeasurable g μ) (hg2 : ∀ᵐ a ∂μ, ‖g a‖ ≤ C) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  B.flip.integrable_of_bilin_of_bdd_left C hg1 hg2 hf

variable (r) in
/-- The map between `MeasureTheory.Lp` spaces satisfying `ENNReal.HolderTriple`
induced by a continuous bilinear map on the underlying spaces. -/
/-
**ContinuousLinearMap.holder** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ
参数：f : Lp E p μ；g : Lp F q μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between `MeasureTheory.Lp` spaces satisfying `ENNReal.HolderTriple`
induced by a continuous bilinear map on the underlying spaces.
-/
def holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ :=
  (B.memLp_of_bilin r (Lp.memLp f) (Lp.memLp g)).toLp
/-
**ContinuousLinearMap.coeFn_holder** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：coeFn_holder (f : Lp E p μ) (g : Lp F q μ) : B.holder r f g =ᵐ[μ] fun x =>
 B (f x) (g x)
参数：f : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.holder.eq_1`：∀ {α : Type u_1} {𝕜 : Type u_2} {E : Ty
pe u_3} {F : Type u_4} {G : Type u_5} {m : MeasurableSpace α}   {μ : MeasureTheo
ry.Measure α} {p q : …
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
-/
lemma coeFn_holder (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f g =ᵐ[μ] fun x ↦ B (f x) (g x) := by
  rw [holder]
  exact MemLp.coeFn_toLp _
/-
**ContinuousLinearMap.nnnorm_holder_apply_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：nnnorm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) : ‖B.holder r f
 g‖₊ <= ‖B‖₊ * ‖f‖₊ * ‖g‖₊
参数：f : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.enorm_def`：enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f 
p μ
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用引理 `ContinuousLinearMap.coeFn_holder`：coeFn_holder (f : Lp E p μ) (g : Lp F 
q μ) : B.holder r f g =ᵐ[μ] fun x => B (f x) (g x)
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`：eLpNorm_le_eLpNo
rm_mul_eLpNorm_of_nnnorm {p q r : Real>=0∞} (hf : AEStronglyMeasurable f μ) (hg 
: AEStronglyMeasurable g μ) (b : E -> F -> G…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖
-/
lemma nnnorm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖₊ ≤ ‖B‖₊ * ‖f‖₊ * ‖g‖₊ := by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
  apply eLpNorm_congr_ae (coeFn_holder B f g) |>.trans_le
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memLp f).1 (Lp.memLp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ ↦ B.le_opNorm₂ _ _)
/-
**ContinuousLinearMap.norm_holder_apply_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：norm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) : ‖B.holder r f g
‖ <= ‖B‖ * ‖f‖ * ‖g‖
参数：f : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用引理 `ContinuousLinearMap.nnnorm_holder_apply_apply_le`：nnnorm_holder_apply_ap
ply_le (f : Lp E p μ) (g : Lp F q μ) : ‖B.holder r f g‖₊ <= ‖B‖₊ * ‖f‖₊ * ‖g‖₊
-/
lemma norm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  NNReal.coe_le_coe.mpr <| nnnorm_holder_apply_apply_le B f g
/-
**ContinuousLinearMap.holder_add_left** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：holder_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) : B.holder r (f₁ + f₂) g
 = B.holder r f₁ g + B.holder r f₂ g
参数：f₁ f₂ : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.coeFn_add`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : Add γ] [i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma holder_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) :
    B.holder r (f₁ + f₂) g = B.holder r f₁ g + B.holder r f₂ g := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]
/-
**ContinuousLinearMap.holder_add_right** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：holder_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) : B.holder r f (g₁ + g₂
) = B.holder r f g₁ + B.holder r f g₂
参数：f : Lp E p μ；g₁ g₂ : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.coeFn_add`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : Add γ] [i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma holder_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) :
    B.holder r f (g₁ + g₂) = B.holder r f g₁ + B.holder r f g₂ := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]
/-
**ContinuousLinearMap.holder_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：holder_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) : B.holder r (c • f
) g = c • B.holder r f g
参数：c : 𝕜；f : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma holder_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r (c • f) g = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]
/-
**ContinuousLinearMap.holder_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：holder_smul_right (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) : B.holder r f (c 
• g) = c • B.holder r f g
参数：c : 𝕜；f : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**ContinuousLinearMap.holder** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ
参数：f : Lp E p μ；g : Lp F q μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MeasureTheory.Lp.holder` as a bilinear map.
-/
def holderₗ : Lp E p μ →ₗ[𝕜] Lp F q μ →ₗ[𝕜] Lp G r μ :=
  .mk₂ 𝕜 (B.holder r) B.holder_add_left B.holder_smul_left
    B.holder_add_right B.holder_smul_right

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a continuous bilinear map. -/
@[simps! apply_apply]
/-
**ContinuousLinearMap.holderL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：holderL : Lp E p μ ->L[𝕜] Lp F q μ ->L[𝕜] Lp G r μ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.norm_holder_apply_apply_le`：norm_holder_apply_apply_
le (f : Lp E p μ) (g : Lp F q μ) : ‖B.holder r f g‖ <= ‖B‖ * ‖f‖ * ‖g‖

--- 原说明 ---
`MeasureTheory.Lp.holder` as a continuous bilinear map.
-/
def holderL : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] Lp G r μ :=
  LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_holder_apply_apply_le B)
/-
**ContinuousLinearMap.norm_holderL_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：norm_holderL_le : ‖(B.holderL μ p q r)‖ <= ‖B‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `ContinuousLinearMap.norm_holder_apply_apply_le`：norm_holder_apply_apply_
le (f : Lp E p μ) (g : Lp F q μ) : ‖B.holder r f g‖ <= ‖B‖ * ‖f‖ * ‖g‖
-/
lemma norm_holderL_le : ‖(B.holderL μ p q r)‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

variable [HolderConjugate p q] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]

variable (μ p q) in
/-- The natural pairing between `Lp E p μ` and `Lp F q μ` (for Hölder conjugate `p q : ℝ≥0∞`) with
values in a space `G` induced by a bilinear map `B : E →L[𝕜] F →L[𝕜] G`.

This is given by `∫ x, B (f x) (g x) ∂μ`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, which is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is the
natural map `Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)`. -/
/-
**ContinuousLinearMap.lpPairing** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：lpPairing (B : E ->L[𝕜] F ->L[𝕜] G) : Lp E p μ ->L[𝕜] Lp F q μ ->L[𝕜] G
参数：B : E ->L[𝕜] F ->L[𝕜] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
The natural pairing between `Lp E p μ` and `Lp F q μ` (for Hölder conjugate `p q
 : ℝ≥0∞`) with
values in a space `G` induced by a bilinear map `B : E →L[𝕜] F →L[𝕜] G`.

This is given by `∫ x, B (f x) (g x) ∂μ`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, wh
ich is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is 
the
natural map `Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)`.
-/
def lpPairing (B : E →L[𝕜] F →L[𝕜] G) : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G :=
  (L1.integralCLM' 𝕜 |>.postcomp <| Lp F q μ) ∘L (B.holderL μ p q 1)
/-
**ContinuousLinearMap.lpPairing_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：lpPairing_eq_integral (f : Lp E p μ) (g : Lp F q μ) : B.lpPairing μ p q f 
g = ∫ x, B (f x) (g x) ∂μ
参数：f : Lp E p μ；g : Lp F q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ContinuousLinearMap.postcomp_apply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} {𝕜
₃ : Type u_3} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂]   [inst_2 : Norm
edField 𝕜₃] {σ : 𝕜₁ →+* …
· 使用定理 `ContinuousLinearMap.holderL_apply_apply`：∀ {α : Type u_1} {𝕜 : Type u_2}
 {E : Type u_3} {F : Type u_4} {G : Type u_5} {m : MeasurableSpace α}   (μ : Mea
sureTheory.Measure α) (p q r …
· 使用定理 `MeasureTheory.L1.integral_eq_integral`：∀ {α : Type u_1} {E : Type u_2} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m : MeasurableSpace α} 
  {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用引理 `ContinuousLinearMap.coeFn_holder`：coeFn_holder (f : Lp E p μ) (g : Lp F 
q μ) : B.holder r f g =ᵐ[μ] fun x => B (f x) (g x)
-/
lemma lpPairing_eq_integral (f : Lp E p μ) (g : Lp F q μ) :
    B.lpPairing μ p q f g = ∫ x, B (f x) (g x) ∂μ := by
  simpa [lpPairing, ← L1.integral_eq', L1.integral_eq_integral] using
    integral_congr_ae <| B.coeFn_holder _ _

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
    {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r]

section MulActionWithZero

variable [NormedRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Heterogeneous scalar multiplication of `MeasureTheory.Lp` functions by `MeasureTheory.Lp`
functions when the exponents satisfy `ENNReal.HolderTriple p q r`. -/
/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Heterogeneous scalar multiplication of `MeasureTheory.Lp` functions by `MeasureT
heory.Lp`
functions when the exponents satisfy `ENNReal.HolderTriple p q r`.
-/
instance : HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ) where
  hSMul f g := (Lp.memLp g).smul (Lp.memLp f) |>.toLp (⇑f • ⇑g)
/-
**MeasureTheory.Lp.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} : f • g = ((Lp.memLp g).smul (Lp.me
mLp f)).toLp (⇑f • ⇑g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} :
    f • g = ((Lp.memLp g).smul (Lp.memLp f)).toLp (⇑f • ⇑g) :=
  rfl
/-
**MeasureTheory.Lp.coeFn_lpSMul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_lpSMul (f : Lp 𝕜 p μ) (g : Lp E q μ) : (f • g : Lp E r μ) =ᵐ[μ] ⇑f •
 g
参数：f : Lp 𝕜 p μ；g : Lp E q μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Lp.smul_def`：smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} : f • 
g = ((Lp.memLp g).smul (Lp.memLp f)).toLp (⇑f • ⇑g)
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
-/
lemma coeFn_lpSMul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f • g : Lp E r μ) =ᵐ[μ] ⇑f • g := by
  rw [smul_def]
  exact MemLp.coeFn_toLp _
/-
**MeasureTheory.Lp.norm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p q r : ENNReal}   [hpqr : p.HolderTriple q r] [inst
 : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : MulActionWithZero 𝕜 E
]   [inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp 𝕜 p μ)) (g : ↥(MeasureT
heory.Lp E q μ)), ‖f • g‖ ≤ ‖f‖ * ‖g‖
参数：f : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用引理 `MeasureTheory.Lp.coeFn_lpSMul`：coeFn_lpSMul (f : Lp 𝕜 p μ) (g : Lp E q μ
) : (f • g : Lp E r μ) =ᵐ[μ] ⇑f • g
· 使用定理 `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`：eLpNorm_smul_le_mul_eLpNorm {
p q r : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) {φ : α -> 𝕜} (hφ 
: AEStronglyMeasurable φ μ) [hp…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
-/
protected lemma norm_smul_le (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    ‖f • g‖ ≤ ‖f‖ * ‖g‖ := by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by finiteness) ?_
  rw [eLpNorm_congr_ae (coeFn_lpSMul f g)]
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)

end MulActionWithZero

section Module

variable [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-
**MeasureTheory.Lp.smul_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p q r : ENNReal}   [hpqr : p.HolderTriple q r] [inst
 : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   
[inst_3 : IsBoundedSMul 𝕜 E] (f₁ f₂ : ↥(MeasureTheory.Lp 𝕜 p μ)) (g : ↥(MeasureT
heory.Lp E q μ)),   (f₁ + f₂) • g = f₁ • g + f₂ • g
参数：f₁ f₂ : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)；f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `MeasureTheory.AEEqFun.coeFn_add`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : Add γ] [i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma smul_add (f₁ f₂ : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f₁ + f₂) • g = f₁ • g + f₂ • g := by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_smul]
/-
**MeasureTheory.Lp.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p q r : ENNReal}   [hpqr : p.HolderTriple q r] [inst
 : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   
[inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp 𝕜 p μ)) (g₁ g₂ : ↥(MeasureT
heory.Lp E q μ)),   f • (g₁ + g₂) = f • g₁ + f • g₂
参数：f : ↥(MeasureTheory.Lp 𝕜 p μ)；g₁ g₂ : ↥(MeasureTheory.Lp E q μ)；g₁ + g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.coeFn_add`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : Add γ] [i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma add_smul (f : Lp 𝕜 p μ) (g₁ g₂ : Lp E q μ) :
    f • (g₁ + g₂) = f • g₁ + f • g₂ := by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, smul_add]

variable (E q) in
@[simp]
/-
**MeasureTheory.Lp.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} (E : Type u_4) {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p : ENNReal}   (q : ENNReal) {r : ENNReal} [hpqr : p
.HolderTriple q r] [inst : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : _root_.Module 𝕜 E] [inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp 𝕜 p
 μ)), f • 0 = 0
参数：E : Type u_4；q : ENNReal；f : ↥(MeasureTheory.Lp 𝕜 p μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MemLp.toLp_zero`：toLp_zero (h : MemLp (0 : α -> E) p μ) : 
h.toLp 0 = 0
-/
protected lemma smul_zero (f : Lp 𝕜 p μ) :
    f • (0 : Lp E q μ) = (0 : Lp E r μ) := by
  convert! MemLp.zero (ε := E) |>.toLp_zero
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero E q μ] with x hx
  rw [Pi.smul_apply', hx]
  simp

variable (𝕜 p) in
@[simp]
/-
**MeasureTheory.Lp.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} (𝕜 : Type u_3) {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} (p : ENNReal)   {q r : ENNReal} [hpqr : p.HolderTripl
e q r] [inst : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : _root_.
Module 𝕜 E] [inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp E q μ)), 0 • f 
= 0
参数：𝕜 : Type u_3；p : ENNReal；f : ↥(MeasureTheory.Lp E q μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MemLp.toLp_zero`：toLp_zero (h : MemLp (0 : α -> E) p μ) : 
h.toLp 0 = 0
-/
protected lemma zero_smul (f : Lp E q μ) :
    (0 : Lp 𝕜 p μ) • f = (0 : Lp E r μ) := by
  convert! MemLp.zero (ε := E) |>.toLp_zero
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
  rw [Pi.smul_apply', hx]
  simp

@[simp]
/-
**MeasureTheory.Lp.smul_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p q r : ENNReal}   [hpqr : p.HolderTriple q r] [inst
 : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   
[inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp 𝕜 p μ)) (g : ↥(MeasureTheor
y.Lp E q μ)), f • -g = -(f • g)
参数：f : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)；f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MeasureTheory.Lp.smul_zero`：∀ {α : Type u_1} {𝕜 : Type u_3} (E : Type u_
4) {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {p : ENNReal}   (q : EN
NReal) {r : ENNR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma smul_neg (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    f • -g = -(f • g) := by
  simp [eq_neg_iff_add_eq_zero, ← Lp.add_smul]

@[simp]
/-
**MeasureTheory.Lp.neg_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p q r : ENNReal}   [hpqr : p.HolderTriple q r] [inst
 : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   
[inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp 𝕜 p μ)) (g : ↥(MeasureTheor
y.Lp E q μ)), -f • g = -(f • g)
参数：f : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)；f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MeasureTheory.Lp.zero_smul`：∀ {α : Type u_1} (𝕜 : Type u_3) {E : Type u_
4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} (p : ENNReal)   {q r : 
ENNReal} [hpqr :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma neg_smul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    -f • g = -(f • g) := by
  simp [eq_neg_iff_add_eq_zero, ← Lp.smul_add]
/-
**MeasureTheory.Lp.neg_smul_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α} {p q r : ENNReal}   [hpqr : p.HolderTriple q r] [inst
 : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   
[inst_3 : IsBoundedSMul 𝕜 E] (f : ↥(MeasureTheory.Lp 𝕜 p μ)) (g : ↥(MeasureTheor
y.Lp E q μ)), -f • -g = f • g
参数：f : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.smul_neg`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {p q r : ENNReal}   [hpq
r : p.HolderTri…
· 使用定理 `MeasureTheory.Lp.neg_smul`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type u_4
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {p q r : ENNReal}   [hpq
r : p.HolderTri…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma neg_smul_neg (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    -f • -g = f • g := by
  simp

variable [NormedRing 𝕜'] [Module 𝕜' E] [Module 𝕜' 𝕜] [IsBoundedSMul 𝕜' E] [IsBoundedSMul 𝕜' 𝕜]
/-
**MeasureTheory.Lp.smul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜' : Type u_2} {𝕜 : Type u_3} {E : Type u_4} {m : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {p q r : ENNReal} [hpqr : p.HolderT
riple q r] [inst : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_3 : IsBoundedSMul 𝕜 E] [inst_4 : NormedRing 𝕜'] [inst_5 : 
_root_.Module 𝕜' E]   [inst_6 : _root_.Module 𝕜' 𝕜] [inst_7 : IsBoundedSMul 𝕜' E
] [inst_8 : IsBoundedSMul 𝕜' 𝕜] [IsScalarTower 𝕜' 𝕜 E]   (c : 𝕜') (f : ↥(Measure
Theory.Lp 𝕜 p μ)) (g : ↥(MeasureTheory.Lp E q μ)), (c • f) • g = c • f • g
参数：c : 𝕜'；f : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma smul_assoc [IsScalarTower 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (c • f) • g = c • (f • g) := by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [-smul_eq_mul, hx]
/-
**MeasureTheory.Lp.smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {𝕜' : Type u_2} {𝕜 : Type u_3} {E : Type u_4} {m : Measur
ableSpace α} {μ : MeasureTheory.Measure α}   {p q r : ENNReal} [hpqr : p.HolderT
riple q r] [inst : NormedRing 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_3 : IsBoundedSMul 𝕜 E] [inst_4 : NormedRing 𝕜'] [inst_5 : 
_root_.Module 𝕜' E]   [inst_6 : _root_.Module 𝕜' 𝕜] [inst_7 : IsBoundedSMul 𝕜' E
] [IsBoundedSMul 𝕜' 𝕜] [SMulCommClass 𝕜' 𝕜 E] (c : 𝕜')   (f : ↥(MeasureTheory.Lp
 𝕜 p μ)) (g : ↥(MeasureTheory.Lp E q μ)), c • f • g = f • c • g
参数：c : 𝕜'；f : ↥(MeasureTheory.Lp 𝕜 p μ)；g : ↥(MeasureTheory.Lp E q μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.toLp_congr`：toLp_congr {f g : α -> E} (hf : MemLp f 
p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) : hf.toLp f = hg.toLp g
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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

