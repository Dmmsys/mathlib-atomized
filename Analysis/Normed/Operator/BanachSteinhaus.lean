/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem for normed spaces: any collection of bounded linear
maps from a Banach space into a normed space which is pointwise bounded is uniformly bounded.

Note that we prove the more general version about barrelled spaces in
`Analysis.LocallyConvex.Barrelled`, and the usual version below is indeed deduced from the
more general setup.
-/

public section

open Set

variable {E F 𝕜 𝕜₂ : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded.

See also `WithSeminorms.banach_steinhaus` for the general statement in barrelled spaces. -/
/-
**banach_steinhaus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι -> E ->SL[σ₁₂] F} (h
 : forall x, exists C, forall i, ‖g i x‖ <= C) : exists C', forall i, ‖g i‖ <= C
'
参数：h : forall x, exists C, forall i, ‖g i x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `NormedSpace.equicontinuous_TFAE`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : T
ype u_5} {F : Type u_6} {ι : Type u_9} [inst : NontriviallyNormedField 𝕜]   [ins
t_1 : NontriviallyNor…
· 使用定理 `WithSeminorms.banach_steinhaus`：∀ {ι : Type u_2} {κ : Type u_3} {𝕜₁ : Ty
pe u_4} {𝕜₂ : Type u_5} {E : Type u_6} {F : Type u_7}   [inst : NontriviallyNorm
edField 𝕜₁] [inst_1 …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `BaireSpace.of_completelyPseudoMetrizable`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X], BaireSpac
e X
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseu
dometrizable`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(unifo
rmity X).IsCountablyGenerated],   TopologicalSpace.IsCompletelyPseudoMetri…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is
 pointwise
bounded, then the norms of these linear maps are uniformly bounded.

See also `WithSeminorms.banach_steinhaus` for the general statement in barrelled
 spaces.
-/
theorem banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  rw [show (∃ C, ∀ i, ‖g i‖ ≤ C) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 5 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x ↦ ?_)
  simpa [bddAbove_def, forall_mem_range] using h x

open ENNReal

/-- This version of Banach-Steinhaus is stated in terms of suprema of `↑‖·‖₊ : ℝ≥0∞`
for convenience. -/
/-
**banach_steinhaus_iSup_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：banach_steinhaus_iSup_nnnorm {ι : Type*} [CompleteSpace E] {g : ι -> E ->S
L[σ₁₂] F} (h : forall x, (⨆ i, ↑‖g i x‖₊) < ∞) : (⨆ i, ↑‖g i‖₊) < ∞
参数：h : forall x, (⨆ i, ↑‖g i x‖₊) < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `NormedSpace.equicontinuous_TFAE`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E : T
ype u_5} {F : Type u_6} {ι : Type u_9} [inst : NontriviallyNormedField 𝕜]   [ins
t_1 : NontriviallyNor…
· 使用定理 `WithSeminorms.banach_steinhaus`：∀ {ι : Type u_2} {κ : Type u_3} {𝕜₁ : Ty
pe u_4} {𝕜₂ : Type u_5} {E : Type u_6} {F : Type u_7}   [inst : NontriviallyNorm
edField 𝕜₁] [inst_1 …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `BaireSpace.of_completelyPseudoMetrizable`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X], BaireSpac
e X
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseu
dometrizable`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(unifo
rmity X).IsCountablyGenerated],   TopologicalSpace.IsCompletelyPseudoMetri…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENNReal.iSup_coe_lt_top`：iSup_coe_lt_top : ⨆ i, (f i : Real>=0∞) < ⊤ ↔ B
ddAbove (range f)

--- 原说明 ---
This version of Banach-Steinhaus is stated in terms of suprema of `↑‖·‖₊ : ℝ≥0∞`
for convenience.
-/
theorem banach_steinhaus_iSup_nnnorm {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, (⨆ i, ↑‖g i x‖₊) < ∞) : (⨆ i, ↑‖g i‖₊) < ∞ := by
  rw [show ((⨆ i, ↑‖g i‖₊) < ∞) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 8 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x ↦ ?_)
  simpa [← NNReal.bddAbove_coe, ← Set.range_comp] using! ENNReal.iSup_coe_lt_top.1 (h x)
