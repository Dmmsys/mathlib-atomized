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

/-- A class of almost everywhere equal functions is `Integrable` if its function representative
is integrable. -/
/-
**MeasureTheory.AEEqFun.Integrable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：Integrable (f : α ->ₘ[μ] ε) : Prop
参数：f : α ->ₘ[μ] ε。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of almost everywhere equal functions is `Integrable` if its function rep
resentative
is integrable.
-/
def Integrable (f : α →ₘ[μ] ε) : Prop :=
  MeasureTheory.Integrable f μ
/-
**MeasureTheory.AEEqFun.integrable_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：integrable_mk {f : α -> ε} (hf : AEStronglyMeasurable f μ) : Integrable (m
k f hf : α ->ₘ[μ] ε) ↔ MeasureTheory.Integrable f μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem integrable_mk {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (mk f hf : α →ₘ[μ] ε) ↔ MeasureTheory.Integrable f μ := by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf
/-
**MeasureTheory.AEEqFun.integrable_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEEqFun`。
形式化陈述：integrable_coeFn {f : α ->ₘ[μ] ε} : MeasureTheory.Integrable f μ ↔ Integra
ble f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.integrable_mk`：integrable_mk {f : α -> ε} (hf : AE
StronglyMeasurable f μ) : Integrable (mk f hf : α ->ₘ[μ] ε) ↔ MeasureTheory.Inte
grable f μ
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrable_coeFn {f : α →ₘ[μ] ε} : MeasureTheory.Integrable f μ ↔ Integrable f := by
  rw [← integrable_mk f.aestronglyMeasurable, mk_coeFn]
/-
**MeasureTheory.AEEqFun.integrable_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEEqFun`。
形式化陈述：integrable_zero : Integrable (0 : α ->ₘ[μ] ε')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem integrable_zero : Integrable (0 : α →ₘ[μ] ε') :=
  (MeasureTheory.integrable_zero α ε' μ).congr (coeFn_mk _ _).symm

end

section

/-
**MeasureTheory.AEEqFun.Integrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AEEqFun.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α →ₘ[μ] β}, f.Integrable → (-f)
.Integrable
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.AEEqFun.integrable_mk`：integrable_mk {f : α -> ε} (hf : AE
StronglyMeasurable f μ) : Integrable (mk f hf : α ->ₘ[μ] ε) ↔ MeasureTheory.Inte
grable f μ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Integrable.neg {f : α →ₘ[μ] β} : Integrable f → Integrable (-f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section

/-
**MeasureTheory.AEEqFun.integrable_iff_mem_L1** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEEqFun`。
形式化陈述：integrable_iff_mem_L1 {f : α ->ₘ[μ] β} : Integrable f ↔ f in (α ->₁[μ] β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.integrable_coeFn`：integrable_coeFn {f : α ->ₘ[μ] ε
} : MeasureTheory.Integrable f μ ↔ Integrable f
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrable_iff_mem_L1 {f : α →ₘ[μ] β} : Integrable f ↔ f ∈ (α →₁[μ] β) := by
  rw [← integrable_coeFn, ← memLp_one_iff_integrable, Lp.mem_Lp_iff_memLp]

-- TODO: generalise these lemmas to `ENormedSpace` or similar
/-
**MeasureTheory.AEEqFun.Integrable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AEEqFun.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f g : α →ₘ[μ] β}, f.Integrable → g.
Integrable → (f + g).Integrable
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on₂`：induction_on₂ {α' β' : Type*} [Meas
urableSpace α'] [TopologicalSpace β'] {μ' : Measure α'} (f : α ->ₘ[μ] β) (f' : α
' ->ₘ[μ'] β') {p : (α ->ₘ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
-/
theorem Integrable.add {f g : α →ₘ[μ] β} : Integrable f → Integrable g → Integrable (f + g) := by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi
/-
**MeasureTheory.AEEqFun.Integrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AEEqFun.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f g : α →ₘ[μ] β}, f.Integrable → g.
Integrable → (f - g).Integrable
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.Integrable.add`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {f g : α →ₘ[μ] β}, f.I…
· 使用定理 `MeasureTheory.AEEqFun.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {f : α →ₘ[μ] β}, f.Int…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem Integrable.sub {f g : α →ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) :
    Integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

/-
**MeasureTheory.AEEqFun.Integrable.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEEqFun.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_5} [inst_1 : NormedRing 
𝕜] [inst_2 : _root_.Module 𝕜 β] [inst_3 : IsBoundedSMul 𝕜 β] {c : 𝕜}   {f : α →ₘ
[μ] β}, f.Integrable → (c • f).Integrable
参数：c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.AEEqFun.integrable_mk`：integrable_mk {f : α -> ε} (hf : AE
StronglyMeasurable f μ) : Integrable (mk f hf : α ->ₘ[μ] ε) ↔ MeasureTheory.Inte
grable f μ
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : Integrable f → Integrable (c • f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 <|
    by simpa using! ((integrable_mk hfm).1 hfi).smul c

end IsBoundedSMul

end

end AEEqFun

namespace L1

@[fun_prop]
/-
**MeasureTheory.L1.integrable_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`
。
形式化陈述：integrable_coeFn (f : α ->₁[μ] β) : Integrable f μ
参数：f : α ->₁[μ] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem integrable_coeFn (f : α →₁[μ] β) : Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact Lp.memLp f
/-
**MeasureTheory.L1.hasFiniteIntegral_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.L1`。
形式化陈述：hasFiniteIntegral_coeFn (f : α ->₁[μ] β) : HasFiniteIntegral f μ
参数：f : α ->₁[μ] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
-/
theorem hasFiniteIntegral_coeFn (f : α →₁[μ] β) : HasFiniteIntegral f μ :=
  (integrable_coeFn f).hasFiniteIntegral

@[fun_prop]
/-
**MeasureTheory.L1.stronglyMeasurable_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1`。
形式化陈述：stronglyMeasurable_coeFn (f : α ->₁[μ] β) : StronglyMeasurable f
参数：f : α ->₁[μ] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
-/
theorem stronglyMeasurable_coeFn (f : α →₁[μ] β) : StronglyMeasurable f :=
  Lp.stronglyMeasurable f

@[fun_prop]
/-
**MeasureTheory.L1.measurable_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`
。
形式化陈述：measurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β) : Mea
surable f
参数：f : α ->₁[μ] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
-/
theorem measurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α →₁[μ] β) : Measurable f :=
  (Lp.stronglyMeasurable f).measurable

@[fun_prop]
/-
**MeasureTheory.L1.aestronglyMeasurable_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.L1`。
形式化陈述：aestronglyMeasurable_coeFn (f : α ->₁[μ] β) : AEStronglyMeasurable f μ
参数：f : α ->₁[μ] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
-/
theorem aestronglyMeasurable_coeFn (f : α →₁[μ] β) : AEStronglyMeasurable f μ :=
  Lp.aestronglyMeasurable f

@[fun_prop]
/-
**MeasureTheory.L1.aemeasurable_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
1`。
形式化陈述：aemeasurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α ->₁[μ] β) : A
EMeasurable f μ
参数：f : α ->₁[μ] β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
-/
theorem aemeasurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α →₁[μ] β) : AEMeasurable f μ :=
  (Lp.stronglyMeasurable f).measurable.aemeasurable
/-
**MeasureTheory.L1.edist_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：edist_def (f g : α ->₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ
参数：f g : α ->₁[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Lp.edist_def`：edist_def (f g : Lp E p μ) : edist f g = eLp
Norm (⇑f - ⇑g) p μ
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_def (f g : α →₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [Lp.edist_def, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm, Pi.sub_apply,
    toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]
/-
**MeasureTheory.L1.dist_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：dist_def (f g : α ->₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toRe
al
参数：f g : α ->₁[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.L1.edist_def`：edist_def (f g : α ->₁[μ] β) : edist f g = ∫
⁻ a, edist (f a) (g a) ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_def (f g : α →₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  simp_rw [dist_edist, edist_def]
/-
**MeasureTheory.L1.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：norm_def (f : α ->₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal
参数：f : α ->₁[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_def (f : α →₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal := by
  simp [Lp.norm_def, eLpNorm, eLpNorm'_eq_lintegral_enorm]

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
/-
**MeasureTheory.L1.norm_sub_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.L1`。
形式化陈述：norm_sub_eq_lintegral (f g : α ->₁[μ] β) : ‖f - g‖ = (∫⁻ x, ‖f x - g x‖ₑ ∂
μ).toReal
参数：f g : α ->₁[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.norm_def`：norm_def (f : α ->₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a
‖ₑ ∂μ).toReal
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Computing the norm of a difference between two L¹-functions. Note that this is n
ot a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal).
-/
theorem norm_sub_eq_lintegral (f g : α →₁[μ] β) : ‖f - g‖ = (∫⁻ x, ‖f x - g x‖ₑ ∂μ).toReal := by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]
/-
**MeasureTheory.L1.ofReal_norm_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1`。
形式化陈述：ofReal_norm_eq_lintegral (f : α ->₁[μ] β) : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f 
x‖ₑ ∂μ
参数：f : α ->₁[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.norm_def`：norm_def (f : α ->₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a
‖ₑ ∂μ).toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.L1.hasFiniteIntegral_coeFn`：hasFiniteIntegral_coeFn (f : α
 ->₁[μ] β) : HasFiniteIntegral f μ
-/
theorem ofReal_norm_eq_lintegral (f : α →₁[μ] β) : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [norm_def, ENNReal.ofReal_toReal]
  exact ne_of_lt (hasFiniteIntegral_coeFn f)

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `ofReal_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
/-
**MeasureTheory.L1.ofReal_norm_sub_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L1`。
形式化陈述：ofReal_norm_sub_eq_lintegral (f g : α ->₁[μ] β) : ENNReal.ofReal ‖f - g‖ =
 ∫⁻ x, ‖f x - g x‖ₑ ∂μ
参数：f g : α ->₁[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.ofReal_norm_eq_lintegral`：ofReal_norm_eq_lintegral (f :
 α ->₁[μ] β) : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Computing the norm of a difference between two L¹-functions. Note that this is n
ot a
  special case of `ofReal_norm_eq_lintegral` since `(f - g) x` and `f x - g x` a
re not equal
  (but only a.e.-equal).
-/
theorem ofReal_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
    ENNReal.ofReal ‖f - g‖ = ∫⁻ x, ‖f x - g x‖ₑ ∂μ := by
  simp_rw [ofReal_norm_eq_lintegral, ← edist_zero_right]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

end L1

namespace Integrable


/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `Lp β 1 μ`. -/
/-
**MeasureTheory.Integrable.toL1** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：toL1 (f : α -> β) (hf : Integrable f μ) : α ->₁[μ] β
参数：f : α -> β；hf : Integrable f μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the equivalence class `[f]` of an integrable function `f`, as a member
 of the
space `Lp β 1 μ`.
-/
def toL1 (f : α → β) (hf : Integrable f μ) : α →₁[μ] β :=
  (memLp_one_iff_integrable.2 hf).toLp f

@[simp]
/-
**MeasureTheory.Integrable.toL1_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：toL1_coeFn (f : α ->₁[μ] β) (hf : Integrable f μ) : hf.toL1 f = f
参数：f : α ->₁[μ] β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.toLp_coeFn`：toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ
) : hf.toLp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toL1_coeFn (f : α →₁[μ] β) (hf : Integrable f μ) : hf.toL1 f = f := by
  simp [Integrable.toL1]
/-
**MeasureTheory.Integrable.coeFn_toL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：coeFn_toL1 {f : α -> β} (hf : Integrable f μ) : hf.toL1 f =ᵐ[μ] f
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_toL1 {f : α → β} (hf : Integrable f μ) : hf.toL1 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

@[simp]
/-
**MeasureTheory.Integrable.toL1_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：toL1_zero (h : Integrable (0 : α -> β) μ) : h.toL1 0 = 0
参数：h : Integrable (0 : α -> β) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toL1_zero (h : Integrable (0 : α → β) μ) : h.toL1 0 = 0 :=
  rfl

@[simp]
/-
**MeasureTheory.Integrable.toL1_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：toL1_eq_mk (f : α -> β) (hf : Integrable f μ) : (hf.toL1 f : α ->ₘ[μ] β) =
 AEEqFun.mk f hf.aestronglyMeasurable
参数：f : α -> β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toL1_eq_mk (f : α → β) (hf : Integrable f μ) :
    (hf.toL1 f : α →ₘ[μ] β) = AEEqFun.mk f hf.aestronglyMeasurable :=
  rfl

@[simp]
/-
**MeasureTheory.Integrable.toL1_eq_toL1_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Integrable`。
形式化陈述：toL1_eq_toL1_iff (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ
) : toL1 f hf = toL1 g hg ↔ f =ᵐ[μ] g
参数：f g : α -> β；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.toLp_eq_toLp_iff`：toLp_eq_toLp_iff {f g : α -> E} (h
f : MemLp f p μ) (hg : MemLp g p μ) : hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g
-/
theorem toL1_eq_toL1_iff (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 f hf = toL1 g hg ↔ f =ᵐ[μ] g :=
  MemLp.toLp_eq_toLp_iff _ _
/-
**MeasureTheory.Integrable.toL1_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：toL1_add (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ) : toL1
 (f + g) (hf.add hg) = toL1 f hf + toL1 g hg
参数：f g : α -> β；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem toL1_add (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f + g) (hf.add hg) = toL1 f hf + toL1 g hg :=
  rfl
/-
**MeasureTheory.Integrable.toL1_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：toL1_neg (f : α -> β) (hf : Integrable f μ) : toL1 (-f) (Integrable.neg hf
) = -toL1 f hf
参数：f : α -> β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem toL1_neg (f : α → β) (hf : Integrable f μ) : toL1 (-f) (Integrable.neg hf) = -toL1 f hf :=
  rfl
/-
**MeasureTheory.Integrable.toL1_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：toL1_sub (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ) : toL1
 (f - g) (hf.sub hg) = toL1 f hf - toL1 g hg
参数：f g : α -> β；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
theorem toL1_sub (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f - g) (hf.sub hg) = toL1 f hf - toL1 g hg :=
  rfl
/-
**MeasureTheory.Integrable.norm_toL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：norm_toL1 (f : α -> β) (hf : Integrable f μ) : ‖hf.toL1 f‖ = (∫⁻ a, edist 
(f a) 0 ∂μ).toReal
参数：f : α -> β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Lp.norm_toLp`：norm_toLp (f : α -> E) (hf : MemLp f p μ) : 
‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_toL1 (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = (∫⁻ a, edist (f a) 0 ∂μ).toReal := by
  simp [toL1, Lp.norm_toLp, eLpNorm, eLpNorm'_eq_lintegral_enorm]
/-
**MeasureTheory.Integrable.enorm_toL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：enorm_toL1 {f : α -> β} (hf : Integrable f μ) : ‖hf.toL1 f‖ₑ = ∫⁻ a, ‖f a‖
ₑ ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Lp.enorm_def`：enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f 
p μ
· 使用定理 `MeasureTheory.eLpNorm_aeeqFun`：eLpNorm_aeeqFun {α E : Type*} [Measurable
Space α] {μ : Measure α} [NormedAddCommGroup E] {p : Real>=0∞} {f : α -> E} (hf 
: AEStronglyMeasura…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem enorm_toL1 {f : α → β} (hf : Integrable f μ) : ‖hf.toL1 f‖ₑ = ∫⁻ a, ‖f a‖ₑ ∂μ := by
  simp only [Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  simp [eLpNorm, eLpNorm']
/-
**MeasureTheory.Integrable.norm_toL1_eq_lintegral_norm** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Integrable`。
形式化陈述：norm_toL1_eq_lintegral_norm (f : α -> β) (hf : Integrable f μ) : ‖hf.toL1 
f‖ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ)
参数：f : α -> β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.norm_toL1`：norm_toL1 (f : α -> β) (hf : Integra
ble f μ) : ‖hf.toL1 f‖ = (∫⁻ a, edist (f a) 0 ∂μ).toReal
· 使用定理 `MeasureTheory.lintegral_norm_eq_lintegral_edist`：lintegral_norm_eq_linte
gral_edist (f : α -> β) : ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ
-/
theorem norm_toL1_eq_lintegral_norm (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  rw [norm_toL1, lintegral_norm_eq_lintegral_edist]
/-
**MeasureTheory.Integrable.norm_toL1_eq_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Integrable`。
形式化陈述：norm_toL1_eq_lintegral_enorm (f : α -> β) (hf : Integrable f μ) : ‖hf.toL1
 f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal
参数：f : α -> β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.norm_toL1`：norm_toL1 (f : α -> β) (hf : Integra
ble f μ) : ‖hf.toL1 f‖ = (∫⁻ a, edist (f a) 0 ∂μ).toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_toL1_eq_lintegral_enorm (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal := by
  simp_rw [norm_toL1, edist_zero_right]

@[simp]
/-
**MeasureTheory.Integrable.edist_toL1_toL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：edist_toL1_toL1 (f g : α -> β) (hf : Integrable f μ) (hg : Integrable g μ)
 : edist (hf.toL1 f) (hg.toL1 g) = ∫⁻ a, edist (f a) (g a) ∂μ
参数：f g : α -> β；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Lp.edist_toLp_toLp`：edist_toLp_toLp (f g : α -> E) (hf : M
emLp f p μ) (hg : MemLp g p μ) : edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g)
 p μ
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_toL1_toL1 (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (hf.toL1 f) (hg.toL1 g) = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [toL1, Lp.edist_toLp_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm,
    Pi.sub_apply, toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]
/-
**MeasureTheory.Integrable.edist_toL1_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：edist_toL1_zero (f : α -> β) (hf : Integrable f μ) : edist (hf.toL1 f) 0 =
 ∫⁻ a, edist (f a) 0 ∂μ
参数：f : α -> β；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `MeasureTheory.Lp.enorm_def`：enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f 
p μ
· 使用定理 `MeasureTheory.eLpNorm_aeeqFun`：eLpNorm_aeeqFun {α E : Type*} [Measurable
Space α] {μ : Measure α} [NormedAddCommGroup E] {p : Real>=0∞} {f : α -> E} (hf 
: AEStronglyMeasura…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
-/
theorem edist_toL1_zero (f : α → β) (hf : Integrable f μ) :
    edist (hf.toL1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [edist_zero_right, Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  apply eLpNorm_one_eq_lintegral_enorm

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
/-
**MeasureTheory.Integrable.toL1_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：toL1_smul (f : α -> β) (hf : Integrable f μ) (k : 𝕜) : toL1 (fun a => k • 
f a) (hf.smul k) = k • toL1 f hf
参数：f : α -> β；hf : Integrable f μ；k : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
theorem toL1_smul (f : α → β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (fun a => k • f a) (hf.smul k) = k • toL1 f hf :=
  rfl
/-
**MeasureTheory.Integrable.toL1_smul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：toL1_smul' (f : α -> β) (hf : Integrable f μ) (k : 𝕜) : toL1 (k • f) (hf.s
mul k) = k • toL1 f hf
参数：f : α -> β；hf : Integrable f μ；k : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
theorem toL1_smul' (f : α → β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (k • f) (hf.smul k) = k • toL1 f hf :=
  rfl

end Integrable

end MeasureTheory

