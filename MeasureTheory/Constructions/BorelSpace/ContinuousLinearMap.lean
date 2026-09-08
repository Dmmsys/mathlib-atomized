/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Measurable functions in normed spaces

-/

public section


open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

namespace ContinuousLinearMap

variable {R E F : Type*} [Semiring R]
  [SeminormedAddCommGroup E] [Module R E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SeminormedAddCommGroup F] [Module R F] [MeasurableSpace F] [BorelSpace F]

@[fun_prop]
/-
**ContinuousLinearMap.measurable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Semiring R] [inst_1
 : SeminormedAddCommGroup E]   [inst_2 : _root_.Module R E] [inst_3 : Measurable
Space E] [OpensMeasurableSpace E] [inst_5 : SeminormedAddCommGroup F]   [inst_6 
: _root_.Module R F] [inst_7 : MeasurableSpace F] [BorelSpace F] (L : E →L[R] F)
, Measurable ⇑L
参数：L : E →L[R] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
protected theorem measurable (L : E →L[R] F) : Measurable L :=
  L.continuous.measurable

@[fun_prop]
/-
**ContinuousLinearMap.measurable_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：measurable_comp (L : E ->L[R] F) {φ : α -> E} (φ_meas : Measurable φ) : Me
asurable fun a : α => L (φ a)
参数：L : E ->L[R] F；φ_meas : Measurable φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
-/
theorem measurable_comp (L : E →L[R] F) {φ : α → E} (φ_meas : Measurable φ) :
    Measurable fun a : α => L (φ a) :=
  L.measurable.comp φ_meas

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-
**ContinuousLinearMap.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：instMeasurableSpace : MeasurableSpace (E ->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMeasurableSpace : MeasurableSpace (E →L[𝕜] F) :=
  borel _
/-
**ContinuousLinearMap.instBorelSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：instBorelSpace : BorelSpace (E ->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
instance instBorelSpace : BorelSpace (E →L[𝕜] F) :=
  ⟨rfl⟩

@[fun_prop]
/-
**ContinuousLinearMap.measurable_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) : Measurable f
un f : E ->L[𝕜] F => f x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) :
    Measurable fun f : E →L[𝕜] F => f x :=
  (apply 𝕜 F x).continuous.measurable
/-
**ContinuousLinearMap.measurable_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：measurable_apply' [MeasurableSpace E] [OpensMeasurableSpace E] [Measurable
Space F] [BorelSpace F] : Measurable fun (x : E) (f : E ->L[𝕜] F) => f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
-/
theorem measurable_apply' [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] : Measurable fun (x : E) (f : E →L[𝕜] F) => f x :=
  measurable_pi_lambda _ fun f => f.measurable
/-
**ContinuousLinearMap.measurable_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：measurable_coe [MeasurableSpace F] [BorelSpace F] : Measurable fun (f : E 
->L[𝕜] F) (x : E) => f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `ContinuousLinearMap.measurable_apply`：measurable_apply [MeasurableSpace 
F] [BorelSpace F] (x : E) : Measurable fun f : E ->L[𝕜] F => f x
-/
theorem measurable_coe [MeasurableSpace F] [BorelSpace F] :
    Measurable fun (f : E →L[𝕜] F) (x : E) => f x :=
  measurable_pi_lambda _ measurable_apply

end ContinuousLinearMap

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[fun_prop]
/-
**Measurable.apply_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.apply_continuousLinearMap {φ : α -> F ->L[𝕜] E} (hφ : Measurabl
e φ) (v : F) : Measurable fun a => φ a v
参数：hφ : Measurable φ；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem Measurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} (hφ : Measurable φ) (v : F) :
    Measurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp hφ

@[fun_prop]
/-
**AEMeasurable.apply_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.apply_continuousLinearMap {φ : α -> F ->L[𝕜] E} {μ : Measure 
α} (hφ : AEMeasurable φ μ) (v : F) : AEMeasurable (fun a => φ a v) μ
参数：hφ : AEMeasurable φ μ；v : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem AEMeasurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} {μ : Measure α}
    (hφ : AEMeasurable φ μ) (v : F) : AEMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp_aemeasurable hφ

end ContinuousLinearMapNontriviallyNormedField

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [MeasurableSpace 𝕜]
variable [BorelSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [BorelSpace E]

/-
**measurable_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_smul_const {f : α -> 𝕜} {c : E} (hc : c != 0) : (Measurable fun
 x => f x • c) ↔ Measurable f
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.measurable_comp_iff`：measurable_comp_iff (hg : Measu
rableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `isClosedEmbedding_smul_left`：isClosedEmbedding_smul_left [T2Space E] {c 
: E} (hc : c != 0) : IsClosedEmbedding fun x : 𝕜 => x • c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem measurable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    (Measurable fun x => f x • c) ↔ Measurable f :=
  (isClosedEmbedding_smul_left hc).measurableEmbedding.measurable_comp_iff
/-
**aemeasurable_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_smul_const {f : α -> 𝕜} {μ : Measure α} {c : E} (hc : c != 0)
 : AEMeasurable (fun x => f x • c) μ ↔ AEMeasurable f μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.aemeasurable_comp_iff`：MeasurableEmbedding.aemeasura
ble_comp_iff {g : β -> γ} (hg : MeasurableEmbedding g) {μ : Measure α} : AEMeasu
rable (g ∘ f) μ ↔ AEMeasurable …
· 使用定理 `Topology.IsClosedEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [m
β : TopologicalSpace β] [inst_2 : Me…
· 使用定理 `isClosedEmbedding_smul_left`：isClosedEmbedding_smul_left [T2Space E] {c 
: E} (hc : c != 0) : IsClosedEmbedding fun x : 𝕜 => x • c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem aemeasurable_smul_const {f : α → 𝕜} {μ : Measure α} {c : E} (hc : c ≠ 0) :
    AEMeasurable (fun x => f x • c) μ ↔ AEMeasurable f μ :=
  (isClosedEmbedding_smul_left hc).measurableEmbedding.aemeasurable_comp_iff

end NormedSpace

