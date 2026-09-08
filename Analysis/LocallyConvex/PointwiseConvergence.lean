/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.StrongTopology

/-!
# The topology of pointwise convergence is locally convex

We prove that the topology of pointwise convergence is induced by a family of seminorms and
that it is locally convex in the topological sense

* `PointwiseConvergenceCLM.seminorm`: the seminorms on `E →SLₚₜ[σ] F` given by `A ↦ ‖A x‖` for fixed
  `x : E`.
* `PointwiseConvergenceCLM.withSeminorm`: the topology is induced by the seminorms.
* `PointwiseConvergenceCLM.instLocallyConvexSpace`: `E →SLₚₜ[σ] F` is locally convex.

-/

@[expose] public section

variable {α R 𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₃ →+* 𝕜₂} {D E F G : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]

namespace PointwiseConvergenceCLM

section NormedSpace

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
/-
**PointwiseConvergenceCLM.seminorm** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergen
ceCLM`。
形式化陈述：{𝕜₁ : Type u_3} →   {𝕜₂ : Type u_4} →     [inst : NormedField 𝕜₁] →       
[inst_1 : NormedField 𝕜₂] →         {σ : 𝕜₁ →+* 𝕜₂} →           {E : Type u_7} →
             {F : Type u_8} →               [inst_2 : AddCommGroup E] →         
        [inst_3 : TopologicalSpace E] →                   [inst_4 : _root_.Modul
e 𝕜₁ E] →                     [inst_5 : NormedAddCommGroup F] → [inst_6 : Normed
Space 𝕜₂ F] → E → Seminorm 𝕜₂ (E →SLₚₜ[σ] F)
参数：E →SLₚₜ[σ] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms that induce the topology of pointwise convergence, namel
y `‖A x‖` for
all `x : E`.
-/
protected def seminorm (x : E) : Seminorm 𝕜₂ (E →SLₚₜ[σ] F) where
  toFun A := ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using! norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]

variable (σ E F) in
/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
/-
**PointwiseConvergenceCLM.seminormFamily** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseCon
vergenceCLM`。
形式化陈述：{𝕜₁ : Type u_3} →   {𝕜₂ : Type u_4} →     [inst : NormedField 𝕜₁] →       
[inst_1 : NormedField 𝕜₂] →         (σ : 𝕜₁ →+* 𝕜₂) →           (E : Type u_7) →
             (F : Type u_8) →               [inst_2 : AddCommGroup E] →         
        [inst_3 : TopologicalSpace E] →                   [inst_4 : _root_.Modul
e 𝕜₁ E] →                     [inst_5 : NormedAddCommGroup F] → [inst_6 : Normed
Space 𝕜₂ F] → SeminormFamily 𝕜₂ (E →SLₚₜ[σ] F) E
参数：σ : 𝕜₁ →+* 𝕜₂；E : Type u_7；F : Type u_8；E →SLₚₜ[σ] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms that induce the topology of pointwise convergence, namel
y `‖A x‖` for
all `x : E`.
-/
protected abbrev seminormFamily : SeminormFamily 𝕜₂ (E →SLₚₜ[σ] F) E :=
  PointwiseConvergenceCLM.seminorm

variable (σ E F) in
/-- The coercion `E →SLₚₜ[σ] F` to `E → F` as a linear map.

The topology on `E →SLₚₜ[σ] F` is induced by this map. -/
/-
**PointwiseConvergenceCLM.inducingFn** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConverg
enceCLM`。
形式化陈述：inducingFn : (E ->SLₚₜ[σ] F) ->ₗ[𝕜₂] (E -> F) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion `E →SLₚₜ[σ] F` to `E → F` as a linear map.

The topology on `E →SLₚₜ[σ] F` is induced by this map.
-/
def inducingFn : (E →SLₚₜ[σ] F) →ₗ[𝕜₂] (E → F) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (σ E F) in
/-
**PointwiseConvergenceCLM.isInducing_inducingFn** 是 Mathlib 中的一个定理，位于命名空间 `Point
wiseConvergenceCLM`。
形式化陈述：isInducing_inducingFn : Topology.IsInducing (inducingFn σ E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `PointwiseConvergenceCLM.isEmbedding_coeFn`：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type 
u_5} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) (E : Type
 u_7)   (F : Type u_8) [inst_2 …
-/
theorem isInducing_inducingFn : Topology.IsInducing (inducingFn σ E F) :=
  (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing
/-
**PointwiseConvergenceCLM.withSeminorms** 是 Mathlib 中的一个引理，位于命名空间 `PointwiseConv
ergenceCLM`。
形式化陈述：withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E 
F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Topology.IsInducing.withSeminorms`：Topology.IsInducing.withSeminorms {q 
: SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) [TopologicalSpace E] {f : E ->ₛₗ
[σ₁₂] F} (hf : IsInduci…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `WithSeminorms.congr_equiv`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9
} {ι' : Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : 
_root_.Module 𝕜…
· 使用定理 `withSeminorms_pi`：withSeminorms_pi {κ : ι -> Type*} {E : ι -> Type*} [fo
rall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpa
ce (E …
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `PointwiseConvergenceCLM.isInducing_inducingFn`：isInducing_inducingFn : T
opology.IsInducing (inducingFn σ E F)
-/
lemma withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F) :=
  let e : E ≃ (Σ _ : E, Fin 1) := .symm <| .sigmaUnique _ _
  (isInducing_inducingFn σ E F).withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ F)
    |>.congr_equiv e

section Tendsto

open Filter
open scoped Topology

/-
**PointwiseConvergenceCLM.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `PointwiseConve
rgenceCLM`。
形式化陈述：tendsto_nhds {f : Filter α} (u : α -> E ->SLₚₜ[σ] F) (y₀ : E ->SLₚₜ[σ] F) 
: Tendsto u f (𝓝 y₀) ↔ forall (x : E) (ε : Real), 0 < ε -> forallᶠ (k : α) in f,
 ‖u k x - y₀ x‖ < ε
参数：u : α -> E ->SLₚₜ[σ] F；y₀ : E ->SLₚₜ[σ] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.tendsto_nhds`：WithSeminorms.tendsto_nhds (hp : WithSeminor
ms p) (u : F -> E) {f : Filter F} (y₀ : E) : Filter.Tendsto u f (𝓝 y₀) ↔ forall 
i ε, 0 < ε -> fo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `PointwiseConvergenceCLM.withSeminorms`：withSeminorms : WithSeminorms (Po
intwiseConvergenceCLM.seminormFamily σ E F)
-/
theorem tendsto_nhds {f : Filter α} (u : α → E →SLₚₜ[σ] F) (y₀ : E →SLₚₜ[σ] F) :
    Tendsto u f (𝓝 y₀) ↔ ∀ (x : E) (ε : ℝ), 0 < ε → ∀ᶠ (k : α) in f, ‖u k x - y₀ x‖ < ε :=
  PointwiseConvergenceCLM.withSeminorms.tendsto_nhds _ _
/-
**PointwiseConvergenceCLM.tendsto_nhds_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Pointwis
eConvergenceCLM`。
形式化陈述：tendsto_nhds_atTop [SemilatticeSup α] [Nonempty α] (u : α -> E ->SLₚₜ[σ] F
) (y₀ : E ->SLₚₜ[σ] F) : Tendsto u atTop (𝓝 y₀) ↔ forall (x : E) (ε : Real), 0 <
 ε -> exists (k₀ : α), forall (k : α), k₀ <= k -> ‖u k x - y₀ x‖ < ε
参数：u : α -> E ->SLₚₜ[σ] F；y₀ : E ->SLₚₜ[σ] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.tendsto_nhds_atTop`：WithSeminorms.tendsto_nhds_atTop (hp :
 WithSeminorms p) (u : F -> E) (y₀ : E) : Filter.Tendsto u Filter.atTop (𝓝 y₀) ↔
 forall i ε, 0 < ε -> …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `PointwiseConvergenceCLM.withSeminorms`：withSeminorms : WithSeminorms (Po
intwiseConvergenceCLM.seminormFamily σ E F)
-/
theorem tendsto_nhds_atTop [SemilatticeSup α] [Nonempty α] (u : α → E →SLₚₜ[σ] F)
    (y₀ : E →SLₚₜ[σ] F) :
    Tendsto u atTop (𝓝 y₀) ↔
      ∀ (x : E) (ε : ℝ), 0 < ε → ∃ (k₀ : α), ∀ (k : α), k₀ ≤ k → ‖u k x - y₀ x‖ < ε :=
  PointwiseConvergenceCLM.withSeminorms.tendsto_nhds_atTop _ _

end Tendsto

section ContinuousLinearMap

variable [AddCommGroup D] [TopologicalSpace D] [Module 𝕜₃ D]
  [NormedAddCommGroup G] [NormedSpace 𝕜₂ G]

open NNReal ContinuousLinearMap

variable (F G) in
/-- Define a continuous linear map between `E →SLₚₜ[σ] F` and `D →SLₚₜ[τ] G`.

Use `PointwiseConvergenceCLM.precomp` for the special case of the adjoint operator. -/
/-
**PointwiseConvergenceCLM.mkCLM** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergenceC
LM`。
形式化陈述：mkCLM (A : (E ->SL[σ] F) ->ₗ[𝕜₂] D ->SL[τ] G) (hbound : forall (f : D), ex
ists (s : Finset E) (C : Real>=0), forall (B : E ->SL[σ] F), exists (g : E) (_hb
 : g in s), ‖(A B) f‖ <= C • ‖B g‖) : (E ->SLₚₜ[σ] F) ->L[𝕜₂] D ->SLₚₜ[τ] G wher
e __
参数：A : (E ->SL[σ] F) ->ₗ[𝕜₂] D ->SL[τ] G；hbound : forall (f : D), exists (s : Fi
nset E) (C : Real>=0), forall (B : E ->SL[σ] F), exists (g : E) (_hb : g in s), 
‖(A B) f‖ <= C • ‖B g‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a continuous linear map between `E →SLₚₜ[σ] F` and `D →SLₚₜ[τ] G`.

Use `PointwiseConvergenceCLM.precomp` for the special case of the adjoint operat
or.
-/
def mkCLM (A : (E →SL[σ] F) →ₗ[𝕜₂] D →SL[τ] G) (hbound : ∀ (f : D), ∃ (s : Finset E) (C : ℝ≥0),
  ∀ (B : E →SL[σ] F), ∃ (g : E) (_hb : g ∈ s), ‖(A B) f‖ ≤ C • ‖B g‖) :
    (E →SLₚₜ[σ] F) →L[𝕜₂] D →SLₚₜ[τ] G where
  __ := (toUniformConvergenceCLM _ _ _).toLinearMap.comp
    (A.comp (toUniformConvergenceCLM _ _ _).symm.toLinearMap)
  cont := by
    apply PointwiseConvergenceCLM.withSeminorms.continuous_of_isBounded
      PointwiseConvergenceCLM.withSeminorms A
    intro f
    obtain ⟨s, C, h⟩ := hbound f
    use s, C
    rw [← Seminorm.finset_sup_smul]
    intro B
    obtain ⟨g, h₁, h₂⟩ := h ((toUniformConvergenceCLM _ _ _).symm B)
    refine le_trans ?_ (Seminorm.le_finset_sup_apply h₁)
    exact h₂

end ContinuousLinearMap

end NormedSpace

section IsTopologicalAddGroup

variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜₂ F]
  [Semiring R] [PartialOrder R]
  [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/-
**PointwiseConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `PointwiseConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyConvexSpace R (E →SLₚₜ[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R {(s : Set E) | Set.Finite s} ⟨∅, Set.finite_empty⟩
    (directedOn_of_sup_mem fun _ _ => Set.Finite.union)

end IsTopologicalAddGroup

end PointwiseConvergenceCLM

