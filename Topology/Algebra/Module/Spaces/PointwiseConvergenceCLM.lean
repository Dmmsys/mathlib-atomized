/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Topology of pointwise convergence on continuous linear maps

## Main definitions

* `PointwiseConvergenceCLM`: Type synonym of `E →SL[σ] F` equipped with the uniform convergence
  topology on finite sets.
* `PointwiseConvergenceCLM.evalCLM`: The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for fixed `a : E`
  as a continuous linear map.
* `ContinuousLinearMap.toPointwiseConvergenceCLM`: The canonical map from `E →SL[σ] F` to
  `E →SLₚₜ[σ] F` as a continuous linear map. This is the statement that bounded convergence is
  stronger than pointwise convergence.
* `PointwiseConvergenceCLM.equivWeakDual`: The continuous equivalence between `E →Lₚₜ[𝕜] 𝕜` and
  `WeakDual 𝕜 E`.

## Main statements

* `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto`: In the topology of pointwise convergence,
  `a` converges to `a₀` iff for every `x : E` the map `a · x` converges to `a₀ x`.
* `PointwiseConvergenceCLM.continuous_of_continuous_eval`: A map to `g : α → E →SLₚₜ[σ] F` is
  continuous if for every `x : E` the evaluation `g · x` is continuous.

## Notation

* `E →SLₚₜ[σ] F` is space of continuous linear maps equipped with pointwise convergence topology.

-/

@[expose] public section

/-! ### Topology of pointwise convergence -/

variable {α ι : Type*} [TopologicalSpace α]
variable {𝕜 𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜] [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
variable {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ]
variable {E F Fᵤ G : Type*} [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup Fᵤ] [UniformSpace Fᵤ] [IsUniformAddGroup Fᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 Fᵤ] [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₂ Fᵤ] [Module 𝕜₃ G]

open Set Topology

variable (σ E F) in
/-- The space of continuous linear maps equipped with the topology of pointwise convergence,
sometimes also called the *strong operator topology*. We avoid this terminology since so many other
things share similar names, and using "pointwise convergence" in the name is more informative.

This topology is also known as the weak⋆-topology in the case that `σ = RingHom.id 𝕜` and `F = 𝕜` -/
/-
**PointwiseConvergenceCLM** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PointwiseConvergenceCLM
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous linear maps equipped with the topology of pointwise conv
ergence,
sometimes also called the *strong operator topology*. We avoid this terminology 
since so many other
things share similar names, and using "pointwise convergence" in the name is mor
e informative.

This topology is also known as the weak⋆-topology in the case that `σ = RingHom.
id 𝕜` and `F = 𝕜`
-/
abbrev PointwiseConvergenceCLM := UniformConvergenceCLM σ F {s : Set E | Finite s}

@[inherit_doc]
notation:25 E " →SLₚₜ[" σ "] " F => PointwiseConvergenceCLM σ E F

@[inherit_doc]
notation:25 E " →Lₚₜ[" R "] " F => PointwiseConvergenceCLM (RingHom.id R) E F

namespace PointwiseConvergenceCLM

/-
**PointwiseConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `PointwiseConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space F] : T2Space (E →SLₚₜ[σ] F) :=
  UniformConvergenceCLM.t2Space _ _ _ Set.sUnion_finite_eq_univ
/-
**PointwiseConvergenceCLM.continuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `Pointwi
seConvergenceCLM`。
形式化陈述：continuousEvalConst : ContinuousEvalConst (E ->SLₚₜ[σ] F) E F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.continuousEvalConst`：continuousEvalConst [Topologi
calSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) :
 ContinuousEvalConst (E ->SLᵤ[σ…
· 使用定理 `Set.sUnion_finite_eq_univ`：sUnion_finite_eq_univ {X : Type*} : ⋃₀ {(s : 
Set X) | Set.Finite s} = Set.univ
-/
instance continuousEvalConst : ContinuousEvalConst (E →SLₚₜ[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst _ _ _ Set.sUnion_finite_eq_univ
/-
**PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间 
`PointwiseConvergenceCLM`。
形式化陈述：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type u_5} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_7}   {F : Type u_8} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : AddCommGroup F]   [inst_5 : Topologi
calSpace F] [inst_6 : IsTopologicalAddGroup F] [inst_7 : _root_.Module 𝕜₁ E]   [
inst_8 : _root_.Module 𝕜₂ F] {ι : Type u_11} {p : ι → Prop} {b : ι → Set F},   (
nhds 0).HasBasis p b → (nhds 0).HasBasis (fun Si => Finite ↑Si.1 ∧ p Si.2) fun S
i => {f | ∀ x ∈ Si.1, f x ∈ b Si.2}
参数：nhds 0；nhds 0；fun Si => Finite ↑Si.1 ∧ p Si.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero_of
_basis [TopologicalSpace F] [IsTopologicalAddGroup F] {ι : Type*} (𝔖 : Set (Set 
E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedO…
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `directedOn_of_sup_mem`：directedOn_of_sup_mem [SemilatticeSup α] {S : Set
 α} (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
protected theorem hasBasis_nhds_zero_of_basis
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SLₚₜ[σ] F)).HasBasis (fun Si : Set E × ι => Finite Si.1 ∧ p Si.2)
      fun Si => { f : E →SLₚₜ[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Finite S }
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => Set.Finite.union) h
/-
**PointwiseConvergenceCLM.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pointwis
eConvergenceCLM`。
形式化陈述：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type u_5} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_7}   {F : Type u_8} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : AddCommGroup F]   [inst_5 : Topologi
calSpace F] [inst_6 : IsTopologicalAddGroup F] [inst_7 : _root_.Module 𝕜₁ E]   [
inst_8 : _root_.Module 𝕜₂ F],   (nhds 0).HasBasis (fun SV => Finite ↑SV.1 ∧ SV.2
 ∈ nhds 0) fun SV => {f | ∀ x ∈ SV.1, f x ∈ SV.2}
参数：nhds 0；fun SV => Finite ↑SV.1 ∧ SV.2 ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis`：∀ {𝕜₁ : Type u_4} {
𝕜₂ : Type u_5} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
 {E : Type u_7}   {F : Type u_8} [inst_2 …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
protected theorem hasBasis_nhds_zero :
    (𝓝 (0 : E →SLₚₜ[σ] F)).HasBasis
      (fun SV : Set E × Set F => Finite SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SLₚₜ[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

variable (σ E Fᵤ) in
/-
**PointwiseConvergenceCLM.isUniformEmbedding_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `Po
intwiseConvergenceCLM`。
形式化陈述：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type u_5} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) (E : Type u_7)   (Fᵤ : Type u_9) [inst_2 : AddCommGrou
p E] [inst_3 : TopologicalSpace E] [inst_4 : AddCommGroup Fᵤ]   [inst_5 : Unifor
mSpace Fᵤ] [inst_6 : IsUniformAddGroup Fᵤ] [inst_7 : _root_.Module 𝕜₁ E]   [inst
_8 : _root_.Module 𝕜₂ Fᵤ], IsUniformEmbedding DFunLike.coe
参数：σ : 𝕜₁ →+* 𝕜₂；E : Type u_7；Fᵤ : Type u_9。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.comp`：IsUniformEmbedding.comp {g : β -> γ} (hg : IsUn
iformEmbedding g) {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformEmbedding 
(g ∘ f) where…
· 使用定理 `UniformOnFun.isUniformEmbedding_toFun_finite`：isUniformEmbedding_toFun_f
inite : IsUniformEmbedding (toFun _ : (α ->ᵤ[{s | s.Finite}] β) -> (α -> β))
· 使用定理 `UniformConvergenceCLM.isUniformEmbedding_coeFn`：isUniformEmbedding_coeFn
 [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformEmbedding (
α
-/
protected theorem isUniformEmbedding_coeFn :
    IsUniformEmbedding ((↑) : (E →SLₚₜ[σ] Fᵤ) → (E → Fᵤ)) :=
  (UniformOnFun.isUniformEmbedding_toFun_finite E Fᵤ).comp
    (UniformConvergenceCLM.isUniformEmbedding_coeFn σ Fᵤ _)

variable (σ E F) in
/-
**PointwiseConvergenceCLM.isEmbedding_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `Pointwise
ConvergenceCLM`。
形式化陈述：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type u_5} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) (E : Type u_7)   (F : Type u_8) [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : AddCommGroup F]   [inst_5 : Topologi
calSpace F] [inst_6 : IsTopologicalAddGroup F] [inst_7 : _root_.Module 𝕜₁ E]   [
inst_8 : _root_.Module 𝕜₂ F], Topology.IsEmbedding DFunLike.coe
参数：σ : 𝕜₁ →+* 𝕜₂；E : Type u_7；F : Type u_8。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `PointwiseConvergenceCLM.isUniformEmbedding_coeFn`：∀ {𝕜₁ : Type u_4} {𝕜₂ 
: Type u_5} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) (E
 : Type u_7)   (Fᵤ : Type u_9) [inst_2…
-/
protected theorem isEmbedding_coeFn : IsEmbedding ((↑) : (E →SLₚₜ[σ] F) → (E → F)) :=
  let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  PointwiseConvergenceCLM.isUniformEmbedding_coeFn σ E F |>.isEmbedding

/-- In the topology of pointwise convergence, `a` converges to `a₀` iff for every `x : E` the map
`a · x` converges to `a₀ x`. -/
/-
**PointwiseConvergenceCLM.tendsto_iff_forall_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `
PointwiseConvergenceCLM`。
形式化陈述：tendsto_iff_forall_tendsto {p : Filter ι} {a : ι -> E ->SLₚₜ[σ] F} {a₀ : E
 ->SLₚₜ[σ] F} : Filter.Tendsto a p (𝓝 a₀) ↔ forall x : E, Filter.Tendsto (a · x)
 p (𝓝 (a₀ x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `PointwiseConvergenceCLM.isEmbedding_coeFn`：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type 
u_5} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) (E : Type
 u_7)   (F : Type u_8) [inst_2 …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
In the topology of pointwise convergence, `a` converges to `a₀` iff for every `x
 : E` the map
`a · x` converges to `a₀ x`.
-/
theorem tendsto_iff_forall_tendsto {p : Filter ι} {a : ι → E →SLₚₜ[σ] F} {a₀ : E →SLₚₜ[σ] F} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ x : E, Filter.Tendsto (a · x) p (𝓝 (a₀ x)) := by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).tendsto_nhds_iff, tendsto_pi_nhds]

variable (σ E F) in
/-- Coercion from `E →SLₚₜ[σ] F` to `E →ₛₗ[σ] F` as a `𝕜₂`-linear map. -/
@[simps!]
/-
**PointwiseConvergenceCLM.coeLM** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergenceC
LM`。
形式化陈述：coeLM [ContinuousConstSMul 𝕜 F] : (E ->Lₚₜ[𝕜] F) ->ₗ[𝕜] E ->ₗ[𝕜] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `E →SLₚₜ[σ] F` to `E →ₛₗ[σ] F` as a `𝕜₂`-linear map.
-/
def coeLMₛₗ [ContinuousConstSMul 𝕜₂ F] : (E →SLₚₜ[σ] F) →ₗ[𝕜₂] E →ₛₗ[σ] F :=
  ContinuousLinearMap.coeLMₛₗ σ

variable (𝕜 E F) in
/-- Coercion from `E →Lₚₜ[𝕜] F` to `E →ₗ[𝕜] F` as a `𝕜`-linear map. -/
@[simps!]
/-
**PointwiseConvergenceCLM.coeLM** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergenceC
LM`。
形式化陈述：coeLM [ContinuousConstSMul 𝕜 F] : (E ->Lₚₜ[𝕜] F) ->ₗ[𝕜] E ->ₗ[𝕜] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `E →Lₚₜ[𝕜] F` to `E →ₗ[𝕜] F` as a `𝕜`-linear map.
-/
def coeLM [ContinuousConstSMul 𝕜 F] : (E →Lₚₜ[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F := ContinuousLinearMap.coeLM 𝕜

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
variable (σ F) in
/-- The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for `a : E` as a continuous linear map. -/
@[simps!]
/-
**PointwiseConvergenceCLM.evalCLM** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergenc
eCLM`。
形式化陈述：evalCLM [ContinuousConstSMul 𝕜₂ F] (a : E) : (E ->SLₚₜ[σ] F) ->L[𝕜₂] F whe
re toLinearMap
参数：a : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for `a : E` as a continuous linear
 map.
-/
def evalCLM [ContinuousConstSMul 𝕜₂ F] (a : E) : (E →SLₚₜ[σ] F) →L[𝕜₂] F where
  toLinearMap := (coeLMₛₗ σ E F).flip a
  cont := continuous_eval_const a

/-- A map to `E →SLₚₜ[σ] F` is continuous if for every `x : E` the evaluation `g · x` is
continuous. -/
/-
**PointwiseConvergenceCLM.continuous_of_continuous_eval** 是 Mathlib 中的一个定理，位于命名空
间 `PointwiseConvergenceCLM`。
形式化陈述：continuous_of_continuous_eval {g : α -> E ->SLₚₜ[σ] F} (h : forall x, Cont
inuous (g · x)) : Continuous g
参数：h : forall x, Continuous (g · x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `PointwiseConvergenceCLM.isEmbedding_coeFn`：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type 
u_5} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) (E : Type
 u_7)   (F : Type u_8) [inst_2 …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A map to `E →SLₚₜ[σ] F` is continuous if for every `x : E` the evaluation `g · x
` is
continuous.
-/
theorem continuous_of_continuous_eval {g : α → E →SLₚₜ[σ] F}
    (h : ∀ x, Continuous (g · x)) : Continuous g := by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous_iff, continuous_pi_iff, h]

variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map for the pointwise
convergence topology. -/
@[simps! apply]
/-
**PointwiseConvergenceCLM.precomp** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergenc
eCLM`。
形式化陈述：precomp [ContinuousConstSMul 𝕜₃ G] (L : E ->SL[σ] F) : (F ->SLₚₜ[τ] G) ->L
[𝕜₃] E ->SLₚₜ[ρ] G where toFun f
参数：L : E ->SL[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pre-composition by a *fixed* continuous linear map as a continuous linear map fo
r the pointwise
convergence topology.
-/
def precomp [ContinuousConstSMul 𝕜₃ G] (L : E →SL[σ] F) : (F →SLₚₜ[τ] G) →L[𝕜₃] E →SLₚₜ[ρ] G where
  toFun f := f.comp L
  __ := ContinuousLinearMap.precompUniformConvergenceCLM G {(S : Set E) | Finite S}
    {(S : Set F) | Finite S} L (fun S hS ↦ letI : Finite S := hS; Finite.Set.finite_image _ _)

variable (E) in
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map for the pointwise
convergence topology. -/
@[simps! apply]
/-
**PointwiseConvergenceCLM.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergen
ceCLM`。
形式化陈述：postcomp [ContinuousConstSMul 𝕜₂ F] [ContinuousConstSMul 𝕜₃ G] (L : F ->SL
[τ] G) : (E ->SLₚₜ[σ] F) ->SL[τ] E ->SLₚₜ[ρ] G where toFun f
参数：L : F ->SL[τ] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-composition by a *fixed* continuous linear map as a continuous linear map f
or the pointwise
convergence topology.
-/
def postcomp [ContinuousConstSMul 𝕜₂ F] [ContinuousConstSMul 𝕜₃ G] (L : F →SL[τ] G) :
    (E →SLₚₜ[σ] F) →SL[τ] E →SLₚₜ[ρ] G where
  toFun f := L.comp f
  __ := ContinuousLinearMap.postcompUniformConvergenceCLM {(S : Set E) | Finite S} L

variable (𝕜₂ σ E F) in
/-- The topology of bounded convergence is stronger than the topology of pointwise convergence. -/
@[simps!]
/-
**PointwiseConvergenceCLM._root_.ContinuousLinearMap.toPointwiseConvergenceCLM**
 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of bounded convergence is stronger than the topology of pointwise c
onvergence.
-/
def _root_.ContinuousLinearMap.toPointwiseConvergenceCLM [ContinuousSMul 𝕜₁ E]
    [ContinuousConstSMul 𝕜₂ F] : (E →SL[σ] F) →L[𝕜₂] (E →SLₚₜ[σ] F) where
  __ := LinearMap.id
  cont := _root_.ContinuousLinearMap.toUniformConvergenceCLM_continuous σ F _
    (fun _ ↦ Set.Finite.isVonNBounded)

variable (𝕜 E) in
/-- The topology of pointwise convergence on `E →Lₚₜ[𝕜] 𝕜` coincides with the weak-\* topology. -/
@[simps!]
/-
**PointwiseConvergenceCLM.equivWeakDual** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConv
ergenceCLM`。
形式化陈述：equivWeakDual : (E ->Lₚₜ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of pointwise convergence on `E →Lₚₜ[𝕜] 𝕜` coincides with the weak-\
* topology.
-/
def equivWeakDual : (E →Lₚₜ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  __ := LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)
  continuous_toFun :=
    WeakDual.continuous_of_continuous_eval (fun y ↦ (evalCLM _ 𝕜 y).continuous)
  continuous_invFun := continuous_of_continuous_eval (WeakBilin.eval_continuous _)

section Pi

variable {ι : Type*} (F : ι → Type*)
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜 (F i)]

variable (𝕜 E) in
/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →Lₚₜ[𝕜] F i` and `E →Lₚₜ[𝕜] Π i, F i`. -/
/-
**PointwiseConvergenceCLM.piEquivL** 是 Mathlib 中的一个定义，位于命名空间 `PointwiseConvergen
ceCLM`。
形式化陈述：piEquivL : (Π i, E ->Lₚₜ[𝕜] F i) ≃L[𝕜] (E ->Lₚₜ[𝕜] Π i, F i) where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →Lₚₜ[𝕜] F i` and `E →Lₚₜ[𝕜] Π i, F i`.
-/
def piEquivL :
    (Π i, E →Lₚₜ[𝕜] F i) ≃L[𝕜] (E →Lₚₜ[𝕜] Π i, F i) where
  toFun F := ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

@[simp]
/-
**PointwiseConvergenceCLM.piEquivL_apply** 是 Mathlib 中的一个引理，位于命名空间 `PointwiseCon
vergenceCLM`。
形式化陈述：piEquivL_apply (T : Π i, E ->Lₚₜ[𝕜] F i) (e : E) (i : ι) : piEquivL 𝕜 E F 
T e i = T i e
参数：T : Π i, E ->Lₚₜ[𝕜] F i；e : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
-/
lemma piEquivL_apply (T : Π i, E →Lₚₜ[𝕜] F i) (e : E) (i : ι) :
    piEquivL 𝕜 E F T e i = T i e := rfl

@[simp]
/-
**PointwiseConvergenceCLM.piEquivL_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pointwi
seConvergenceCLM`。
形式化陈述：piEquivL_symm_apply (T : E ->Lₚₜ[𝕜] Π i, F i) (e : E) (i : ι) : (piEquivL 
𝕜 E F).symm T i e = T e i
参数：T : E ->Lₚₜ[𝕜] Π i, F i；e : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
-/
lemma piEquivL_symm_apply (T : E →Lₚₜ[𝕜] Π i, F i) (e : E) (i : ι) :
    (piEquivL 𝕜 E F).symm T i e = T e i := rfl

end Pi

end PointwiseConvergenceCLM

