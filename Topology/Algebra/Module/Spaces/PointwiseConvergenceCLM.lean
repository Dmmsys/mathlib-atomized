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
variable {σ : 𝕜₁ ->+* 𝕜₂} {τ : 𝕜₂ ->+* 𝕜₃} {ρ : 𝕜₁ ->+* 𝕜₃} [RingHomCompTriple σ τ ρ]
variable {E F Fᵤ G : Type*} [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup Fᵤ] [UniformSpace Fᵤ] [IsUniformAddGroup Fᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 Fᵤ] [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₂ Fᵤ] [Module 𝕜₃ G]

open Set Topology

variable (σ E F) in
/--
Definition of `PointwiseConvergenceCLM` / `PointwiseConvergenceCLM` 的定义

English:
abbreviation PointwiseConvergenceCLM
  body: UniformConvergenceCLM σ F {s : Set E | Finite s}

@[inherit_doc]
notation:25 E " ->SLₚₜ[" σ "] " F => PointwiseConvergenceCLM σ E F

@[inherit_doc]
notation:25 E " ->Lₚₜ[" R "] " F => PointwiseConvergenceCLM (RingHom.id R) E F

中文:
缩写 PointwiseConvergenceCLM
  定义体: UniformConvergenceCLM σ F {s : Set E | Finite s}

@[inherit_doc]
notation:25 E " ->SLₚₜ[" σ "] " F => PointwiseConvergenceCLM σ E F

@[inherit_doc]
notation:25 E " ->Lₚₜ[" R "] " F => PointwiseConvergenceCLM (RingHom.id R) E F

Depends on / 依赖: Finite, UniformConvergenceCLM
-/
abbrev PointwiseConvergenceCLM := UniformConvergenceCLM σ F {s : Set E | Finite s}

@[inherit_doc]
notation:25 E " ->SLₚₜ[" σ "] " F => PointwiseConvergenceCLM σ E F

@[inherit_doc]
notation:25 E " ->Lₚₜ[" R "] " F => PointwiseConvergenceCLM (RingHom.id R) E F

namespace PointwiseConvergenceCLM

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: F] : T2Space (E ->SLₚₜ[σ] F)
  body: UniformConvergenceCLM.t2Space _ _ _ Set.sUnion_finite_eq_univ

中文:
实例 [T2空间
  签名: F] : T2空间 (E ->SLₚₜ[σ] F)
  定义体: UniformConvergenceCLM.t2Space _ _ _ Set.sUnion_finite_eq_univ

Depends on / 依赖: Set.sUnion_finite_eq_univ, UniformConvergenceCLM, UniformConvergenceCLM.t2Space, sUnion_finite_eq_univ, t2Space
-/
instance [T2Space F] : T2Space (E ->SLₚₜ[σ] F) :=
  UniformConvergenceCLM.t2Space _ _ _ Set.sUnion_finite_eq_univ

/--
Instance `continuousEvalConst` / 实例 `continuousEvalConst`

English:
instance continuousEvalConst
  signature: : ContinuousEvalConst (E ->SLₚₜ[σ] F) E F
  body: UniformConvergenceCLM.continuousEvalConst _ _ _ Set.sUnion_finite_eq_univ

中文:
实例 continuousEvalConst
  签名: : 余ntinuousEvalConst (E ->SLₚₜ[σ] F) E F
  定义体: UniformConvergenceCLM.continuousEvalConst _ _ _ Set.sUnion_finite_eq_univ

Depends on / 依赖: Set.sUnion_finite_eq_univ, UniformConvergenceCLM, UniformConvergenceCLM.continuousEvalConst, continuousEvalConst, sUnion_finite_eq_univ
-/
instance continuousEvalConst : ContinuousEvalConst (E ->SLₚₜ[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst _ _ _ Set.sUnion_finite_eq_univ

/--
theorem `hasBasis_nhds_zero_of_basis` / 定理 `hasBasis_nhds_zero_of_basis`

English:
theorem hasBasis_nhds_zero_of_basis
  proof: UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Finite S }
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => Set.Finite.union) h

中文:
定理 hasBasis_nhds_zero_of_basis
  证明: UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Finite S }
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => Set.Finite.union) h
-/
protected theorem hasBasis_nhds_zero_of_basis
    {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E ->SLₚₜ[σ] F)).HasBasis (fun Si : Set E × ι => Finite Si.1 ∧ p Si.2)
      fun Si => { f : E ->SLₚₜ[σ] F | forall x in Si.1, f x in b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | Finite S }
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => Set.Finite.union) h

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  proof: PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

中文:
定理 hasBasis_nhds_zero
  证明: PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets
-/
protected theorem hasBasis_nhds_zero :
    (𝓝 (0 : E ->SLₚₜ[σ] F)).HasBasis
      (fun SV : Set E × Set F => Finite SV.1 ∧ SV.2 in (𝓝 0 : Filter F))
      fun SV => { f : E ->SLₚₜ[σ] F | forall x in SV.1, f x in SV.2 } :=
  PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

variable (σ E Fᵤ) in
/--
theorem `isUniformEmbedding_coeFn` / 定理 `isUniformEmbedding_coeFn`

English:
theorem isUniformEmbedding_coeFn
  proof: (UniformOnFun.isUniformEmbedding_toFun_finite E Fᵤ).comp
    (UniformConvergenceCLM.isUniformEmbedding_coeFn σ Fᵤ _)

中文:
定理 isUniformEmbedding_coeFn
  证明: (UniformOnFun.isUniformEmbedding_toFun_finite E Fᵤ).comp
    (UniformConvergenceCLM.isUniformEmbedding_coeFn σ Fᵤ _)
-/
protected theorem isUniformEmbedding_coeFn :
    IsUniformEmbedding ((↑) : (E ->SLₚₜ[σ] Fᵤ) -> (E -> Fᵤ)) :=
  (UniformOnFun.isUniformEmbedding_toFun_finite E Fᵤ).comp
    (UniformConvergenceCLM.isUniformEmbedding_coeFn σ Fᵤ _)

variable (σ E F) in
/--
theorem `isEmbedding_coeFn` / 定理 `isEmbedding_coeFn`

English:
theorem isEmbedding_coeFn
  statement: IsEmbedding ((↑) : (E ->SLₚₜ[σ] F) -> (E -> F))
  proof: let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
.isEmbedding PointwiseConvergenceCLM.isUniformEmbedding_coeFn σ E F

中文:
定理 isEmbedding_coeFn
  结论: 是嵌入 ((↑) : (E ->SLₚₜ[σ] F) -> (E -> F))
  证明: let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
.isEmbedding PointwiseConvergenceCLM.isUniformEmbedding_coeFn σ E F
-/
protected theorem isEmbedding_coeFn : IsEmbedding ((↑) : (E ->SLₚₜ[σ] F) -> (E -> F)) :=
  let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
.isEmbedding PointwiseConvergenceCLM.isUniformEmbedding_coeFn σ E F

/--
theorem `tendsto_iff_forall_tendsto` / 定理 `tendsto_iff_forall_tendsto`

English:
theorem tendsto_iff_forall_tendsto
  given: {p : Filter ι} {a : ι -> E ->SLₚₜ[σ] F} {a₀ : E ->SLₚₜ[σ] F}
  proof: by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).tendsto_nhds_iff, tendsto_pi_nhds]

中文:
定理 tendsto_iff_对任意_tendsto
  条件: {p : 滤子 ι} {a : ι -> E ->SLₚₜ[σ] F} {a₀ : E ->SLₚₜ[σ] F}
  证明: by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).tendsto_nhds_iff, tendsto_pi_nhds]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.isEmbedding_coeFn, isEmbedding_coeFn, tendsto_nhds_iff, tendsto_pi_nhds
-/
theorem tendsto_iff_forall_tendsto {p : Filter ι} {a : ι -> E ->SLₚₜ[σ] F} {a₀ : E ->SLₚₜ[σ] F} :
    Filter.Tendsto a p (𝓝 a₀) ↔ forall x : E, Filter.Tendsto (a · x) p (𝓝 (a₀ x)) := by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).tendsto_nhds_iff, tendsto_pi_nhds]

variable (σ E F) in
/-- Coercion from `E →SLₚₜ[σ] F` to `E →ₛₗ[σ] F` as a `𝕜₂`-linear map. -/
@[simps!]
/--
Definition of `coeLMₛₗ` / `coeLMₛₗ` 的定义

English:
definition coeLMₛₗ
  signature: [ContinuousConstSMul 𝕜₂ F]
  body: ContinuousLinearMap.coeLMₛₗ σ

中文:
定义 coeLMₛₗ
  签名: [连续常数标量乘法 𝕜₂ F]
  定义体: ContinuousLinearMap.coeLMₛₗ σ

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeLM
-/
def coeLMₛₗ [ContinuousConstSMul 𝕜₂ F] : (E ->SLₚₜ[σ] F) ->ₗ[𝕜₂] E ->ₛₗ[σ] F :=
  ContinuousLinearMap.coeLMₛₗ σ

variable (𝕜 E F) in
/-- Coercion from `E →Lₚₜ[𝕜] F` to `E →ₗ[𝕜] F` as a `𝕜`-linear map. -/
@[simps!]
/--
Definition of `coeLM` / `coeLM` 的定义

English:
definition coeLM
  signature: [ContinuousConstSMul 𝕜 F]
  body: ContinuousLinearMap.coeLM 𝕜

#adaptation_note

中文:
定义 coeLM
  签名: [连续常数标量乘法 𝕜 F]
  定义体: ContinuousLinearMap.coeLM 𝕜

#adaptation_note

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeLM
-/
def coeLM [ContinuousConstSMul 𝕜 F] : (E ->Lₚₜ[𝕜] F) ->ₗ[𝕜] E ->ₗ[𝕜] F := ContinuousLinearMap.coeLM 𝕜

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
variable (σ F) in
/-- The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for `a : E` as a continuous linear map. -/
@[simps!]
/--
Definition of `evalCLM` / `evalCLM` 的定义

English:
definition evalCLM
  signature: [ContinuousConstSMul 𝕜₂ F] (a : E)
  body: (coeLMₛₗ σ E F).flip a
  cont := continuous_eval_const a

中文:
定义 evalCLM
  签名: [连续常数标量乘法 𝕜₂ F] (a : E)
  定义体: (coeLMₛₗ σ E F).flip a
  cont := continuous_eval_const a
-/
def evalCLM [ContinuousConstSMul 𝕜₂ F] (a : E) : (E ->SLₚₜ[σ] F) ->L[𝕜₂] F where
  toLinearMap := (coeLMₛₗ σ E F).flip a
  cont := continuous_eval_const a

/--
theorem `continuous_of_continuous_eval` / 定理 `continuous_of_continuous_eval`

English:
theorem continuous_of_continuous_eval
  statement: {g : α -> E ->SLₚₜ[σ] F}
  proof: by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous_iff, continuous_pi_iff, h]

中文:
定理 continuous_of_continuous_eval
  结论: {g : α -> E ->SLₚₜ[σ] F}
  证明: by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous_iff, continuous_pi_iff, h]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.isEmbedding_coeFn, continuous_iff, continuous_pi_iff, isEmbedding_coeFn
-/
theorem continuous_of_continuous_eval {g : α -> E ->SLₚₜ[σ] F}
    (h : forall x, Continuous (g · x)) : Continuous g := by
  simp [(PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous_iff, continuous_pi_iff, h]

variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map for the pointwise
convergence topology. -/
@[simps! apply]
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: [ContinuousConstSMul 𝕜₃ G] (L : E ->SL[σ] F)
  body: f.comp L
  __ := ContinuousLinearMap.precompUniformConvergenceCLM G {(S : Set E) | Finite S}
    {(S : Set F) | Finite S} L (fun S hS => letI : Finite S := hS; Finite.Set.finite_image _ _)

中文:
定义 precomp
  签名: [连续常数标量乘法 𝕜₃ G] (L : E ->SL[σ] F)
  定义体: f.comp L
  __ := ContinuousLinearMap.precompUniformConvergenceCLM G {(S : Set E) | Finite S}
    {(S : Set F) | Finite S} L (fun S hS => letI : Finite S := hS; Finite.Set.finite_image _ _)

Depends on / 依赖: f.comp
-/
def precomp [ContinuousConstSMul 𝕜₃ G] (L : E ->SL[σ] F) : (F ->SLₚₜ[τ] G) ->L[𝕜₃] E ->SLₚₜ[ρ] G where
  toFun f := f.comp L
  __ := ContinuousLinearMap.precompUniformConvergenceCLM G {(S : Set E) | Finite S}
    {(S : Set F) | Finite S} L (fun S hS => letI : Finite S := hS; Finite.Set.finite_image _ _)

variable (E) in
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map for the pointwise
convergence topology. -/
@[simps! apply]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: [ContinuousConstSMul 𝕜₂ F] [ContinuousConstSMul 𝕜₃ G] (L : F ->SL[τ] G)
  body: L.comp f
  __ := ContinuousLinearMap.postcompUniformConvergenceCLM {(S : Set E) | Finite S} L

中文:
定义 postcomp
  签名: [连续常数标量乘法 𝕜₂ F] [连续常数标量乘法 𝕜₃ G] (L : F ->SL[τ] G)
  定义体: L.comp f
  __ := ContinuousLinearMap.postcompUniformConvergenceCLM {(S : Set E) | Finite S} L

Depends on / 依赖: L.comp
-/
def postcomp [ContinuousConstSMul 𝕜₂ F] [ContinuousConstSMul 𝕜₃ G] (L : F ->SL[τ] G) :
    (E ->SLₚₜ[σ] F) ->SL[τ] E ->SLₚₜ[ρ] G where
  toFun f := L.comp f
  __ := ContinuousLinearMap.postcompUniformConvergenceCLM {(S : Set E) | Finite S} L

variable (𝕜₂ σ E F) in
/-- The topology of bounded convergence is stronger than the topology of pointwise convergence. -/
@[simps!]
/--
Definition of `_root_.ContinuousLinearMap.toPointwiseConvergenceCLM` / `_root_.ContinuousLinearMap.toPointwiseConvergenceCLM` 的定义

English:
definition _root_.ContinuousLinearMap.toPointwiseConvergenceCLM
  signature: [ContinuousSMul 𝕜₁ E]
  body: LinearMap.id
  cont := _root_.ContinuousLinearMap.toUniformConvergenceCLM_continuous σ F _
    (fun _ => Set.Finite.isVonNBounded)

中文:
定义 _root_.连续线性映射.toPointwiseConvergenceCLM
  签名: [连续标量乘法 𝕜₁ E]
  定义体: LinearMap.id
  cont := _root_.ContinuousLinearMap.toUniformConvergenceCLM_continuous σ F _
    (fun _ => Set.Finite.isVonNBounded)

Depends on / 依赖: LinearMap, LinearMap.id
-/
def _root_.ContinuousLinearMap.toPointwiseConvergenceCLM [ContinuousSMul 𝕜₁ E]
    [ContinuousConstSMul 𝕜₂ F] : (E ->SL[σ] F) ->L[𝕜₂] (E ->SLₚₜ[σ] F) where
  __ := LinearMap.id
  cont := _root_.ContinuousLinearMap.toUniformConvergenceCLM_continuous σ F _
    (fun _ => Set.Finite.isVonNBounded)

variable (𝕜 E) in
/-- The topology of pointwise convergence on `E →Lₚₜ[𝕜] 𝕜` coincides with the weak-\* topology. -/
@[simps!]
/--
Definition of `equivWeakDual` / `equivWeakDual` 的定义

English:
definition equivWeakDual
  signature: : (E ->Lₚₜ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  body: LinearEquiv.refl 𝕜 (E ->L[𝕜] 𝕜)
  continuous_toFun :=
    WeakDual.continuous_of_continuous_eval (fun y => (evalCLM _ 𝕜 y).continuous)
  continuous_invFun := continuous_of_continuous_eval (WeakBilin.eval_continuous _)

中文:
定义 equivWeakDual
  签名: : (E ->Lₚₜ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  定义体: LinearEquiv.refl 𝕜 (E ->L[𝕜] 𝕜)
  continuous_toFun :=
    WeakDual.continuous_of_continuous_eval (fun y => (evalCLM _ 𝕜 y).continuous)
  continuous_invFun := continuous_of_continuous_eval (WeakBilin.eval_continuous _)

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def equivWeakDual : (E ->Lₚₜ[𝕜] 𝕜) ≃L[𝕜] WeakDual 𝕜 E where
  __ := LinearEquiv.refl 𝕜 (E ->L[𝕜] 𝕜)
  continuous_toFun :=
    WeakDual.continuous_of_continuous_eval (fun y => (evalCLM _ 𝕜 y).continuous)
  continuous_invFun := continuous_of_continuous_eval (WeakBilin.eval_continuous _)

section Pi

variable {ι : Type*} (F : ι -> Type*)
  [forall i, AddCommGroup (F i)] [forall i, Module 𝕜 (F i)] [forall i, TopologicalSpace (F i)]
  [forall i, IsTopologicalAddGroup (F i)] [forall i, ContinuousConstSMul 𝕜 (F i)]

variable (𝕜 E) in
/--
Definition of `piEquivL` / `piEquivL` 的定义

English:
definition piEquivL
  signature: :
  body: ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

@[simp]

中文:
定义 piEquivL
  签名: :
  定义体: ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.pi
-/
def piEquivL :
    (Π i, E ->Lₚₜ[𝕜] F i) ≃L[𝕜] (E ->Lₚₜ[𝕜] Π i, F i) where
  toFun F := ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

@[simp]
/--
lemma `piEquivL_apply` / 引理 `piEquivL_apply`

English:
lemma piEquivL_apply
  given: (T : Π i, E ->Lₚₜ[𝕜] F i) (e : E) (i : ι)
  proof: rfl

@[simp]

中文:
引理 piEquivL_apply
  条件: (T : Π i, E ->Lₚₜ[𝕜] F i) (e : E) (i : ι)
  证明: rfl

@[simp]
-/
lemma piEquivL_apply (T : Π i, E ->Lₚₜ[𝕜] F i) (e : E) (i : ι) :
    piEquivL 𝕜 E F T e i = T i e := rfl

@[simp]
/--
lemma `piEquivL_symm_apply` / 引理 `piEquivL_symm_apply`

English:
lemma piEquivL_symm_apply
  given: (T : E ->Lₚₜ[𝕜] Π i, F i) (e : E) (i : ι)
  proof: rfl

中文:
引理 piEquivL_symm_apply
  条件: (T : E ->Lₚₜ[𝕜] Π i, F i) (e : E) (i : ι)
  证明: rfl
-/
lemma piEquivL_symm_apply (T : E ->Lₚₜ[𝕜] Π i, F i) (e : E) (i : ι) :
    (piEquivL 𝕜 E F).symm T i e = T e i := rfl

end Pi

end PointwiseConvergenceCLM
