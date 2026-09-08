/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Algebraic operations on `SeparationQuotient`

In this file we construct a section of the quotient map `E → SeparationQuotient E` as a continuous
linear map `SeparationQuotient E →L[K] E`.
-/

@[expose] public section

open Topology

namespace SeparationQuotient
section VectorSpace

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul K E]

/-- There exists a continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`.

Note that continuity of this map comes for free, because `mk` is a topology inducing map.
-/
/-
**SeparationQuotient.exists_out_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `S
eparationQuotient`。
形式化陈述：exists_out_continuousLinearMap : exists f : SeparationQuotient E ->L[K] E,
 mkCLM K E ∘L f = .id K (SeparationQuotient E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.exists_rightInverse_of_surjective`：∀ {R : Type u_1} [inst : Se
miring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]
   {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g

--- 原说明 ---
There exists a continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`.

Note that continuity of this map comes for free, because `mk` is a topology indu
cing map.
-/
theorem exists_out_continuousLinearMap :
    ∃ f : SeparationQuotient E →L[K] E, mkCLM K E ∘L f = .id K (SeparationQuotient E) := by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, isInducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

/-- A continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`. -/
/-
**SeparationQuotient.outCLM** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：outCLM : SeparationQuotient E ->L[K] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.exists_out_continuousLinearMap`：exists_out_continuous
LinearMap : exists f : SeparationQuotient E ->L[K] E, mkCLM K E ∘L f = .id K (Se
parationQuotient E)

--- 原说明 ---
A continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`.
-/
noncomputable def outCLM : SeparationQuotient E →L[K] E :=
  (exists_out_continuousLinearMap K E).choose

@[simp]
/-
**SeparationQuotient.mkCLM_comp_outCLM** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuot
ient`。
形式化陈述：mkCLM_comp_outCLM : mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeparationQuotient.exists_out_continuousLinearMap`：exists_out_continuous
LinearMap : exists f : SeparationQuotient E ->L[K] E, mkCLM K E ∘L f = .id K (Se
parationQuotient E)
-/
theorem mkCLM_comp_outCLM : mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E) :=
  (exists_out_continuousLinearMap K E).choose_spec

variable {E} in
@[simp]
/-
**SeparationQuotient.mk_outCLM** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：mk_outCLM (x : SeparationQuotient E) : mk (outCLM K E x) = x
参数：x : SeparationQuotient E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeparationQuotient.mkCLM_comp_outCLM`：mkCLM_comp_outCLM : mkCLM K E ∘L o
utCLM K E = .id K (SeparationQuotient E)
-/
theorem mk_outCLM (x : SeparationQuotient E) : mk (outCLM K E x) = x :=
  DFunLike.congr_fun (mkCLM_comp_outCLM K E) x

@[simp]
/-
**SeparationQuotient.mk_comp_outCLM** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotien
t`。
形式化陈述：mk_comp_outCLM : mk ∘ outCLM K E = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeparationQuotient.mk_outCLM`：mk_outCLM (x : SeparationQuotient E) : mk 
(outCLM K E x) = x
-/
theorem mk_comp_outCLM : mk ∘ outCLM K E = id := funext (mk_outCLM K)

variable {K} in
/-
**SeparationQuotient.postcomp_mkCLM_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Separa
tionQuotient`。
形式化陈述：postcomp_mkCLM_surjective {L : Type*} [Semiring L] (σ : L ->+* K) (F : Typ
e*) [AddCommMonoid F] [Module L F] [TopologicalSpace F] : Function.Surjective ((
mkCLM K E).comp : (F ->SL[σ] E) -> (F ->SL[σ] SeparationQuotient E))
参数：σ : L ->+* K；F : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…
· 使用定理 `SeparationQuotient.mkCLM_comp_outCLM`：mkCLM_comp_outCLM : mkCLM K E ∘L o
utCLM K E = .id K (SeparationQuotient E)
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
-/
theorem postcomp_mkCLM_surjective {L : Type*} [Semiring L] (σ : L →+* K)
    (F : Type*) [AddCommMonoid F] [Module L F] [TopologicalSpace F] :
    Function.Surjective ((mkCLM K E).comp : (F →SL[σ] E) → (F →SL[σ] SeparationQuotient E)) := by
  intro f
  use (outCLM K E).comp f
  rw [← ContinuousLinearMap.comp_assoc, mkCLM_comp_outCLM, ContinuousLinearMap.id_comp]

/-- The `SeparationQuotient.outCLM K E` map is a topological embedding. -/
/-
**SeparationQuotient.isEmbedding_outCLM** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuo
tient`。
形式化陈述：isEmbedding_outCLM : IsEmbedding (outCLM K E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {g : Y → X},   F
unction.LeftInverse f …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeparationQuotient.mk_outCLM`：mk_outCLM (x : SeparationQuotient E) : mk 
(outCLM K E x) = x
· 使用定理 `SeparationQuotient.continuous_mk`：continuous_mk : Continuous (mk : X -> 
SeparationQuotient X)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…

--- 原说明 ---
The `SeparationQuotient.outCLM K E` map is a topological embedding.
-/
theorem isEmbedding_outCLM : IsEmbedding (outCLM K E) :=
  Function.LeftInverse.isEmbedding (mk_outCLM K) continuous_mk (map_continuous _)
/-
**SeparationQuotient.outCLM_injective** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：outCLM_injective : Function.Injective (outCLM K E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeparationQuotient.isEmbedding_outCLM`：isEmbedding_outCLM : IsEmbedding 
(outCLM K E)
-/
theorem outCLM_injective : Function.Injective (outCLM K E) :=
  (isEmbedding_outCLM K E).injective

end VectorSpace

section VectorSpaceUniform

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul K E]

@[fun_prop]
/-
**SeparationQuotient.outCLM_isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `Separat
ionQuotient`。
形式化陈述：outCLM_isUniformInducing : IsUniformInducing (outCLM K E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
· 使用定理 `SeparationQuotient.mk_comp_outCLM`：mk_comp_outCLM : mk ∘ outCLM K E = id
· 使用定理 `IsUniformInducing.id`：IsUniformInducing.id : IsUniformInducing (@id α)
-/
theorem outCLM_isUniformInducing : IsUniformInducing (outCLM K E) := by
  rw [← isUniformInducing_mk.of_comp_iff, mk_comp_outCLM]
  exact .id

@[fun_prop]
/-
**SeparationQuotient.outCLM_isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Separa
tionQuotient`。
形式化陈述：outCLM_isUniformEmbedding : IsUniformEmbedding (outCLM K E) where injectiv
e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `SeparationQuotient.outCLM_isUniformInducing`：outCLM_isUniformInducing : 
IsUniformInducing (outCLM K E)
· 使用定理 `SeparationQuotient.outCLM_injective`：outCLM_injective : Function.Injecti
ve (outCLM K E)
-/
theorem outCLM_isUniformEmbedding : IsUniformEmbedding (outCLM K E) where
  injective := outCLM_injective K E
  toIsUniformInducing := outCLM_isUniformInducing K E

@[fun_prop]
/-
**SeparationQuotient.outCLM_uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Separat
ionQuotient`。
形式化陈述：outCLM_uniformContinuous : UniformContinuous (outCLM K E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `SeparationQuotient.outCLM_isUniformInducing`：outCLM_isUniformInducing : 
IsUniformInducing (outCLM K E)
-/
theorem outCLM_uniformContinuous : UniformContinuous (outCLM K E) :=
  (outCLM_isUniformInducing K E).uniformContinuous

end VectorSpaceUniform
end SeparationQuotient

