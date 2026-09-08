/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov, Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM

/-!
# Topology of compact convergence on the space of continuous linear maps

In this file, we define a type alias `CompactConvergenceCLM` for `E →L[𝕜] F`,
endowed with the topology of uniform convergence on compact subsets.

More concretely, `CompactConvergenceCLM` is an abbreviation for
`UniformConvergenceCLM σ F {(S : Set E) | IsCompact S}`. We denote it by `E →SL_c[σ] F`.

Here is a list of type aliases for `E →L[𝕜] F` endowed with various topologies :
* `ContinuousLinearMap`: topology of bounded convergence
* `UniformConvergenceCLM`: topology of `𝔖`-convergence, for a general `𝔖 : Set (Set E)`
* `CompactConvergenceCLM`: topology of compact convergence
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-\* topology"
  or "strong-operator topology" depending on the context
* `ContinuousLinearMapWOT`: topology of weak pointwise convergence, also called "weak-operator
  topology"

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

@[expose] public section

open Bornology Filter Function Set Topology ContinuousLinearMap
open scoped UniformConvergence Uniformity

section CompactSets

/-! ### Topology of compact convergence for continuous linear maps -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*}
  [AddCommGroup E] [Module 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G]

variable (E F σ) in
/-- The topology of compact convergence on `E →L[𝕜] F`. -/
/-
**CompactConvergenceCLM** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CompactConvergenceCLM [TopologicalSpace E] [TopologicalSpace F]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of compact convergence on `E →L[𝕜] F`.
-/
abbrev CompactConvergenceCLM [TopologicalSpace E] [TopologicalSpace F] :=
  UniformConvergenceCLM σ F {S : Set E | IsCompact S}

@[inherit_doc]
scoped[CompactConvergenceCLM]
notation:25 E " →SL_c[" σ "] " F => CompactConvergenceCLM σ E F

@[inherit_doc]
scoped[CompactConvergenceCLM]
notation:25 E " →L_c[" R "] " F => CompactConvergenceCLM (RingHom.id R) E F

namespace CompactConvergenceCLM

/-
**CompactConvergenceCLM.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `CompactConverg
enceCLM`。
形式化陈述：continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpac
e E] [IsTopologicalAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F] [C
ontinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E ->SL_c[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.continuousSMul`：continuousSMul [RingHomSurjective 
σ] [RingHomIsometric σ] [TopologicalSpace F] [IsTopologicalAddGroup F] [Continuo
usSMul 𝕜₂ F] (𝔖 : Set (Set…
· 使用定理 `IsCompact.isVonNBounded`：IsCompact.isVonNBounded [NormedField 𝕜] [AddCom
mGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Continuou
sSMul 𝕜 E] {s…
-/
instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] :
    ContinuousSMul 𝕜₂ (E →SL_c[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsCompact S }
    (fun _ hs => hs.isVonNBounded 𝕜₁)
/-
**CompactConvergenceCLM.instContinuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `Compa
ctConvergenceCLM`。
形式化陈述：instContinuousEvalConst [TopologicalSpace E] [TopologicalSpace F] [IsTopol
ogicalAddGroup F] : ContinuousEvalConst (E ->SL_c[σ] F) E F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.continuousEvalConst`：continuousEvalConst [Topologi
calSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) :
 ContinuousEvalConst (E ->SLᵤ[σ…
· 使用定理 `Set.sUnion_isCompact_eq_univ`：∀ {X : Type u} [inst : TopologicalSpace X]
, ⋃₀ {s | IsCompact s} = Set.univ
-/
instance instContinuousEvalConst [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup F] : ContinuousEvalConst (E →SL_c[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst σ F _ sUnion_isCompact_eq_univ
/-
**CompactConvergenceCLM.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `CompactConvergenc
eCLM`。
形式化陈述：instT2Space [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGro
up F] [T2Space F] : T2Space (E ->SL_c[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.t2Space`：t2Space [TopologicalSpace F] [IsTopologic
alAddGroup F] [T2Space F] (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = univ) : T2Space (E ->SL
ᵤ[σ, 𝔖] F)
· 使用定理 `Set.sUnion_isCompact_eq_univ`：∀ {X : Type u} [inst : TopologicalSpace X]
, ⋃₀ {s | IsCompact s} = Set.univ
-/
instance instT2Space [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [T2Space F] : T2Space (E →SL_c[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _ sUnion_isCompact_eq_univ
/-
**CompactConvergenceCLM.hasBasis_nhds_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `C
ompactConvergenceCLM`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_4}   {F : Type u_5} [inst_2 : AddCommGroup
 E] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.M
odule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F]   [inst_
8 : IsTopologicalAddGroup F] {ι : Type u_7} {p : ι → Prop} {b : ι → Set F},   (n
hds 0).HasBasis p b → (nhds 0).HasBasis (fun Si => IsCompact Si.1 ∧ p Si.2) fun 
Si => {f | ∀ x ∈ Si.1, f x ∈ b Si.2}
参数：nhds 0；nhds 0；fun Si => IsCompact Si.1 ∧ p Si.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero_of
_basis [TopologicalSpace F] [IsTopologicalAddGroup F] {ι : Type*} (𝔖 : Set (Set 
E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedO…
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `directedOn_of_sup_mem`：directedOn_of_sup_mem [SemilatticeSup α] {S : Set
 α} (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
-/
protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL_c[σ] F)).HasBasis (fun Si : Set E × ι => IsCompact Si.1 ∧ p Si.2)
      fun Si => { f : E →SL_c[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsCompact S }
    ⟨∅, isCompact_empty⟩
    (directedOn_of_sup_mem fun _ _ => IsCompact.union) h
/-
**CompactConvergenceCLM.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `CompactCon
vergenceCLM`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_4}   {F : Type u_5} [inst_2 : AddCommGroup
 E] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.M
odule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F]   [inst_
8 : IsTopologicalAddGroup F],   (nhds 0).HasBasis (fun SV => IsCompact SV.1 ∧ SV
.2 ∈ nhds 0) fun SV => {f | ∀ x ∈ SV.1, f x ∈ SV.2}
参数：nhds 0；fun SV => IsCompact SV.1 ∧ SV.2 ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactConvergenceCLM.hasBasis_nhds_zero_of_basis`：∀ {𝕜₁ : Type u_1} {𝕜₂
 : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {
E : Type u_4}   {F : Type u_5} [inst_2 …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
protected theorem hasBasis_nhds_zero [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup F] :
    (𝓝 (0 : E →SL_c[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsCompact SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL_c[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  CompactConvergenceCLM.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

end CompactConvergenceCLM

section comp

variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

open scoped CompactConvergenceCLM

variable (G) in
/-- Specialization of `ContinuousLinearMap.precomp_uniformConvergenceCLM` to compact
convergence. -/
@[simps! apply]
/-
**ContinuousLinearMap.precompCompactConvergenceCLM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.precompCompactConvergenceCLM [IsTopologicalAddGroup G]
 [ContinuousConstSMul 𝕜₃ G] (L : E ->SL[σ] F) : (F ->SL_c[τ] G) ->L[𝕜₃] E ->SL_c
[ρ] G
参数：L : E ->SL[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialization of `ContinuousLinearMap.precomp_uniformConvergenceCLM` to compact
convergence.
-/
def ContinuousLinearMap.precompCompactConvergenceCLM [IsTopologicalAddGroup G]
    [ContinuousConstSMul 𝕜₃ G] (L : E →SL[σ] F) : (F →SL_c[τ] G) →L[𝕜₃] E →SL_c[ρ] G :=
  L.precompUniformConvergenceCLM G _ _ (fun _ hs ↦ hs.image L.continuous)

@[deprecated (since := "2026-01-27")]
alias precomp_compactConvergenceCLM := precompCompactConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias precomp_compactConvergenceCLM_apply := precompCompactConvergenceCLM_apply

variable (E) in
/-- Specialization of `ContinuousLinearMap.postcomp_uniformConvergenceCLM` to compact
convergence. -/
@[simps! apply]
/-
**ContinuousLinearMap.postcompCompactConvergenceCLM** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：ContinuousLinearMap.postcompCompactConvergenceCLM [IsTopologicalAddGroup F
] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F
] (L : F ->SL[τ] G) : (E ->SL_c[σ] F) ->SL[τ] E ->SL_c[ρ] G
参数：L : F ->SL[τ] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialization of `ContinuousLinearMap.postcomp_uniformConvergenceCLM` to compac
t
convergence.
-/
def ContinuousLinearMap.postcompCompactConvergenceCLM [IsTopologicalAddGroup F]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F]
    (L : F →SL[τ] G) : (E →SL_c[σ] F) →SL[τ] E →SL_c[ρ] G :=
  L.postcompUniformConvergenceCLM _

@[deprecated (since := "2026-01-27")]
alias postcomp_compactConvergenceCLM := postcompCompactConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias postcomp_compactConvergenceCLM_apply := postcompCompactConvergenceCLM_apply

end comp

/-! ### Continuous linear equivalences -/

section Pi

open scoped CompactConvergenceCLM

variable [TopologicalSpace E] {ι : Type*} (F : ι → Type*)
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜₁ (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜₁ (F i)]

variable (𝕜₁ E) in
/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →L_c[𝕜] F i` and `E →L_c[𝕜] Π i, F i`. -/
/-
**CompactConvergenceCLM.piEquivL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompactConvergenceCLM.piEquivL : (Π i, E ->L_c[𝕜₁] F i) ≃L[𝕜₁] (E ->L_c[𝕜₁
] Π i, F i) where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →L_c[𝕜] F i` and `E →L_c[𝕜] Π i, F i`.
-/
def CompactConvergenceCLM.piEquivL :
    (Π i, E →L_c[𝕜₁] F i) ≃L[𝕜₁] (E →L_c[𝕜₁] Π i, F i) where
  toFun F := ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

@[simp]
/-
**CompactConvergenceCLM.piEquivL_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompactConvergenceCLM.piEquivL_apply (T : Π i, E ->L_c[𝕜₁] F i) (e : E) (i
 : ι) : piEquivL 𝕜₁ E F T e i = T i e
参数：T : Π i, E ->L_c[𝕜₁] F i；e : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
-/
lemma CompactConvergenceCLM.piEquivL_apply
    (T : Π i, E →L_c[𝕜₁] F i) (e : E) (i : ι) :
    piEquivL 𝕜₁ E F T e i = T i e :=
  rfl

@[simp]
/-
**CompactConvergenceCLM.piEquivL_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompactConvergenceCLM.piEquivL_symm_apply (T : E ->L_c[𝕜₁] Π i, F i) (e : 
E) (i : ι) : (piEquivL 𝕜₁ E F).symm T i e = T e i
参数：T : E ->L_c[𝕜₁] Π i, F i；e : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
-/
lemma CompactConvergenceCLM.piEquivL_symm_apply
    (T : E →L_c[𝕜₁] Π i, F i) (e : E) (i : ι) :
    (piEquivL 𝕜₁ E F).symm T i e = T e i :=
  rfl

end Pi

namespace ContinuousLinearEquiv

open scoped CompactConvergenceCLM

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₄ H]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. This version is for the type alias
`CompactConvergenceCLM`. -/
/-
**ContinuousLinearEquiv.compactConvergenceCLMCongrSL** 是 Mathlib 中的一个定义，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：compactConvergenceCLMCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) : (
E ->SL_c[σ₁₄] H) ≃SL[σ₄₃] (F ->SL_c[σ₂₃] G)
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous (semi)linear equivalences generates a (semi)linear equivale
nce between the
spaces of continuous (semi)linear maps. This version is for the type alias
`CompactConvergenceCLM`.
-/
def compactConvergenceCLMCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E →SL_c[σ₁₄] H) ≃SL[σ₄₃] (F →SL_c[σ₂₃] G) :=
  ContinuousLinearEquiv.uniformConvergenceCLMCongrSL e₁₂ e₄₃ _ _ fun s ↦ by
    simp [← e₁₂.toHomeomorph.isCompact_preimage]

@[simp]
/-
**ContinuousLinearEquiv.compactConvergenceCLMCongrSL_apply** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：compactConvergenceCLMCongrSL_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] 
G) (φ : E ->SL_c[σ₁₄] H) (f : F) : compactConvergenceCLMCongrSL e₁₂ e₄₃ φ f = e₄
₃ (φ (e₁₂.symm f))
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G；φ : E ->SL_c[σ₁₄] H；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compactConvergenceCLMCongrSL_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (φ : E →SL_c[σ₁₄] H) (f : F) :
    compactConvergenceCLMCongrSL e₁₂ e₄₃ φ f = e₄₃ (φ (e₁₂.symm f)) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.compactConvergenceCLMCongrSL_symm_apply** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：compactConvergenceCLMCongrSL_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[
σ₄₃] G) (φ : F ->SL_c[σ₂₃] G) (e : E) : (compactConvergenceCLMCongrSL e₁₂ e₄₃).s
ymm φ e = e₄₃.symm (φ (e₁₂ e))
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G；φ : F ->SL_c[σ₂₃] G；e : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compactConvergenceCLMCongrSL_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (φ : F →SL_c[σ₂₃] G) (e : E) :
    (compactConvergenceCLMCongrSL e₁₂ e₄₃).symm φ e = e₄₃.symm (φ (e₁₂ e)) :=
  rfl

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*}
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. This version is for the type alias
`CompactConvergenceCLM`. -/
/-
**ContinuousLinearEquiv.compactConvergenceCLMCongr** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousLinearEquiv`。
形式化陈述：compactConvergenceCLMCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E ->L_c[𝕜]
 H) ≃L[𝕜] (F ->L_c[𝕜] G)
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous linear equivalences generates a continuous linear equivalen
ce between
the spaces of continuous linear maps. This version is for the type alias
`CompactConvergenceCLM`.
-/
def compactConvergenceCLMCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (E →L_c[𝕜] H) ≃L[𝕜] (F →L_c[𝕜] G) :=
  e₁.compactConvergenceCLMCongrSL e₂

@[simp]
/-
**ContinuousLinearEquiv.compactConvergenceCLMCongr_apply** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousLinearEquiv`。
形式化陈述：compactConvergenceCLMCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (φ : E 
->L_c[𝕜] H) (f : F) : compactConvergenceCLMCongr e₁ e₂ φ f = e₂ (φ (e₁.symm f))
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；φ : E ->L_c[𝕜] H；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compactConvergenceCLMCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (φ : E →L_c[𝕜] H) (f : F) :
    compactConvergenceCLMCongr e₁ e₂ φ f = e₂ (φ (e₁.symm f)) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.compactConvergenceCLMCongr_symm_apply** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：compactConvergenceCLMCongr_symm_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (φ
 : F ->L_c[𝕜] G) (e : E) : (compactConvergenceCLMCongr e₁ e₂).symm φ e = e₂.symm
 (φ (e₁ e))
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；φ : F ->L_c[𝕜] G；e : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compactConvergenceCLMCongr_symm_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (φ : F →L_c[𝕜] G) (e : E) :
    (compactConvergenceCLMCongr e₁ e₂).symm φ e = e₂.symm (φ (e₁ e)) :=
  rfl

end Linear

end ContinuousLinearEquiv

end CompactSets

