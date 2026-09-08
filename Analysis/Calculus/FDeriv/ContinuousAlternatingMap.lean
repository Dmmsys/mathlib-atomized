/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Derivatives of operations on continuous alternating maps

In this file we prove formulas for the derivatives of

- `ContinuousAlternatingMap.compContinuousLinearMap`, the pullback of a continuous alternating map
  along a continuous linear map;
- application of a `ContinuousAlternatingMap` as a function of both the map and the vectors.
-/

public section

variable {𝕜 ι E F G H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

open ContinuousAlternatingMap
open scoped Topology

section CompContinuousLinearMap

variable
  {f : E → G [⋀^ι]→L[𝕜] H} {f' : E →L[𝕜] G [⋀^ι]→L[𝕜] H}
  {g : E → F →L[𝕜] G} {g' : E →L[𝕜] F →L[𝕜] G}
  {s : Set E} {x : E}

/-!
### Derivative of the pullback

In this section we prove a formula for the derivative
of the pullback of a continuous alternating map along a continuous linear map,
as a function of both maps.
-/

/-
**ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff
** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp
_iff [Finite ι] : HasStrictFDerivAt (toContinuousMultilinearMap ∘ f) (toContinuo
usMultilinearMapCLM 𝕜 ∘L f') x ↔ HasStrictFDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasStrictFDerivAt_iff_isLittleOTVS`：hasStrictFDerivAt_iff_isLittleOTVS :
 HasStrictFDerivAt f f' x ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; 𝓝 (x
, x)] (fun p => p.1 - p.…
· 使用定理 `Asymptotics.IsBigOTVS.trans_isLittleOTVS`：∀ {α : Type u_1} {𝕜 : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : AddCommGroup E] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply`：∀ {𝕜 : Typ
e u_1} {E : Type u_2} {F : Type u_3} {ι : Type u_4} [inst : NormedField 𝕜] [inst
_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `LinearMap.isBigOTVS_rev_comp`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type 
u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup 
E] [inst_2 : Topol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap`：isEmbed
ding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilinearMap : (E [
⋀^ι]->L[𝕜] F -> _))
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…

--- 原说明 ---
### Derivative of the pullback

In this section we prove a formula for the derivative
of the pullback of a continuous alternating map along a continuous linear map,
as a function of both maps.
-/
theorem ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff [Finite ι] :
    HasStrictFDerivAt (toContinuousMultilinearMap ∘ f) (toContinuousMultilinearMapCLM 𝕜 ∘L f') x ↔
      HasStrictFDerivAt f f' x := by
  cases nonempty_fintype ι
  constructor <;> intro h
  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
    simp only [Function.comp_apply, ← toContinuousMultilinearMapCLM_apply 𝕜,
      ContinuousLinearMap.comp_apply, ← map_sub]
    apply LinearMap.isBigOTVS_rev_comp
    simp [isEmbedding_toContinuousMultilinearMap.nhds_eq_comap]
  · exact (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x h

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

/-
**ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap (fg : (
G [⋀^ι]->L[𝕜] H) × (F ->L[𝕜] G)) : HasStrictFDerivAt (fun fg : (G [⋀^ι]->L[𝕜] H)
 × (F ->L[𝕜] G) => fg.1.compContinuousLinearMap fg.2) (compContinuousLinearMapCL
M fg.2 ∘L .fst _ _ _ + fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _) fg
参数：fg : (G [⋀^ι]->L[𝕜] H) × (F ->L[𝕜] G)。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_co
mp_iff`：ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_co
mp_iff [Finite ι] : HasStrictFDerivAt (toContinuousMultilinearMap ∘ …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (fg : ContinuousM
ultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i) : HasStr…
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictFDerivAt.prodMap`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type u_…
-/
theorem ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : (G [⋀^ι]→L[𝕜] H) × (F →L[𝕜] G)) :
    HasStrictFDerivAt
      (fun fg : (G [⋀^ι]→L[𝕜] H) × (F →L[𝕜] G) ↦ fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapCLM fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι ↦ fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι ↦ hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)
/-
**HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hf : Ha
sStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (fun
 x => (f x).compContinuousLinearMap (g x)) (compContinuousLinearMapCLM (g x) ∘L 
f' + (f x).fderivCompContinuousLinearMap (g x) ∘L g') x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x。
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
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap (fg : (G [⋀^ι]->L
[𝕜] H) × (F ->L[𝕜] G)) : HasStrictFDerivAt (fun fg : (G …
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, g x) |>.comp x (hf.prodMk hg)
/-
**HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hf : HasFDeri
vAt f f' x) (hg : HasFDerivAt g g' x) : HasFDerivAt (fun x => (f x).compContinuo
usLinearMap (g x)) (compContinuousLinearMapCLM (g x) ∘L f' + (f x).fderivCompCon
tinuousLinearMap (g x) ∘L g') x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x。
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap (fg : (G [⋀^ι]->L
[𝕜] H) × (F ->L[𝕜] G)) : HasStrictFDerivAt (fun fg : (G …
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt |>.comp x (hf.prodMk hg)
/-
**HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hf : Ha
sFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt 
(fun x => (f x).compContinuousLinearMap (g x)) (compContinuousLinearMapCLM (g x)
 ∘L f' + (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x。
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap`：Cont
inuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap (fg : (G [⋀^ι]->L
[𝕜] H) × (F ->L[𝕜] G)) : HasStrictFDerivAt (fun fg : (G …
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt |>.comp_hasFDerivWithinAt
      x (hf.prodMk hg)
/-
**fderivWithin_continuousAlternatingMapCompContinuousLinearMap** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：fderivWithin_continuousAlternatingMapCompContinuousLinearMap (hf : Differe
ntiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) (hs : UniqueDiffW
ithinAt 𝕜 s x) : fderivWithin 𝕜 (fun x => (f x).compContinuousLinearMap (g x)) s
 x = compContinuousLinearMapCLM (g x) ∘L fderivWithin 𝕜 f s x + (f x).fderivComp
ContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x；hs : 
UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap`：HasFD
erivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hf : HasFDerivWith
inAt f f' s x) (hg : HasFDerivWithinAt g g' s x) : HasF…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x =
      compContinuousLinearMapCLM (g x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
    |>.fderivWithin hs
/-
**fderiv_continuousAlternatingMapCompContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：fderiv_continuousAlternatingMapCompContinuousLinearMap (hf : Differentiabl
eAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : fderiv 𝕜 (fun x => (f x).compContinuo
usLinearMap (g x)) x = compContinuousLinearMapCLM (g x) ∘L fderiv 𝕜 f x + (f x).
fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap`：HasFDerivAt
.continuousAlternatingMapCompContinuousLinearMap (hf : HasFDerivAt f f' x) (hg :
 HasFDerivAt g g' x) : HasFDerivAt (fun x => (f x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x =
      compContinuousLinearMapCLM (g x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x :=
  hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt) |>.fderiv

end HasFDerivAt

/-!
### Differentiability of the pullback

In this section we prove that the pullback of a continuous alternating map
along a continuous linear map is differentiable with respect to a parameter,
provided that both maps are differentiable.
-/

variable [Finite ι]

/-
**DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap (hf
 : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : Diffe
rentiableWithinAt 𝕜 (fun x => (f x).compContinuousLinearMap (g x)) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap`：HasFD
erivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hf : HasFDerivWith
inAt f f' s x) (hg : HasFDerivWithinAt g g' s x) : HasF…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivWithinAt
    |>.differentiableWithinAt
/-
**DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap (hf : Dif
ferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (fun x =
> (f x).compContinuousLinearMap (g x)) x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap`：HasFDerivAt
.continuousAlternatingMapCompContinuousLinearMap (hf : HasFDerivAt f f' x) (hg :
 HasFDerivAt g g' x) : HasFDerivAt (fun x => (f x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivAt
    |>.differentiableAt

end CompContinuousLinearMap

/-!
### Derivative of a continuous alternating map applied to a tuple of vectors

In this section we prove the formula for the derivative `D_xf(x; g_0(x), ..., g_n(x))`.
-/

section Apply

variable {f : E → F [⋀^ι]→L[𝕜] G} {f' : E →L[𝕜] F [⋀^ι]→L[𝕜] G}
  {g : ι → E → F} {g' : ι → E →L[𝕜] F}
  {s : Set E} {x : E}

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

namespace ContinuousAlternatingMap

/-
**ContinuousAlternatingMap.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：hasStrictFDerivAt (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E) : HasStrictFDerivAt f
 (f.1.linearDeriv x) x
参数：f : E [⋀^ι]->L[𝕜] F；x : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 :
 NormedSpace 𝕜 F] {ι : Type u_2}…
-/
theorem hasStrictFDerivAt (f : E [⋀^ι]→L[𝕜] F) (x : ι → E) :
    HasStrictFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasStrictFDerivAt x
/-
**ContinuousAlternatingMap.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：hasFDerivAt (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E) : HasFDerivAt f (f.1.linear
Deriv x) x
参数：f : E [⋀^ι]->L[𝕜] F；x : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : Norme
dSpace 𝕜 F] {ι : Type u_2}…
-/
theorem hasFDerivAt (f : E [⋀^ι]→L[𝕜] F) (x : ι → E) : HasFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasFDerivAt x
/-
**ContinuousAlternatingMap.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：hasFDerivWithinAt (f : E [⋀^ι]->L[𝕜] F) (s : Set (ι -> E)) (x : ι -> E) : 
HasFDerivWithinAt f (f.1.linearDeriv x) s x
参数：f : E [⋀^ι]->L[𝕜] F；s : Set (ι -> E)；x : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAlternatingMap.hasFDerivAt`：hasFDerivAt (f : E [⋀^ι]->L[𝕜] F) 
(x : ι -> E) : HasFDerivAt f (f.1.linearDeriv x) x
-/
theorem hasFDerivWithinAt (f : E [⋀^ι]→L[𝕜] F) (s : Set (ι → E)) (x : ι → E) :
    HasFDerivWithinAt f (f.1.linearDeriv x) s x :=
  (f.hasFDerivAt x).hasFDerivWithinAt

end ContinuousAlternatingMap

/-
**HasStrictFDerivAt.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.continuousAlternatingMap_apply (hf : HasStrictFDerivAt f
 f' x) (hg : forall i, HasStrictFDerivAt (g i) (g' i) x) : HasStrictFDerivAt (fu
n x => f x (g · x)) (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMa
p (g · x) i ∘L g' i) x
参数：hf : HasStrictFDerivAt f f' x；hg : forall i, HasStrictFDerivAt (g i) (g' i) x
。
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
· 使用定理 `HasStrictFDerivAt.continuousMultilinearMap_apply`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [in
st_2 : NormedSpace 𝕜 F] {ι : Type u_2}…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem HasStrictFDerivAt.continuousAlternatingMap_apply (hf : HasStrictFDerivAt f f' x)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x hf
    |>.continuousMultilinearMap_apply hg
/-
**HasFDerivAt.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.continuousAlternatingMap_apply (hf : HasFDerivAt f f' x) (hg :
 forall i, HasFDerivAt (g i) (g' i) x) : HasFDerivAt (fun x => f x (g · x)) (app
ly 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) x
参数：hf : HasFDerivAt f f' x；hg : forall i, HasFDerivAt (g i) (g' i) x。
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
· 使用定理 `HasFDerivAt.continuousMultilinearMap_apply`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 :
 NormedSpace 𝕜 F] {ι : Type u_2}…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivAt.continuousAlternatingMap_apply (hf : HasFDerivAt f f' x)
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp x hf
    |>.continuousMultilinearMap_apply hg
/-
**HasFDerivWithinAt.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.continuousAlternatingMap_apply (hf : HasFDerivWithinAt f
 f' s x) (hg : forall i, HasFDerivWithinAt (g i) (g' i) s x) : HasFDerivWithinAt
 (fun x => f x (g · x)) (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLine
arMap (g · x) i ∘L g' i) s x
参数：hf : HasFDerivWithinAt f f' s x；hg : forall i, HasFDerivWithinAt (g i) (g' i)
 s x。
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
· 使用定理 `HasFDerivWithinAt.continuousMultilinearMap_apply`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [in
st_2 : NormedSpace 𝕜 F] {ι : Type u_2}…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivWithinAt.continuousAlternatingMap_apply (hf : HasFDerivWithinAt f f' s x)
    (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      s x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x hf
    |>.continuousMultilinearMap_apply hg
/-
**fderivWithin_continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜
 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWith
inAt 𝕜 s x) : fderivWithin 𝕜 (fun x => f x (g · x)) s x = apply 𝕜 F G (g · x) ∘L
 fderivWithin 𝕜 f s x + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderivWith
in 𝕜 (g i) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : forall i, DifferentiableWithinAt 𝕜 (
g i) s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.continuousAlternatingMap_apply`：HasFDerivWithinAt.cont
inuousAlternatingMap_apply (hf : HasFDerivWithinAt f f' s x) (hg : forall i, Has
FDerivWithinAt (g i) (g' i) s x) : Has…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ f x (g · x)) s x =
      apply 𝕜 F G (g · x) ∘L fderivWithin 𝕜 f s x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivWithinAt)
    |>.fderivWithin hs
/-
**fderivWithin_continuousAlternatingMap_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：fderivWithin_continuousAlternatingMap_apply_apply (hf : DifferentiableWith
inAt 𝕜 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDi
ffWithinAt 𝕜 s x) (dx : E) : fderivWithin 𝕜 (fun x => f x (g · x)) s x dx = fder
ivWithin 𝕜 f s x dx (g · x) + ∑ i, f x (Function.update (g · x) i (fderivWithin 
𝕜 (g i) s x dx))
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : forall i, DifferentiableWithinAt 𝕜 (
g i) s x；hs : UniqueDiffWithinAt 𝕜 s x；dx : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `fderivWithin_continuousAlternatingMap_apply`：fderivWithin_continuousAlte
rnatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x) (hg : forall i, Different
iableWithinAt 𝕜 (g i) s x) (hs : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAlternatingMap.toContinuousLinearMap_apply`：∀ {R : Type u_1} {
M : Type u_2} {N : Type u_4} {ι : Type u_6} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : _root_.Module R M] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_continuousAlternatingMap_apply_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) (dx : E) :
    fderivWithin 𝕜 (fun x ↦ f x (g · x)) s x dx =
      fderivWithin 𝕜 f s x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderivWithin 𝕜 (g i) s x dx)) := by
  simp [fderivWithin_continuousAlternatingMap_apply, *]
/-
**fderiv_continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x) (hg : 
forall i, DifferentiableAt 𝕜 (g i) x) : fderiv 𝕜 (fun x => f x (g · x)) x = appl
y 𝕜 F G (g · x) ∘L fderiv 𝕜 f x + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L 
fderiv 𝕜 (g i) x
参数：hf : DifferentiableAt 𝕜 f x；hg : forall i, DifferentiableAt 𝕜 (g i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.continuousAlternatingMap_apply`：HasFDerivAt.continuousAltern
atingMap_apply (hf : HasFDerivAt f f' x) (hg : forall i, HasFDerivAt (g i) (g' i
) x) : HasFDerivAt (fun x => f x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x ↦ f x (g · x)) x =
      apply 𝕜 F G (g · x) ∘L fderiv 𝕜 f x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderiv 𝕜 (g i) x :=
  hf.hasFDerivAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivAt) |>.fderiv
/-
**fderiv_continuousAlternatingMap_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_continuousAlternatingMap_apply_apply (hf : DifferentiableAt 𝕜 f x) 
(hg : forall i, DifferentiableAt 𝕜 (g i) x) (dx : E) : fderiv 𝕜 (fun x => f x (g
 · x)) x dx = fderiv 𝕜 f x dx (g · x) + ∑ i, f x (Function.update (g · x) i (fde
riv 𝕜 (g i) x dx))
参数：hf : DifferentiableAt 𝕜 f x；hg : forall i, DifferentiableAt 𝕜 (g i) x；dx : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `fderiv_continuousAlternatingMap_apply`：fderiv_continuousAlternatingMap_a
pply (hf : DifferentiableAt 𝕜 f x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) :
 fderiv 𝕜 (fun x => f x (g …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAlternatingMap.toContinuousLinearMap_apply`：∀ {R : Type u_1} {
M : Type u_2} {N : Type u_4} {ι : Type u_6} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : _root_.Module R M] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_continuousAlternatingMap_apply_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) (dx : E) :
    fderiv 𝕜 (fun x ↦ f x (g · x)) x dx =
      fderiv 𝕜 f x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderiv 𝕜 (g i) x dx)) := by
  simp [fderiv_continuousAlternatingMap_apply, *]

end HasFDerivAt

variable [Finite ι]

/-
**DifferentiableWithinAt.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：DifferentiableWithinAt.continuousAlternatingMap_apply (hf : Differentiable
WithinAt 𝕜 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) : Differen
tiableWithinAt 𝕜 (fun x => f x (g · x)) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : forall i, DifferentiableWithinAt 𝕜 (
g i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.continuousAlternatingMap_apply`：HasFDerivWithinAt.cont
inuousAlternatingMap_apply (hf : HasFDerivWithinAt f f' s x) (hg : forall i, Has
FDerivWithinAt (g i) (g' i) s x) : Has…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f x (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivWithinAt)
    |>.differentiableWithinAt
/-
**DifferentiableAt.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f
 x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) : DifferentiableAt 𝕜 (fun x => f
 x (g · x)) x
参数：hf : DifferentiableAt 𝕜 f x；hg : forall i, DifferentiableAt 𝕜 (g i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.continuousAlternatingMap_apply`：HasFDerivAt.continuousAltern
atingMap_apply (hf : HasFDerivAt f f' x) (hg : forall i, HasFDerivAt (g i) (g' i
) x) : HasFDerivAt (fun x => f x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) : DifferentiableAt 𝕜 (fun x ↦ f x (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivAt)
    |>.differentiableAt
/-
**DifferentiableOn.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.continuousAlternatingMap_apply (hf : DifferentiableOn 𝕜 f
 s) (hg : forall i, DifferentiableOn 𝕜 (g i) s) : DifferentiableOn 𝕜 (fun x => f
 x (g · x)) s
参数：hf : DifferentiableOn 𝕜 f s；hg : forall i, DifferentiableOn 𝕜 (g i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.continuousAlternatingMap_apply`：DifferentiableWit
hinAt.continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x) (hg :
 forall i, DifferentiableWithinAt 𝕜 (g i) s…
-/
theorem DifferentiableOn.continuousAlternatingMap_apply (hf : DifferentiableOn 𝕜 f s)
    (hg : ∀ i, DifferentiableOn 𝕜 (g i) s) : DifferentiableOn 𝕜 (fun x ↦ f x (g · x)) s :=
  fun x hx ↦ (hf x hx).continuousAlternatingMap_apply (hg · x hx)
/-
**Differentiable.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.continuousAlternatingMap_apply (hf : Differentiable 𝕜 f) (h
g : forall i, Differentiable 𝕜 (g i)) : Differentiable 𝕜 (fun x => f x (g · x))
参数：hf : Differentiable 𝕜 f；hg : forall i, Differentiable 𝕜 (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.continuousAlternatingMap_apply`：DifferentiableAt.contin
uousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x) (hg : forall i, Different
iableAt 𝕜 (g i) x) : DifferentiableAt…
-/
theorem Differentiable.continuousAlternatingMap_apply (hf : Differentiable 𝕜 f)
    (hg : ∀ i, Differentiable 𝕜 (g i)) : Differentiable 𝕜 (fun x ↦ f x (g · x)) :=
  fun x ↦ (hf x).continuousAlternatingMap_apply (hg · x)
/-
**ContinuousAlternatingMap.differentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAlternatingMap.differentiable (f : E [⋀^ι]->L[𝕜] F) : Differenti
able 𝕜 f
参数：f : E [⋀^ι]->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Differentiable.continuousAlternatingMap_apply`：Differentiable.continuous
AlternatingMap_apply (hf : Differentiable 𝕜 f) (hg : forall i, Differentiable 𝕜 
(g i)) : Differentiable 𝕜 (fun x =>…
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `differentiable_apply`：differentiable_apply (i : ι) : Differentiable (𝕜
-/
theorem ContinuousAlternatingMap.differentiable (f : E [⋀^ι]→L[𝕜] F) : Differentiable 𝕜 f := by
  cases nonempty_fintype ι
  apply Differentiable.continuousAlternatingMap_apply <;> fun_prop

end Apply

