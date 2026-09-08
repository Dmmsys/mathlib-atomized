/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivative of the Cartesian product of functions

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
Cartesian products of functions, and functions into Pi-types.
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L : Filter (E × E)}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/


section Prod

variable {f₂ : E → G} {f₂' : E →L[𝕜] G}

/-
**HasFDerivAtFilter.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFilter f₁ f₁' L) (hf₂ : HasFDer
ivAtFilter f₂ f₂' L) : HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') 
L
参数：hf₁ : HasFDerivAtFilter f₁ f₁' L；hf₂ : HasFDerivAtFilter f₂ f₂' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `Asymptotics.IsLittleO.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' : 
Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Seminor
medAddCommGroup F'] […
· 使用定理 `HasFDerivAtFilter.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…
-/
theorem HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFilter f₁ f₁' L)
    (hf₂ : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') L :=
  .of_isLittleO <| hf₁.isLittleO.prod_left hf₂.isLittleO
/-
**HasStrictFDerivAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f₁ : E → F} {f₁' : E →L[𝕜] F} {x : 
E} {f₂ : E → G}   {f₂' : E →L[𝕜] G},   HasStrictFDerivAt f₁ f₁' x → HasStrictFDe
rivAt f₂ f₂' x → HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x
参数：fun x => (f₁ x, f₂ x)；f₁'.prod f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.prodMk`：HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFil
ter f₁ f₁' L) (hf₂ : HasFDerivAtFilter f₂ f₂' L) : HasFDerivAtFilter (fun x => (
f₁ x, f₂ x)) (…
-/
protected theorem HasStrictFDerivAt.prodMk (hf₁ : HasStrictFDerivAt f₁ f₁' x)
    (hf₂ : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  HasFDerivAtFilter.prodMk hf₁ hf₂

@[fun_prop]
nonrec theorem HasFDerivWithinAt.prodMk (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prodMk hf₂

@[fun_prop]
nonrec theorem HasFDerivAt.prodMk (hf₁ : HasFDerivAt f₁ f₁' x) (hf₂ : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  hf₁.prodMk hf₂

@[fun_prop]
/-
**hasFDerivAt_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_prodMk_left (e₀ : E) (f₀ : F) : HasFDerivAt (fun e : E => (e, 
f₀)) (inl 𝕜 E F) e₀
参数：e₀ : E；f₀ : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_prodMk_left (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  (hasFDerivAt_id e₀).prodMk (hasFDerivAt_const f₀ e₀)

@[fun_prop]
/-
**hasFDerivAt_prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_prodMk_right (e₀ : E) (f₀ : F) : HasFDerivAt (fun f : F => (e₀
, f)) (inr 𝕜 E F) f₀
参数：e₀ : E；f₀ : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
-/
theorem hasFDerivAt_prodMk_right (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  (hasFDerivAt_const e₀ f₀).prodMk (hasFDerivAt_id f₀)

@[fun_prop]
/-
**DifferentiableWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x) (hf₂
 : DifferentiableWithinAt 𝕜 f₂ s x) : DifferentiableWithinAt 𝕜 (fun x : E => (f₁
 x, f₂ x)) s x
参数：hf₁ : DifferentiableWithinAt 𝕜 f₁ s x；hf₂ : DifferentiableWithinAt 𝕜 f₂ s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : Differentia
bleAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x
参数：hf₁ : DifferentiableAt 𝕜 f₁ x；hf₂ : DifferentiableAt 𝕜 f₂ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.prodMk (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : Differentia
bleOn 𝕜 f₂ s) : DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s
参数：hf₁ : DifferentiableOn 𝕜 f₁ s；hf₂ : DifferentiableOn 𝕜 f₂ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.prodMk`：DifferentiableWithinAt.prodMk (hf₁ : Diff
erentiableWithinAt 𝕜 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) : Different
iableWithinAt 𝕜 (fu…
-/
theorem DifferentiableOn.prodMk (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx => (hf₁ x hx).prodMk (hf₂ x hx)

@[simp, fun_prop]
/-
**Differentiable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.prodMk (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 
f₂) : Differentiable 𝕜 fun x : E => (f₁ x, f₂ x)
参数：hf₁ : Differentiable 𝕜 f₁；hf₂ : Differentiable 𝕜 f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.prodMk`：DifferentiableAt.prodMk (hf₁ : DifferentiableAt
 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x : E => (f₁ 
x, f₂ x)) x
-/
theorem Differentiable.prodMk (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x ↦
  (hf₁ x).prodMk (hf₂ x)
/-
**DifferentiableAt.fderiv_prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.fderiv_prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : Diff
erentiableAt 𝕜 f₂ x) : fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).
prod (fderiv 𝕜 f₂ x)
参数：hf₁ : DifferentiableAt 𝕜 f₁ x；hf₂ : DifferentiableAt 𝕜 f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.fderiv_prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x) :=
  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).fderiv
/-
**DifferentiableWithinAt.fderivWithin_prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.fderivWithin_prodMk (hf₁ : DifferentiableWithinAt 𝕜
 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x
) : fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x = (fderivWithin 𝕜 f₁ s x).pro
d (fderivWithin 𝕜 f₂ s x)
参数：hf₁ : DifferentiableWithinAt 𝕜 f₁ s x；hf₂ : DifferentiableWithinAt 𝕜 f₂ s x；h
xs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.fderivWithin_prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).fderivWithin hxs

end Prod

section Fst

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

/-
**hasFDerivAtFilter_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_fst {L : Filter ((E × F) × (E × F))} : HasFDerivAtFilter
 Prod.fst (fst 𝕜 E F) L
参数：(E × F) × (E × F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem hasFDerivAtFilter_fst {L : Filter ((E × F) × (E × F))} :
    HasFDerivAtFilter Prod.fst (fst 𝕜 E F) L :=
  (fst 𝕜 E F).hasFDerivAtFilter

@[fun_prop]
/-
**hasStrictFDerivAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_fst`：hasFDerivAtFilter_fst {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter Prod.fst (fst 𝕜 E F) L
-/
theorem hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst

@[fun_prop]
/-
**HasStrictFDerivAt.fst** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {f₂ : E → F × G} {f₂' : E →L
[𝕜] F × G},   HasStrictFDerivAt f₂ f₂' x → HasStrictFDerivAt (fun x => (f₂ x).1)
 (ContinuousLinearMap.fst 𝕜 F G ∘SL f₂') x
参数：fun x => (f₂ x).1；ContinuousLinearMap.fst 𝕜 F G ∘SL f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `hasStrictFDerivAt_fst`：hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.
fst E F) (fst 𝕜 E F) p
-/
protected theorem HasStrictFDerivAt.fst (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_fst.comp x h
/-
**HasFDerivAtFilter.fst** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAtFilter`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {L : Filter (E × E)} {f₂ : E → F × G
}   {f₂' : E →L[𝕜] F × G},   HasFDerivAtFilter f₂ f₂' L → HasFDerivAtFilter (fun
 x => (f₂ x).1) (ContinuousLinearMap.fst 𝕜 F G ∘SL f₂') L
参数：E × E；fun x => (f₂ x).1；ContinuousLinearMap.fst 𝕜 F G ∘SL f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `hasFDerivAtFilter_fst`：hasFDerivAtFilter_fst {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter Prod.fst (fst 𝕜 E F) L
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
-/
protected theorem HasFDerivAtFilter.fst (h : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') L :=
  hasFDerivAtFilter_fst.comp h tendsto_map

@[fun_prop]
/-
**hasFDerivAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_fst`：hasFDerivAtFilter_fst {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter Prod.fst (fst 𝕜 E F) L
-/
theorem hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst

@[fun_prop]
/-
**hasFDerivWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_fst {s : Set (E × F)} : HasFDerivWithinAt (@Prod.fst E F
) (fst 𝕜 E F) s p
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_fst`：hasFDerivAtFilter_fst {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter Prod.fst (fst 𝕜 E F) L
-/
theorem hasFDerivWithinAt_fst {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  hasFDerivAtFilter_fst

@[fun_prop]
protected nonrec theorem HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst

@[fun_prop]
/-
**differentiableAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasFDerivAt_fst`：hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E 
F) p
-/
theorem differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFDerivAt_fst.differentiableAt

@[simp, fun_prop]
/-
**DifferentiableAt.fst** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {f₂ : E → F × G},   Differen
tiableAt 𝕜 f₂ x → DifferentiableAt 𝕜 (fun x => (f₂ x).1) x
参数：fun x => (f₂ x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_fst`：differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst
 p
-/
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiableAt_fst.comp x h

@[fun_prop]
/-
**differentiable_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_fst`：differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst
 p
-/
theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) := fun _ =>
  differentiableAt_fst

@[simp, fun_prop]
/-
**Differentiable.fst** 是 Mathlib 中的一个定理，位于命名空间 `Differentiable`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f₂ : E → F × G},   Differentiable 𝕜
 f₂ → Differentiable 𝕜 fun x => (f₂ x).1
参数：f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `differentiable_fst`：differentiable_fst : Differentiable 𝕜 (Prod.fst : E 
× F -> E)
-/
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h

@[fun_prop]
/-
**differentiableWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Pr
od.fst s p
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_fst`：differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst
 p
-/
theorem differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.differentiableWithinAt

@[fun_prop]
/-
**DifferentiableWithinAt.fst** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {s : Set E} {f₂ : E → F × G}
,   DifferentiableWithinAt 𝕜 f₂ s x → DifferentiableWithinAt 𝕜 (fun x => (f₂ x).
1) s x
参数：fun x => (f₂ x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_fst`：differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst
 p
-/
protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiableAt_fst.comp_differentiableWithinAt x h

@[fun_prop]
/-
**differentiableOn_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `differentiable_fst`：differentiable_fst : Differentiable 𝕜 (Prod.fst : E 
× F -> E)
-/
theorem differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.differentiableOn

@[fun_prop]
/-
**DifferentiableOn.fst** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {s : Set E} {f₂ : E → F × G},   Diff
erentiableOn 𝕜 f₂ s → DifferentiableOn 𝕜 (fun x => (f₂ x).1) s
参数：fun x => (f₂ x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp_differentiableOn`：Differentiable.comp_differentiable
On {g : F -> G} (hg : Differentiable 𝕜 g) (hf : DifferentiableOn 𝕜 f s) : Differ
entiableOn 𝕜 (g ∘ f) s
· 使用定理 `differentiable_fst`：differentiable_fst : Differentiable 𝕜 (Prod.fst : E 
× F -> E)
-/
protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiableOn h
/-
**fderiv_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasFDerivAt_fst`：hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E 
F) p
-/
theorem fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFDerivAt_fst.fderiv
/-
**fderiv.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) : fderiv 𝕜 (fun x => (f₂ x).1) x 
= (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x)
参数：h : DifferentiableAt 𝕜 f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.fst`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E 
: Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Ty
pe u_…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.fst.fderiv
/-
**fderivWithin_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) : fderi
vWithin 𝕜 Prod.fst s p = fst 𝕜 E F
参数：E × F；hs : UniqueDiffWithinAt 𝕜 s p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasFDerivWithinAt_fst`：hasFDerivWithinAt_fst {s : Set (E × F)} : HasFDer
ivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p
-/
theorem fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFDerivWithinAt_fst.fderivWithin hs
/-
**fderivWithin.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithin
At 𝕜 f₂ s x) : fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderiv
Within 𝕜 f₂ s x)
参数：hs : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 f₂ s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.fst`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.fst.fderivWithin hs

end Fst

section Snd

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

/-
**hasFDerivAtFilter_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_snd {L : Filter ((E × F) × (E × F))} : HasFDerivAtFilter
 (@Prod.snd E F) (snd 𝕜 E F) L
参数：(E × F) × (E × F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem hasFDerivAtFilter_snd {L : Filter ((E × F) × (E × F))} :
    HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) L :=
  (snd 𝕜 E F).hasFDerivAtFilter
/-
**HasFDerivAtFilter.snd** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAtFilter`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {L : Filter (E × E)} {f₂ : E → F × G
}   {f₂' : E →L[𝕜] F × G},   HasFDerivAtFilter f₂ f₂' L → HasFDerivAtFilter (fun
 x => (f₂ x).2) (ContinuousLinearMap.snd 𝕜 F G ∘SL f₂') L
参数：E × E；fun x => (f₂ x).2；ContinuousLinearMap.snd 𝕜 F G ∘SL f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `hasFDerivAtFilter_snd`：hasFDerivAtFilter_snd {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) L
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
-/
protected theorem HasFDerivAtFilter.snd (h : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') L :=
  hasFDerivAtFilter_snd.comp h tendsto_map

@[fun_prop]
/-
**hasStrictFDerivAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_snd`：hasFDerivAtFilter_snd {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) L
-/
theorem hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd

@[fun_prop]
/-
**HasStrictFDerivAt.snd** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {f₂ : E → F × G} {f₂' : E →L
[𝕜] F × G},   HasStrictFDerivAt f₂ f₂' x → HasStrictFDerivAt (fun x => (f₂ x).2)
 (ContinuousLinearMap.snd 𝕜 F G ∘SL f₂') x
参数：fun x => (f₂ x).2；ContinuousLinearMap.snd 𝕜 F G ∘SL f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
-/
protected theorem HasStrictFDerivAt.snd (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  HasFDerivAtFilter.snd h

@[fun_prop]
/-
**hasFDerivAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_snd`：hasFDerivAtFilter_snd {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) L
-/
theorem hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd

@[fun_prop]
/-
**HasFDerivAt.snd** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {f₂ : E → F × G} {f₂' : E →L
[𝕜] F × G},   HasFDerivAt f₂ f₂' x → HasFDerivAt (fun x => (f₂ x).2) (Continuous
LinearMap.snd 𝕜 F G ∘SL f₂') x
参数：fun x => (f₂ x).2；ContinuousLinearMap.snd 𝕜 F G ∘SL f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
-/
protected theorem HasFDerivAt.snd (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  HasFDerivAtFilter.snd h

@[fun_prop]
/-
**hasFDerivWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_snd {s : Set (E × F)} : HasFDerivWithinAt (@Prod.snd E F
) (snd 𝕜 E F) s p
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_snd`：hasFDerivAtFilter_snd {L : Filter ((E × F) × (E ×
 F))} : HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) L
-/
theorem hasFDerivWithinAt_snd {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFDerivAtFilter_snd

@[fun_prop]
/-
**HasFDerivWithinAt.snd** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {s : Set E} {f₂ : E → F × G}
 {f₂' : E →L[𝕜] F × G},   HasFDerivWithinAt f₂ f₂' s x → HasFDerivWithinAt (fun 
x => (f₂ x).2) (ContinuousLinearMap.snd 𝕜 F G ∘SL f₂') s x
参数：fun x => (f₂ x).2；ContinuousLinearMap.snd 𝕜 F G ∘SL f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
-/
protected theorem HasFDerivWithinAt.snd (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  HasFDerivAtFilter.snd h

@[fun_prop]
/-
**differentiableAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasFDerivAt_snd`：hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E 
F) p
-/
theorem differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFDerivAt_snd.differentiableAt

@[simp, fun_prop]
/-
**DifferentiableAt.snd** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {f₂ : E → F × G},   Differen
tiableAt 𝕜 f₂ x → DifferentiableAt 𝕜 (fun x => (f₂ x).2) x
参数：fun x => (f₂ x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_snd`：differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd
 p
-/
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h

@[fun_prop]
/-
**differentiable_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F -> F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_snd`：differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd
 p
-/
theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) := fun _ =>
  differentiableAt_snd

@[simp, fun_prop]
/-
**Differentiable.snd** 是 Mathlib 中的一个定理，位于命名空间 `Differentiable`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f₂ : E → F × G},   Differentiable 𝕜
 f₂ → Differentiable 𝕜 fun x => (f₂ x).2
参数：f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `differentiable_snd`：differentiable_snd : Differentiable 𝕜 (Prod.snd : E 
× F -> F)
-/
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h

@[fun_prop]
/-
**differentiableWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Pr
od.snd s p
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_snd`：differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd
 p
-/
theorem differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.differentiableWithinAt

@[fun_prop]
/-
**DifferentiableWithinAt.snd** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x : E} {s : Set E} {f₂ : E → F × G}
,   DifferentiableWithinAt 𝕜 f₂ s x → DifferentiableWithinAt 𝕜 (fun x => (f₂ x).
2) s x
参数：fun x => (f₂ x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_snd`：differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd
 p
-/
protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiableWithinAt x h

@[fun_prop]
/-
**differentiableOn_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `differentiable_snd`：differentiable_snd : Differentiable 𝕜 (Prod.snd : E 
× F -> F)
-/
theorem differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.differentiableOn

@[fun_prop]
/-
**DifferentiableOn.snd** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {s : Set E} {f₂ : E → F × G},   Diff
erentiableOn 𝕜 f₂ s → DifferentiableOn 𝕜 (fun x => (f₂ x).2) s
参数：fun x => (f₂ x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp_differentiableOn`：Differentiable.comp_differentiable
On {g : F -> G} (hg : Differentiable 𝕜 g) (hf : DifferentiableOn 𝕜 f s) : Differ
entiableOn 𝕜 (g ∘ f) s
· 使用定理 `differentiable_snd`：differentiable_snd : Differentiable 𝕜 (Prod.snd : E 
× F -> F)
-/
protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiableOn h
/-
**fderiv_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasFDerivAt_snd`：hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E 
F) p
-/
theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFDerivAt_snd.fderiv
/-
**fderiv.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) : fderiv 𝕜 (fun x => (f₂ x).2) x 
= (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x)
参数：h : DifferentiableAt 𝕜 f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E 
: Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Ty
pe u_…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.snd.fderiv
/-
**fderivWithin_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) : fderi
vWithin 𝕜 Prod.snd s p = snd 𝕜 E F
参数：E × F；hs : UniqueDiffWithinAt 𝕜 s p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasFDerivWithinAt_snd`：hasFDerivWithinAt_snd {s : Set (E × F)} : HasFDer
ivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p
-/
theorem fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFDerivWithinAt_snd.fderivWithin hs
/-
**fderivWithin.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithin
At 𝕜 f₂ s x) : fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderiv
Within 𝕜 f₂ s x)
参数：hs : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 f₂ s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.snd.fderivWithin hs

end Snd

section prodMap

variable {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

@[fun_prop]
/-
**HasStrictFDerivAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {G' : Type u_5} [inst_7 : NormedAddC
ommGroup G']   [inst_8 : NormedSpace 𝕜 G'] {f : E → F} {f' : E →L[𝕜] F} {f₂ : G 
→ G'} {f₂' : G →L[𝕜] G'} (p : E × G),   HasStrictFDerivAt f f' p.1 → HasStrictFD
erivAt f₂ f₂' p.2 → HasStrictFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p
参数：p : E × G；Prod.map f f₂；f'.prodMap f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `hasStrictFDerivAt_fst`：hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.
fst E F) (fst 𝕜 E F) p
· 使用定理 `hasStrictFDerivAt_snd`：hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.
snd E F) (snd 𝕜 E F) p
-/
protected theorem HasStrictFDerivAt.prodMap (hf : HasStrictFDerivAt f f' p.1)
    (hf₂ : HasStrictFDerivAt f₂ f₂' p.2) : HasStrictFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasStrictFDerivAt_fst).prodMk (hf₂.comp p hasStrictFDerivAt_snd)

@[fun_prop]
/-
**HasFDerivWithinAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {G' : Type u_5} [inst_7 : NormedAddC
ommGroup G']   [inst_8 : NormedSpace 𝕜 G'] {f : E → F} {f' : E →L[𝕜] F} {f₂ : G 
→ G'} {f₂' : G →L[𝕜] G'} (p : E × G)   {s : Set (E × G)},   HasFDerivWithinAt f 
f' (Prod.fst '' s) p.1 →     HasFDerivWithinAt f₂ f₂' (Prod.snd '' s) p.2 → HasF
DerivWithinAt (Prod.map f f₂) (f'.prodMap f₂') s p
参数：p : E × G；E × G；Prod.fst '' s；Prod.snd '' s；Prod.map f f₂；f'.prodMap f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `hasFDerivWithinAt_fst`：hasFDerivWithinAt_fst {s : Set (E × F)} : HasFDer
ivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p
· 使用引理 `Set.mapsTo_fst_prod`：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Pr
od.fst (s ×ˢ t) s
· 使用定理 `hasFDerivWithinAt_snd`：hasFDerivWithinAt_snd {s : Set (E × F)} : HasFDer
ivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t
-/
protected theorem HasFDerivWithinAt.prodMap {s : Set <| E × G}
    (hf : HasFDerivWithinAt f f' (Prod.fst '' s) p.1)
    (hf₂ : HasFDerivWithinAt f₂ f₂' (Prod.snd '' s) p.2) :
    HasFDerivWithinAt (Prod.map f f₂) (f'.prodMap f₂') s p :=
  (hf.comp _ hasFDerivWithinAt_fst mapsTo_fst_prod).prodMk
    (hf₂.comp _ hasFDerivWithinAt_snd mapsTo_snd_prod) |>.mono (by grind)

@[fun_prop]
/-
**HasFDerivAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {G' : Type u_5} [inst_7 : NormedAddC
ommGroup G']   [inst_8 : NormedSpace 𝕜 G'] {f : E → F} {f' : E →L[𝕜] F} {f₂ : G 
→ G'} {f₂' : G →L[𝕜] G'} (p : E × G),   HasFDerivAt f f' p.1 → HasFDerivAt f₂ f₂
' p.2 → HasFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p
参数：p : E × G；Prod.map f f₂；f'.prodMap f₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `hasFDerivAt_fst`：hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E 
F) p
· 使用定理 `hasFDerivAt_snd`：hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E 
F) p
-/
protected theorem HasFDerivAt.prodMap (hf : HasFDerivAt f f' p.1) (hf₂ : HasFDerivAt f₂ f₂' p.2) :
    HasFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasFDerivAt_fst).prodMk (hf₂.comp p hasFDerivAt_snd)

@[simp, fun_prop]
/-
**DifferentiableAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {G' : Type u_5} [inst_7 : NormedAddC
ommGroup G']   [inst_8 : NormedSpace 𝕜 G'] {f : E → F} {f₂ : G → G'} (p : E × G)
,   DifferentiableAt 𝕜 f p.1 → DifferentiableAt 𝕜 f₂ p.2 → DifferentiableAt 𝕜 (f
un p => (f p.1, f₂ p.2)) p
参数：p : E × G；fun p => (f p.1, f₂ p.2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.prodMk`：DifferentiableAt.prodMk (hf₁ : DifferentiableAt
 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x : E => (f₁ 
x, f₂ x)) x
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_fst`：differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst
 p
· 使用定理 `differentiableAt_snd`：differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd
 p
-/
protected theorem DifferentiableAt.prodMap (hf : DifferentiableAt 𝕜 f p.1)
    (hf₂ : DifferentiableAt 𝕜 f₂ p.2) : DifferentiableAt 𝕜 (fun p : E × G => (f p.1, f₂ p.2)) p :=
  (hf.comp p differentiableAt_fst).prodMk (hf₂.comp p differentiableAt_snd)

end prodMap

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has*FDeriv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `fun x i ↦ φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `fun x ↦ Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type*} {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {φ' : ∀ i, E →L[𝕜] F' i} {Φ : E → ∀ i, F' i}
  {Φ' : E →L[𝕜] ∀ i, F' i}

@[simp]
/-
**hasFDerivAtFilter_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L ↔ forall i, HasFDerivAtFi
lter (fun x => Φ x i) ((proj i).comp Φ') L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAtFilter_pi' :
    HasFDerivAtFilter Φ Φ' L ↔
      ∀ i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]

@[simp]
/-
**hasStrictFDerivAt_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_pi' : HasStrictFDerivAt Φ Φ' x ↔ forall i, HasStrictFDer
ivAt (fun x => Φ x i) ((proj i).comp Φ') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi'`：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L 
↔ forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L
-/
theorem hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
/-
**hasStrictFDerivAt_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_pi'' (hφ : forall i, HasStrictFDerivAt (fun x => Φ x i) 
((proj i).comp Φ') x) : HasStrictFDerivAt Φ Φ' x
参数：hφ : forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi'`：hasStrictFDerivAt_pi' : HasStrictFDerivAt Φ Φ' x 
↔ forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x
-/
theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]
/-
**hasStrictFDerivAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_apply (i : ι) (f : forall i, F' i) : HasStrictFDerivAt (
𝕜
参数：i : ι；f : forall i, F' i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem hasStrictFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f :=
  (proj (R := 𝕜) (φ := F') i).hasStrictFDerivAt
/-
**hasStrictFDerivAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i => φ i x) (ContinuousLin
earMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_pi'`：hasStrictFDerivAt_pi' : HasStrictFDerivAt Φ Φ' x 
↔ forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x
-/
theorem hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'
/-
**hasFDerivAtFilter_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_pi : HasFDerivAtFilter (fun x i => φ i x) (ContinuousLin
earMap.pi φ') L ↔ forall i, HasFDerivAtFilter (φ i) (φ' i) L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi'`：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L 
↔ forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L
-/
theorem hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') L ↔
      ∀ i, HasFDerivAtFilter (φ i) (φ' i) L :=
  hasFDerivAtFilter_pi'

@[simp]
/-
**hasFDerivAt_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_pi' : HasFDerivAt Φ Φ' x ↔ forall i, HasFDerivAt (fun x => Φ x
 i) ((proj i).comp Φ') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi'`：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L 
↔ forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L
-/
theorem hasFDerivAt_pi' :
    HasFDerivAt Φ Φ' x ↔ ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
/-
**hasFDerivAt_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_pi'' (hφ : forall i, HasFDerivAt (fun x => Φ x i) ((proj i).co
mp Φ') x) : HasFDerivAt Φ Φ' x
参数：hφ : forall i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi'`：hasFDerivAt_pi' : HasFDerivAt Φ Φ' x ↔ forall i, HasFDe
rivAt (fun x => Φ x i) ((proj i).comp Φ') x
-/
theorem hasFDerivAt_pi'' (hφ : ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasFDerivAt Φ Φ' x := hasFDerivAt_pi'.2 hφ

@[fun_prop]
/-
**hasFDerivAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_apply (i : ι) (f : forall i, F' i) : HasFDerivAt (𝕜
参数：i : ι；f : forall i, F' i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem hasFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
    HasFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f :=
  (proj (R := 𝕜) (φ := F') i).hasFDerivAt
/-
**hasFDerivAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ'
) x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi`：hasFDerivAtFilter_pi : HasFDerivAtFilter (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') L ↔ forall i, HasFDerivAtFilter (φ i) (φ' 
i) L
-/
theorem hasFDerivAt_pi :
    HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasFDerivAt (φ i) (φ' i) x :=
  hasFDerivAtFilter_pi

@[simp]
/-
**hasFDerivWithinAt_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_pi' : HasFDerivWithinAt Φ Φ' s x ↔ forall i, HasFDerivWi
thinAt (fun x => Φ x i) ((proj i).comp Φ') s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi'`：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L 
↔ forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L
-/
theorem hasFDerivWithinAt_pi' :
    HasFDerivWithinAt Φ Φ' s x ↔ ∀ i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
/-
**hasFDerivWithinAt_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_pi'' (hφ : forall i, HasFDerivWithinAt (fun x => Φ x i) 
((proj i).comp Φ') s x) : HasFDerivWithinAt Φ Φ' s x
参数：hφ : forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi'`：hasFDerivWithinAt_pi' : HasFDerivWithinAt Φ Φ' s 
x ↔ forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x
-/
theorem hasFDerivWithinAt_pi''
    (hφ : ∀ i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x) :
    HasFDerivWithinAt Φ Φ' s x := hasFDerivWithinAt_pi'.2 hφ

@[fun_prop]
/-
**hasFDerivWithinAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_apply (i : ι) (f : forall i, F' i) (s' : Set (forall i, 
F' i)) : HasFDerivWithinAt (𝕜
参数：i : ι；f : forall i, F' i；s' : Set (forall i, F' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `hasFDerivAt_apply`：hasFDerivAt_apply (i : ι) (f : forall i, F' i) : HasF
DerivAt (𝕜
-/
theorem hasFDerivWithinAt_apply (i : ι) (f : ∀ i, F' i) (s' : Set (∀ i, F' i)) :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) s' f :=
  (hasFDerivAt_apply i f).hasFDerivWithinAt
/-
**hasFDerivWithinAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i => φ i x) (ContinuousLin
earMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ' i) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi`：hasFDerivAtFilter_pi : HasFDerivAtFilter (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') L ↔ forall i, HasFDerivAtFilter (φ i) (φ' 
i) L
-/
theorem hasFDerivWithinAt_pi :
    HasFDerivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      ∀ i, HasFDerivWithinAt (φ i) (φ' i) s x :=
  hasFDerivAtFilter_pi

@[simp]
/-
**differentiableWithinAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_pi : DifferentiableWithinAt 𝕜 Φ s x ↔ forall i, Dif
ferentiableWithinAt 𝕜 (fun x => Φ x i) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasFDerivWithinAt_pi'`：hasFDerivWithinAt_pi' : HasFDerivWithinAt Φ Φ' s 
x ↔ forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
-/
theorem differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.hasFDerivWithinAt i).differentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).differentiableWithinAt⟩

@[fun_prop]
/-
**differentiableWithinAt_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_pi'' (hφ : forall i, DifferentiableWithinAt 𝕜 (fun 
x => Φ x i) s x) : DifferentiableWithinAt 𝕜 Φ s x
参数：hφ : forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableWithinAt_pi`：differentiableWithinAt_pi : DifferentiableWit
hinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x
-/
theorem differentiableWithinAt_pi'' (hφ : ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x) :
    DifferentiableWithinAt 𝕜 Φ s x := differentiableWithinAt_pi.2 hφ

@[fun_prop]
/-
**differentiableWithinAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_apply (i : ι) (f : forall i, F' i) (s' : Set (foral
l i, F' i)) : DifferentiableWithinAt (𝕜
参数：i : ι；f : forall i, F' i；s' : Set (forall i, F' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `hasFDerivWithinAt_apply`：hasFDerivWithinAt_apply (i : ι) (f : forall i, 
F' i) (s' : Set (forall i, F' i)) : HasFDerivWithinAt (𝕜
-/
theorem differentiableWithinAt_apply (i : ι) (f : ∀ i, F' i) (s' : Set (∀ i, F' i)) :
    DifferentiableWithinAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) s' f := by
  apply HasFDerivWithinAt.differentiableWithinAt
  fun_prop

@[simp]
/-
**differentiableAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ forall i, DifferentiableAt 
𝕜 (fun x => Φ x i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasFDerivAt_pi'`：hasFDerivAt_pi' : HasFDerivAt Φ Φ' x ↔ forall i, HasFDe
rivAt (fun x => Φ x i) ((proj i).comp Φ') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
-/
theorem differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (hasFDerivAt_pi'.1 h.hasFDerivAt i).differentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).differentiableAt⟩

@[fun_prop]
/-
**differentiableAt_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_pi'' (hφ : forall i, DifferentiableAt 𝕜 (fun x => Φ x i) 
x) : DifferentiableAt 𝕜 Φ x
参数：hφ : forall i, DifferentiableAt 𝕜 (fun x => Φ x i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_pi`：differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ fora
ll i, DifferentiableAt 𝕜 (fun x => Φ x i) x
-/
theorem differentiableAt_pi'' (hφ : ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x) :
    DifferentiableAt 𝕜 Φ x := differentiableAt_pi.2 hφ

@[fun_prop]
/-
**differentiableAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_apply (i : ι) (f : forall i, F' i) : DifferentiableAt (𝕜
参数：i : ι；f : forall i, F' i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_apply`：hasFDerivAt_apply (i : ι) (f : forall i, F' i) : HasF
DerivAt (𝕜
-/
theorem differentiableAt_apply (i : ι) (f : ∀ i, F' i) :
    DifferentiableAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) f :=
  ⟨_, hasFDerivAt_apply ..⟩
/-
**differentiableOn_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ forall i, DifferentiableOn 
𝕜 (fun x => Φ x i) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableWithinAt_pi`：differentiableWithinAt_pi : DifferentiableWit
hinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩

@[fun_prop]
/-
**differentiableOn_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_pi'' (hφ : forall i, DifferentiableOn 𝕜 (fun x => Φ x i) 
s) : DifferentiableOn 𝕜 Φ s
参数：hφ : forall i, DifferentiableOn 𝕜 (fun x => Φ x i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableOn_pi`：differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ fora
ll i, DifferentiableOn 𝕜 (fun x => Φ x i) s
-/
theorem differentiableOn_pi'' (hφ : ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s) :
    DifferentiableOn 𝕜 Φ s := differentiableOn_pi.2 hφ

@[fun_prop]
/-
**differentiableOn_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_apply (i : ι) (s' : Set (forall i, F' i)) : Differentiabl
eOn (𝕜
参数：i : ι；s' : Set (forall i, F' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_apply`：differentiableWithinAt_apply (i : ι) (f : 
forall i, F' i) (s' : Set (forall i, F' i)) : DifferentiableWithinAt (𝕜
-/
theorem differentiableOn_apply (i : ι) (s' : Set (∀ i, F' i)) :
    DifferentiableOn (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) s' :=
  fun _ _ ↦ differentiableWithinAt_apply ..
/-
**differentiable_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_pi : Differentiable 𝕜 Φ ↔ forall i, Differentiable 𝕜 fun x 
=> Φ x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableAt_pi`：differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ fora
ll i, DifferentiableAt 𝕜 (fun x => Φ x i) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩

@[fun_prop]
/-
**differentiable_pi''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_pi'' (hφ : forall i, Differentiable 𝕜 fun x => Φ x i) : Dif
ferentiable 𝕜 Φ
参数：hφ : forall i, Differentiable 𝕜 fun x => Φ x i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiable_pi`：differentiable_pi : Differentiable 𝕜 Φ ↔ forall i, Di
fferentiable 𝕜 fun x => Φ x i
-/
theorem differentiable_pi'' (hφ : ∀ i, Differentiable 𝕜 fun x => Φ x i) :
    Differentiable 𝕜 Φ := differentiable_pi.2 hφ

@[fun_prop]
/-
**differentiable_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_apply (i : ι) : Differentiable (𝕜
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_apply`：differentiableAt_apply (i : ι) (f : forall i, F'
 i) : DifferentiableAt (𝕜
-/
theorem differentiable_apply (i : ι) :
    Differentiable (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) := by intro x; apply differentiableAt_apply

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
/-
**fderivWithin_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_pi (h : forall i, DifferentiableWithinAt 𝕜 (φ i) s x) (hs : U
niqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => f
derivWithin 𝕜 (φ i) s x
参数：h : forall i, DifferentiableWithinAt 𝕜 (φ i) s x；hs : UniqueDiffWithinAt 𝕜 s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs
/-
**fderiv_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_pi (h : forall i, DifferentiableAt 𝕜 (φ i) x) : fderiv 𝕜 (fun x i =
> φ i x) x = pi fun i => fderiv 𝕜 (φ i) x
参数：h : forall i, DifferentiableAt 𝕜 (φ i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv
/-
**fderivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_apply (hΦ : DifferentiableWithinAt 𝕜 Φ s x) (hs : UniqueDiffW
ithinAt 𝕜 s x) (i : ι) : fderivWithin 𝕜 (fun x => Φ x i) s x = (proj i).comp (fd
erivWithin 𝕜 Φ s x)
参数：hΦ : DifferentiableWithinAt 𝕜 Φ s x；hs : UniqueDiffWithinAt 𝕜 s x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasFDerivWithinAt_pi'`：hasFDerivWithinAt_pi' : HasFDerivWithinAt Φ Φ' s 
x ↔ forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_apply (hΦ : DifferentiableWithinAt 𝕜 Φ s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (i : ι) :
    fderivWithin 𝕜 (fun x => Φ x i) s x = (proj i).comp (fderivWithin 𝕜 Φ s x) :=
  (hasFDerivWithinAt_pi'.1 hΦ.hasFDerivWithinAt i).fderivWithin hs
/-
**fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_apply (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι) : fderiv 𝕜 (fun x => Φ 
x i) x = (proj i).comp (fderiv 𝕜 Φ x)
参数：hΦ : DifferentiableAt 𝕜 Φ x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasFDerivAt_pi'`：hasFDerivAt_pi' : HasFDerivAt Φ Φ' x ↔ forall i, HasFDe
rivAt (fun x => Φ x i) ((proj i).comp Φ') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_apply (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι) :
    fderiv 𝕜 (fun x => Φ x i) x = (proj i).comp (fderiv 𝕜 Φ x) :=
  (hasFDerivAt_pi'.1 hΦ.hasFDerivAt i).fderiv

end Pi

/-!
### Derivatives of tuples `f : E → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
-/
section PiFin

variable {n : Nat} {F' : Fin n.succ → Type*}
variable [∀ i, NormedAddCommGroup (F' i)] [∀ i, NormedSpace 𝕜 (F' i)]
variable {φ : E → F' 0} {φs : E → ∀ i, F' (Fin.succ i)}

/-
**hasFDerivAtFilter_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i, F' i} {l : Filter (E × E)} :
 HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔ HasFDerivAtFilter φ (
.proj 0 ∘L φ') l ∧ HasFDerivAtFilter φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') l
参数：E × E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAtFilter_pi'`：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L 
↔ forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAtFilter_finCons
    {φ' : E →L[𝕜] Π i, F' i} {l : Filter (E × E)} :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔
      HasFDerivAtFilter φ (.proj 0 ∘L φ') l ∧
      HasFDerivAtFilter φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') l := by
  rw [hasFDerivAtFilter_pi', Fin.forall_fin_succ, hasFDerivAtFilter_pi']
  dsimp [ContinuousLinearMap.comp, LinearMap.comp, Function.comp_def]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `hasFDerivAtFilter_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasFDerivAtFilter_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_finCons' {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (F
in.succ i)} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φ
s x)) (φ'.finCons φs') l ↔ HasFDerivAtFilter φ φ' l ∧ HasFDerivAtFilter φs φs' l
参数：Fin.succ i；E × E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAtFilter_finCons`：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i,
 F' i} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x))
 φ' l ↔ HasFDer…

--- 原说明 ---
A variant of `hasFDerivAtFilter_finCons` where the derivative variables are free
 on the RHS
instead.
-/
theorem hasFDerivAtFilter_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} {l : Filter (E × E)} :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') l ↔
      HasFDerivAtFilter φ φ' l ∧ HasFDerivAtFilter φs φs' l :=
  hasFDerivAtFilter_finCons
/-
**HasFDerivAtFilter.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.finCons {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fi
n.succ i)} {l : Filter (E × E)} (h : HasFDerivAtFilter φ φ' l) (hs : HasFDerivAt
Filter φs φs' l) : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCon
s φs') l
参数：Fin.succ i；E × E；h : HasFDerivAtFilter φ φ' l；hs : HasFDerivAtFilter φs φs' l
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAtFilter_finCons'`：hasFDerivAtFilter_finCons' {φ' : E ->L[𝕜] F'
 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} {l : Filter (E × E)} : HasFDerivAtFilt
er (fun x => Fin…
-/
theorem HasFDerivAtFilter.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} {l : Filter (E × E)}
    (h : HasFDerivAtFilter φ φ' l) (hs : HasFDerivAtFilter φs φs' l) :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') l :=
  hasFDerivAtFilter_finCons'.mpr ⟨h, hs⟩
/-
**hasStrictFDerivAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_finCons {φ' : E ->L[𝕜] Π i, F' i} : HasStrictFDerivAt (f
un x => Fin.cons (φ x) (φs x)) φ' x ↔ HasStrictFDerivAt φ (.proj 0 ∘L φ') x ∧ Ha
sStrictFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAtFilter_finCons`：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i,
 F' i} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x))
 φ' l ↔ HasFDer…
-/
theorem hasStrictFDerivAt_finCons {φ' : E →L[𝕜] Π i, F' i} :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasStrictFDerivAt φ (.proj 0 ∘L φ') x ∧
      HasStrictFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasStrictFDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasStrictFDerivAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_finCons' {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (F
in.succ i)} : HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs'
) x ↔ HasStrictFDerivAt φ φ' x ∧ HasStrictFDerivAt φs φs' x
参数：Fin.succ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasStrictFDerivAt_finCons`：hasStrictFDerivAt_finCons {φ' : E ->L[𝕜] Π i,
 F' i} : HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔ HasStrictFDer
ivAt φ (.proj 0…

--- 原说明 ---
A variant of `hasStrictFDerivAt_finCons` where the derivative variables are free
 on the RHS
instead.
-/
theorem hasStrictFDerivAt_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔
      HasStrictFDerivAt φ φ' x ∧ HasStrictFDerivAt φs φs' x :=
  hasStrictFDerivAt_finCons

@[fun_prop]
/-
**HasStrictFDerivAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.finCons {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fi
n.succ i)} (h : HasStrictFDerivAt φ φ' x) (hs : HasStrictFDerivAt φs φs' x) : Ha
sStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x
参数：Fin.succ i；h : HasStrictFDerivAt φ φ' x；hs : HasStrictFDerivAt φs φs' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_finCons'`：hasStrictFDerivAt_finCons' {φ' : E ->L[𝕜] F'
 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} : HasStrictFDerivAt (fun x => Fin.cons
 (φ x) (φs x)) (…
-/
theorem HasStrictFDerivAt.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasStrictFDerivAt φ φ' x) (hs : HasStrictFDerivAt φs φs' x) :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x :=
  hasStrictFDerivAt_finCons'.mpr ⟨h, hs⟩
/-
**hasFDerivAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_finCons {φ' : E ->L[𝕜] Π i, F' i} : HasFDerivAt (fun x => Fin.
cons (φ x) (φs x)) φ' x ↔ HasFDerivAt φ (.proj 0 ∘L φ') x ∧ HasFDerivAt φs (Pi.c
ompRightL 𝕜 F' Fin.succ ∘L φ') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAtFilter_finCons`：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i,
 F' i} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x))
 φ' l ↔ HasFDer…
-/
theorem hasFDerivAt_finCons
    {φ' : E →L[𝕜] Π i, F' i} :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasFDerivAt φ (.proj 0 ∘L φ') x ∧ HasFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasFDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasFDerivAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_finCons' {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.suc
c i)} : HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔ HasFDe
rivAt φ φ' x ∧ HasFDerivAt φs φs' x
参数：Fin.succ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAt_finCons`：hasFDerivAt_finCons {φ' : E ->L[𝕜] Π i, F' i} : Has
FDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔ HasFDerivAt φ (.proj 0 ∘L φ') x
 ∧ HasFDe…

--- 原说明 ---
A variant of `hasFDerivAt_finCons` where the derivative variables are free on th
e RHS
instead.
-/
theorem hasFDerivAt_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔
      HasFDerivAt φ φ' x ∧ HasFDerivAt φs φs' x :=
  hasFDerivAt_finCons

@[fun_prop]
/-
**HasFDerivAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.finCons {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ
 i)} (h : HasFDerivAt φ φ' x) (hs : HasFDerivAt φs φs' x) : HasFDerivAt (fun x =
> Fin.cons (φ x) (φs x)) (φ'.finCons φs') x
参数：Fin.succ i；h : HasFDerivAt φ φ' x；hs : HasFDerivAt φs φs' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_finCons'`：hasFDerivAt_finCons' {φ' : E ->L[𝕜] F' 0} {φs' : E
 ->L[𝕜] Π i, F' (Fin.succ i)} : HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'
.finCons φ…
-/
theorem HasFDerivAt.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasFDerivAt φ φ' x) (hs : HasFDerivAt φs φs' x) :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x :=
  hasFDerivAt_finCons'.mpr ⟨h, hs⟩
/-
**hasFDerivWithinAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_finCons {φ' : E ->L[𝕜] Π i, F' i} : HasFDerivWithinAt (f
un x => Fin.cons (φ x) (φs x)) φ' s x ↔ HasFDerivWithinAt φ (.proj 0 ∘L φ') s x 
∧ HasFDerivWithinAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAtFilter_finCons`：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i,
 F' i} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x))
 φ' l ↔ HasFDer…
-/
theorem hasFDerivWithinAt_finCons
    {φ' : E →L[𝕜] Π i, F' i} :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) φ' s x ↔
      HasFDerivWithinAt φ (.proj 0 ∘L φ') s x ∧
      HasFDerivWithinAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') s x :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasFDerivWithinAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasFDerivWithinAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_finCons' {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (F
in.succ i)} : HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs'
) s x ↔ HasFDerivWithinAt φ φ' s x ∧ HasFDerivWithinAt φs φs' s x
参数：Fin.succ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAtFilter_finCons`：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i,
 F' i} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x))
 φ' l ↔ HasFDer…

--- 原说明 ---
A variant of `hasFDerivWithinAt_finCons` where the derivative variables are free
 on the RHS
instead.
-/
theorem hasFDerivWithinAt_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x ↔
      HasFDerivWithinAt φ φ' s x ∧ HasFDerivWithinAt φs φs' s x :=
  hasFDerivAtFilter_finCons

@[fun_prop]
/-
**HasFDerivWithinAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.finCons {φ' : E ->L[𝕜] F' 0} {φs' : E ->L[𝕜] Π i, F' (Fi
n.succ i)} (h : HasFDerivWithinAt φ φ' s x) (hs : HasFDerivWithinAt φs φs' s x) 
: HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x
参数：Fin.succ i；h : HasFDerivWithinAt φ φ' s x；hs : HasFDerivWithinAt φs φs' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_finCons'`：hasFDerivWithinAt_finCons' {φ' : E ->L[𝕜] F'
 0} {φs' : E ->L[𝕜] Π i, F' (Fin.succ i)} : HasFDerivWithinAt (fun x => Fin.cons
 (φ x) (φs x)) (…
-/
theorem HasFDerivWithinAt.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasFDerivWithinAt φ φ' s x) (hs : HasFDerivWithinAt φs φs' s x) :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x :=
  hasFDerivWithinAt_finCons'.mpr ⟨h, hs⟩
/-
**differentiableWithinAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_finCons : DifferentiableWithinAt 𝕜 (fun x => Fin.co
ns (φ x) (φs x)) s x ↔ DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜
 φs s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableWithinAt_pi`：differentiableWithinAt_pi : DifferentiableWit
hinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_finCons :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔
      DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜 φs s x := by
  rw [differentiableWithinAt_pi, Fin.forall_fin_succ, differentiableWithinAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiableWithinAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**differentiableWithinAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_finCons' : DifferentiableWithinAt 𝕜 (fun x => Fin.c
ons (φ x) (φs x)) s x ↔ DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 
𝕜 φs s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `differentiableWithinAt_finCons`：differentiableWithinAt_finCons : Differe
ntiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔ DifferentiableWithinAt 
𝕜 φ s x ∧ Differenti…

--- 原说明 ---
A variant of `differentiableWithinAt_finCons` where the derivative variables are
 free on the RHS
instead.
-/
theorem differentiableWithinAt_finCons' :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔
      DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜 φs s x :=
  differentiableWithinAt_finCons

@[fun_prop]
/-
**DifferentiableWithinAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.finCons (h : DifferentiableWithinAt 𝕜 φ s x) (hs : 
DifferentiableWithinAt 𝕜 φs s x) : DifferentiableWithinAt 𝕜 (fun x => Fin.cons (
φ x) (φs x)) s x
参数：h : DifferentiableWithinAt 𝕜 φ s x；hs : DifferentiableWithinAt 𝕜 φs s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableWithinAt_finCons'`：differentiableWithinAt_finCons' : Diffe
rentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔ DifferentiableWithinA
t 𝕜 φ s x ∧ Different…
-/
theorem DifferentiableWithinAt.finCons
    (h : DifferentiableWithinAt 𝕜 φ s x) (hs : DifferentiableWithinAt 𝕜 φs s x) :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x :=
  differentiableWithinAt_finCons'.mpr ⟨h, hs⟩
/-
**differentiableAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_finCons : DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs
 x)) x ↔ DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableAt_pi`：differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ fora
ll i, DifferentiableAt 𝕜 (fun x => Φ x i) x
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableAt_finCons :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔
      DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x := by
  rw [differentiableAt_pi, Fin.forall_fin_succ, differentiableAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiableAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**differentiableAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_finCons' : DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φ
s x)) x ↔ DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `differentiableAt_finCons`：differentiableAt_finCons : DifferentiableAt 𝕜 
(fun x => Fin.cons (φ x) (φs x)) x ↔ DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜
 φs x

--- 原说明 ---
A variant of `differentiableAt_finCons` where the derivative variables are free 
on the RHS
instead.
-/
theorem differentiableAt_finCons' :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔
      DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x :=
  differentiableAt_finCons

@[fun_prop]
/-
**DifferentiableAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.finCons (h : DifferentiableAt 𝕜 φ x) (hs : Differentiable
At 𝕜 φs x) : DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x
参数：h : DifferentiableAt 𝕜 φ x；hs : DifferentiableAt 𝕜 φs x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_finCons'`：differentiableAt_finCons' : DifferentiableAt 
𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔ DifferentiableAt 𝕜 φ x ∧ DifferentiableAt
 𝕜 φs x
-/
theorem DifferentiableAt.finCons
    (h : DifferentiableAt 𝕜 φ x) (hs : DifferentiableAt 𝕜 φs x) :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x :=
  differentiableAt_finCons'.mpr ⟨h, hs⟩
/-
**differentiableOn_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_finCons : DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs
 x)) s ↔ DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableOn_pi`：differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ fora
ll i, DifferentiableOn 𝕜 (fun x => Φ x i) s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableOn_finCons :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔
      DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s := by
  rw [differentiableOn_pi, Fin.forall_fin_succ, differentiableOn_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiableOn_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**differentiableOn_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_finCons' : DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φ
s x)) s ↔ DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `differentiableOn_finCons`：differentiableOn_finCons : DifferentiableOn 𝕜 
(fun x => Fin.cons (φ x) (φs x)) s ↔ DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜
 φs s

--- 原说明 ---
A variant of `differentiableOn_finCons` where the derivative variables are free 
on the RHS
instead.
-/
theorem differentiableOn_finCons' :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔
      DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s :=
  differentiableOn_finCons

@[fun_prop]
/-
**DifferentiableOn.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.finCons (h : DifferentiableOn 𝕜 φ s) (hs : Differentiable
On 𝕜 φs s) : DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s
参数：h : DifferentiableOn 𝕜 φ s；hs : DifferentiableOn 𝕜 φs s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableOn_finCons'`：differentiableOn_finCons' : DifferentiableOn 
𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔ DifferentiableOn 𝕜 φ s ∧ DifferentiableOn
 𝕜 φs s
-/
theorem DifferentiableOn.finCons
    (h : DifferentiableOn 𝕜 φ s) (hs : DifferentiableOn 𝕜 φs s) :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s :=
  differentiableOn_finCons'.mpr ⟨h, hs⟩
/-
**differentiable_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_finCons : Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x))
 ↔ Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiable_pi`：differentiable_pi : Differentiable 𝕜 Φ ↔ forall i, Di
fferentiable 𝕜 fun x => Φ x i
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiable_finCons :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) ↔
      Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs := by
  rw [differentiable_pi, Fin.forall_fin_succ, differentiable_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiable_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**differentiable_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_finCons' : Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)
) ↔ Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `differentiable_finCons`：differentiable_finCons : Differentiable 𝕜 (fun x
 => Fin.cons (φ x) (φs x)) ↔ Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs

--- 原说明 ---
A variant of `differentiable_finCons` where the derivative variables are free on
 the RHS
instead.
-/
theorem differentiable_finCons' :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) ↔
      Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs :=
  differentiable_finCons

@[fun_prop]
/-
**Differentiable.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.finCons (h : Differentiable 𝕜 φ) (hs : Differentiable 𝕜 φs)
 : Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x))
参数：h : Differentiable 𝕜 φ；hs : Differentiable 𝕜 φs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiable_finCons'`：differentiable_finCons' : Differentiable 𝕜 (fun
 x => Fin.cons (φ x) (φs x)) ↔ Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs
-/
theorem Differentiable.finCons
    (h : Differentiable 𝕜 φ) (hs : Differentiable 𝕜 φs) :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) :=
  differentiable_finCons'.mpr ⟨h, hs⟩

-- TODO: write the `Fin.cons` versions of `fderivWithin_pi` and `fderiv_pi`

end PiFin

end CartesianProduct

end

