/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of models with corners and (extended) charts

In this file, we analyse the differentiability of charts, models with corners and extended charts.
We show that
* models with corners are differentiable
* charts are differentiable on their source
* `mdifferentiableOn_extChartAt`: `extChartAt` is differentiable on its source

Suppose an open partial homeomorphism `e` is differentiable. This file shows
* `OpenPartialHomeomorph.MDifferentiable.mfderiv`: its derivative is a continuous linear equivalence
* `OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective`: its derivative is bijective;
  there are also spellings with trivial kernel and full range

In particular, (extended) charts have bijective differential.

## Tags
charts, differentiable, bijective
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff
open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

section ModelWithCorners
namespace ModelWithCorners

/- In general, the model with corner `I` is implicit in most theorems in differential geometry, but
this section is about `I` as a map, not as a parameter. Therefore, we make it explicit. -/
variable (I)

/-! #### Model with corners -/

/-
**ModelWithCorners.hasMFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {x : H},   HasMFDerivAt% (↑I) x 
(ContinuousLinearMap.id 𝕜 (TangentSpace I x))
参数：I : ModelWithCorners 𝕜 E H；↑I；ContinuousLinearMap.id 𝕜 (TangentSpace I x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `HasFDerivWithinAt.congr'`：HasFDerivWithinAt.congr' (h : HasFDerivWithinA
t f f' s x) (hs : EqOn f₁ f s) (hx : x in s) : HasFDerivWithinAt f₁ f' s x
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `ModelWithCorners.rightInvOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
#### Model with corners
-/
protected theorem hasMFDerivAt {x} : HasMFDerivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩
/-
**ModelWithCorners.hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorner
s`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {s : Set H}   {x : H}, HasMFDeri
vAt[s] (↑I) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x))
参数：I : ModelWithCorners 𝕜 E H；↑I；ContinuousLinearMap.id 𝕜 (TangentSpace I x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `ModelWithCorners.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x (ContinuousLinearMap.id _ _) :=
  I.hasMFDerivAt.hasMFDerivWithinAt
/-
**ModelWithCorners.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithC
orners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {s : Set H}   {x : H}, MDiffAt[s
] ↑I x
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `ModelWithCorners.hasMFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
-/
protected theorem mdifferentiableWithinAt {s x} : MDiffAt[s] I x :=
  I.hasMFDerivWithinAt.mdifferentiableWithinAt
/-
**ModelWithCorners.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {x : H},   MDiffAt ↑I x
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `ModelWithCorners.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
protected theorem mdifferentiableAt {x} : MDiffAt I x :=
  I.hasMFDerivAt.mdifferentiableAt
/-
**ModelWithCorners.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {s : Set H},   MDiff[s] ↑I
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.mdifferentiableWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {H : Type u_…
-/
protected theorem mdifferentiableOn {s} : MDiff[s] I := fun _ _ =>
  I.mdifferentiableWithinAt
/-
**ModelWithCorners.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H), MDiff ↑I
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.mdifferentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {H : Type u_…
-/
protected theorem mdifferentiable : MDiff I := fun _ => I.mdifferentiableAt
/-
**ModelWithCorners.hasMFDerivWithinAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithC
orners`。
形式化陈述：hasMFDerivWithinAt_symm {x} (hx : x in range I) : HasMFDerivWithinAt 𝓘(𝕜, 
E) I I.symm (range I) x (ContinuousLinearMap.id _ _)
参数：hx : x in range I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.continuousWithinAt_symm`：continuousWithinAt_symm {s x} 
: ContinuousWithinAt I.symm s x
· 使用定理 `HasFDerivWithinAt.congr'`：HasFDerivWithinAt.congr' (h : HasFDerivWithinA
t f f' s x) (hs : EqOn f₁ f s) (hx : x in s) : HasFDerivWithinAt f₁ f' s x
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `ModelWithCorners.rightInvOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem hasMFDerivWithinAt_symm {x} (hx : x ∈ range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩
/-
**ModelWithCorners.mdifferentiableOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCo
rners`。
形式化陈述：mdifferentiableOn_symm : MDiff[range I] I.symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `ModelWithCorners.hasMFDerivWithinAt_symm`：hasMFDerivWithinAt_symm {x} (h
x : x in range I) : HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousL
inearMap.id _ _)
-/
theorem mdifferentiableOn_symm : MDiff[range I] I.symm := fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt
/-
**ModelWithCorners.mdifferentiableWithinAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `Model
WithCorners`。
形式化陈述：mdifferentiableWithinAt_symm {z : E} (hz : z in range I) : MDiffAt[range I
] I.symm z
参数：hz : z in range I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.mdifferentiableOn_symm`：mdifferentiableOn_symm : MDiff[
range I] I.symm
-/
theorem mdifferentiableWithinAt_symm {z : E} (hz : z ∈ range I) :
    MDiffAt[range I] I.symm z :=
  I.mdifferentiableOn_symm z hz

end ModelWithCorners

end ModelWithCorners

section Charts

variable {e : OpenPartialHomeomorph M H}

/-
**mdifferentiableAt_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_of_mem_maximalAtlas (h : e in IsManifold.maximalAtlas I 
1 M) {x : M} (hx : x in e.source) : MDiffAt e x
参数：h : e in IsManifold.maximalAtlas I 1 M；hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_of_mem_maximalAtlas`：contMDiffAt_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) (hx : x in e.source) : ContMDiffAt I I n e x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableAt_of_mem_maximalAtlas
    (h : e ∈ IsManifold.maximalAtlas I 1 M) {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  (contMDiffAt_of_mem_maximalAtlas h hx).mdifferentiableAt one_ne_zero
/-
**mdifferentiableAt_symm_of_mem_maximalAtlas** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_symm_of_mem_maximalAtlas (h : e in IsManifold.maximalAtl
as I 1 M) {x : H} (hx : x in e.target) : MDiffAt e.symm x
参数：h : e in IsManifold.maximalAtlas I 1 M；hx : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_symm_of_mem_maximalAtlas`：contMDiffAt_symm_of_mem_maximalAtl
as {x : H} (h : e in maximalAtlas I n M) (hx : x in e.target) : ContMDiffAt I I 
n e.symm x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiableAt_symm_of_mem_maximalAtlas
    (h : e ∈ IsManifold.maximalAtlas I 1 M) {x : H} (hx : x ∈ e.target) :
    MDiffAt e.symm x :=
  contMDiffAt_symm_of_mem_maximalAtlas h hx |>.mdifferentiableAt one_ne_zero

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']
/-
**mdifferentiableAt_atlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_atlas (h : e in atlas H M) {x : M} (hx : x in e.source) 
: MDiffAt e x
参数：h : e in atlas H M；hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_of_mem_maximalAtlas`：contMDiffAt_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) (hx : x in e.source) : ContMDiffAt I I n e x
· 使用定理 `IsManifold.subset_maximalAtlas`：subset_maximalAtlas [IsManifold I n M] :
 atlas H M subseteq maximalAtlas I n M
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableAt_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
    |>.mdifferentiableAt one_ne_zero
/-
**mdifferentiableOn_atlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_atlas (h : e in atlas H M) : MDiff[e.source] e
参数：h : e in atlas H M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiableAt_atlas`：mdifferentiableAt_atlas (h : e in atlas H M) {x
 : M} (hx : x in e.source) : MDiffAt e x
-/
theorem mdifferentiableOn_atlas (h : e ∈ atlas H M) : MDiff[e.source] e :=
  fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt
/-
**mdifferentiableAt_atlas_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_atlas_symm (h : e in atlas H M) {x : H} (hx : x in e.tar
get) : MDiffAt e.symm x
参数：h : e in atlas H M；hx : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableAt_symm_of_mem_maximalAtlas`：mdifferentiableAt_symm_of_me
m_maximalAtlas (h : e in IsManifold.maximalAtlas I 1 M) {x : H} (hx : x in e.tar
get) : MDiffAt e.symm x
· 使用定理 `IsManifold.subset_maximalAtlas`：subset_maximalAtlas [IsManifold I n M] :
 atlas H M subseteq maximalAtlas I n M
-/
theorem mdifferentiableAt_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
    MDiffAt e.symm x :=
  mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
/-
**mdifferentiableOn_atlas_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_atlas_symm (h : e in atlas H M) : MDiff[e.target] e.symm
参数：h : e in atlas H M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiableAt_atlas_symm`：mdifferentiableAt_atlas_symm (h : e in atl
as H M) {x : H} (hx : x in e.target) : MDiffAt e.symm x
-/
theorem mdifferentiableOn_atlas_symm (h : e ∈ atlas H M) : MDiff[e.target] e.symm :=
  fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt
/-
**mdifferentiable_of_mem_atlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_of_mem_atlas (h : e in atlas H M) : e.MDifferentiable I I
参数：h : e in atlas H M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableOn_atlas`：mdifferentiableOn_atlas (h : e in atlas H M) : 
MDiff[e.source] e
· 使用定理 `mdifferentiableOn_atlas_symm`：mdifferentiableOn_atlas_symm (h : e in atl
as H M) : MDiff[e.target] e.symm
-/
theorem mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩
/-
**mdifferentiable_chart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiable_of_mem_atlas`：mdifferentiable_of_mem_atlas (h : e in atl
as H M) : e.MDifferentiable I I
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
-/
theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

end Charts

/-! ### Differentiable open partial homeomorphisms -/

namespace OpenPartialHomeomorph.MDifferentiable
variable {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I')
  {e' : OpenPartialHomeomorph M' M''}
include he

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm

/-
**OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命
名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {e : OpenPartialHomeomorph M M'},   Ope
nPartialHomeomorph.MDifferentiable I I' e → ∀ {x : M}, x ∈ e.source → MDiffAt ↑e
 x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)
/-
**OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt_symm** 是 Mathlib 中的一个定
理，位于命名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：mdifferentiableAt_symm {x : M'} (hx : x in e.target) : MDiffAt e.symm x
参数：hx : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDiffAt e.symm x :=
  (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)
/-
**OpenPartialHomeomorph.MDifferentiable.symm_comp_deriv** 是 Mathlib 中的一个定理，位于命名空
间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：symm_comp_deriv {x : M} (hx : x in e.source) : (mfderiv% e.symm (e x)).com
p (mfderiv% e x) = ContinuousLinearMap.id 𝕜 (TangentSpace I x)
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt_symm`：mdifferent
iableAt_symm {x : M'} (hx : x in e.target) : MDiffAt e.symm x
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt`：∀ {𝕜 : Type u_1
} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `Filter.EventuallyEq.mfderiv_eq`：Filter.EventuallyEq.mfderiv_eq (hL : f₁ 
=ᶠ[𝓝 x] f) : mfderiv% f₁ x = mfderiv% f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv% e.symm (e x)).comp (mfderiv% e x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : mfderiv% (e.symm ∘ e) x = (mfderiv% e.symm (e x)).comp (mfderiv% e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv% (_root_.id : M → M) x = ContinuousLinearMap.id _ _ := mfderiv_id
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source ∈ 𝓝 x := e.open_source.mem_nhds hx
  exact Filter.mem_of_superset this (by mfld_set_tac)
/-
**OpenPartialHomeomorph.MDifferentiable.comp_symm_deriv** 是 Mathlib 中的一个定理，位于命名空
间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：comp_symm_deriv {x : M'} (hx : x in e.target) : (mfderiv% e (e.symm x)).co
mp (mfderiv% e.symm x) = ContinuousLinearMap.id 𝕜 (TangentSpace I' x)
参数：hx : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.symm_comp_deriv`：symm_comp_deriv {
x : M} (hx : x in e.source) : (mfderiv% e.symm (e x)).comp (mfderiv% e x) = Cont
inuousLinearMap.id 𝕜 (TangentSpace I x)
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.symm`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv% e (e.symm x)).comp (mfderiv% e.symm x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx

/-- The derivative of a differentiable open partial homeomorphism, as a continuous linear
equivalence between the tangent spaces at `x` and `e x`. -/
/-
**OpenPartialHomeomorph.MDifferentiable.mfderiv** 是 Mathlib 中的一个定义，位于命名空间 `OpenP
artialHomeomorph.MDifferentiable`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     {I : ModelWithCorners 𝕜 E H} →                 {M : Type u_4} →            
       [inst_4 : TopologicalSpace M] →                     [inst_5 : ChartedSpac
e H M] →                       {E' : Type u_5} →                         [inst_6
 : NormedAddCommGroup E'] →                           [inst_7 : NormedSpace 𝕜 E'
] →                             {H' : Type u_6} →                               
[inst_8 : TopologicalSpace H'] →                                 {I' : ModelWith
Corners 𝕜 E' H'} →                                   {M' : Type u_7} →          
                           [inst_9 : TopologicalSpace M'] →                     
                  [inst_10 : ChartedSpace H' M'] →                              
           {e : OpenPartialHomeomorph M M'} →                                   
        OpenPartialHomeomorph.MDifferentiable I I' e →                          
                   {x : M} → x ∈ e.source → TangentSpace I x ≃L[𝕜] TangentSpace 
I' (↑e x)
参数：↑e x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of a differentiable open partial homeomorphism, as a continuous l
inear
equivalence between the tangent spaces at `x` and `e x`.
-/
protected def mfderiv (he : e.MDifferentiable I I') {x : M} (hx : x ∈ e.source) :
    TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv% e x with
    invFun := mfderiv% e.symm (e x)
    continuous_toFun := (mfderiv% e x).cont
    continuous_invFun := (mfderiv% e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x →L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
      rfl
    right_inv := fun y => by
      have :
        (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) →L[𝕜] TangentSpace I' (e x)) y = y :=
        rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }
/-
**OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective** 是 Mathlib 中的一个定理，位于命
名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：mfderiv_bijective {x : M} (hx : x in e.source) : Function.Bijective (mfder
iv% e x)
参数：hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.bijective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
-/
theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv% e x) :=
  (he.mfderiv hx).bijective
/-
**OpenPartialHomeomorph.MDifferentiable.mfderiv_injective** 是 Mathlib 中的一个定理，位于命
名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：mfderiv_injective {x : M} (hx : x in e.source) : Function.Injective (mfder
iv% e x)
参数：hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.injective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
-/
theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv% e x) :=
  (he.mfderiv hx).injective
/-
**OpenPartialHomeomorph.MDifferentiable.mfderiv_surjective** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：mfderiv_surjective {x : M} (hx : x in e.source) : Function.Surjective (mfd
eriv% e x)
参数：hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv% e x) :=
  (he.mfderiv hx).surjective
/-
**OpenPartialHomeomorph.MDifferentiable.ker_mfderiv_eq_bot** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：ker_mfderiv_eq_bot {x : M} (hx : x in e.source) : (mfderiv% e x).ker = ⊥
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
-/
theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : (mfderiv% e x).ker = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker
/-
**OpenPartialHomeomorph.MDifferentiable.range_mfderiv_eq_top** 是 Mathlib 中的一个定理，
位于命名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：range_mfderiv_eq_top {x : M} (hx : x in e.source) : (mfderiv% e x).range =
 ⊤
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : (mfderiv% e x).range = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range
/-
**OpenPartialHomeomorph.MDifferentiable.range_mfderiv_eq_univ** 是 Mathlib 中的一个定理
，位于命名空间 `OpenPartialHomeomorph.MDifferentiable`。
形式化陈述：range_mfderiv_eq_univ {x : M} (hx : x in e.source) : range (mfderiv% e x) 
= univ
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mfderiv_surjective`：mfderiv_surjec
tive {x : M} (hx : x in e.source) : Function.Surjective (mfderiv% e x)
-/
theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv% e x) = univ :=
  (he.mfderiv_surjective hx).range_eq
/-
**OpenPartialHomeomorph.MDifferentiable.trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph.MDifferentiable`。
形式化陈述：trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I
''
参数：he' : e'.MDifferentiable I' I''。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt`：∀ {𝕜 : Type u_1
} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.symm`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdifferentiableAt hx.1)).mdifferentiableWithinAt

end OpenPartialHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section extChartAt

variable [IsManifold I 1 M] {s : Set M} {x y : M} {z : E}

/-
**hasMFDerivAt_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_extChartAt (h : y in (chartAt H x).source) : HasMFDerivAt% (e
xtChartAt I x) y (mfderiv% (chartAt H x) y :)
参数：h : y in (chartAt H x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.comp`：HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf
 : HasMFDerivAt% f x f') : HasMFDerivAt% (g ∘ f) x (g'.comp f')
· 使用定理 `ModelWithCorners.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt`：∀ {𝕜 : Type u_1
} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `mdifferentiable_chart`：mdifferentiable_chart (x : M) : (chartAt H x).MDi
fferentiable I I
-/
theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt% (extChartAt I x) y (mfderiv% (chartAt H x) y :) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt
/-
**hasMFDerivWithinAt_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_extChartAt (h : y in (chartAt H x).source) : HasMFDeriv
At[s] (extChartAt I x) y (mfderiv% (chartAt H x) y :)
参数：h : y in (chartAt H x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `hasMFDerivAt_extChartAt`：hasMFDerivAt_extChartAt (h : y in (chartAt H x)
.source) : HasMFDerivAt% (extChartAt I x) y (mfderiv% (chartAt H x) y :)
-/
theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt[s] (extChartAt I x) y (mfderiv% (chartAt H x) y :) :=
  (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt
/-
**mdifferentiableAt_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_extChartAt (h : y in (chartAt H x).source) : MDiffAt (ex
tChartAt I x) y
参数：h : y in (chartAt H x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `hasMFDerivAt_extChartAt`：hasMFDerivAt_extChartAt (h : y in (chartAt H x)
.source) : HasMFDerivAt% (extChartAt I x) y (mfderiv% (chartAt H x) y :)
-/
theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDiffAt (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt h).mdifferentiableAt
/-
**mdifferentiableOn_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_extChartAt : MDiff[(chartAt H x).source] (extChartAt I x
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `hasMFDerivWithinAt_extChartAt`：hasMFDerivWithinAt_extChartAt (h : y in (
chartAt H x).source) : HasMFDerivAt[s] (extChartAt I x) y (mfderiv% (chartAt H x
) y :)
-/
theorem mdifferentiableOn_extChartAt : MDiff[(chartAt H x).source] (extChartAt I x) :=
  fun _y hy ↦ (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt
/-
**mdifferentiableWithinAt_extChartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_extChartAt_symm (h : z in (extChartAt I x).target)
 : MDiffAt[range I] (extChartAt I x).symm z
参数：h : z in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.mdifferentiableWithinAt_symm`：mdifferentiableWithinAt_s
ymm {z : E} (hz : z in range I) : MDiffAt[range I] I.symm z
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `mdifferentiableAt_atlas_symm`：mdifferentiableAt_atlas_symm (h : e in atl
as H M) {x : H} (hx : x in e.target) : MDiffAt e.symm x
· 使用定理 `ChartedSpace.chart_mem_atlas`：∀ {H : Type u_5} {inst : TopologicalSpace 
H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x :
 M), ChartedSpace.…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem mdifferentiableWithinAt_extChartAt_symm (h : z ∈ (extChartAt I x).target) :
    MDiffAt[range I] (extChartAt I x).symm z := by
  have Z := I.mdifferentiableWithinAt_symm (extChartAt_target_subset_range x h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I) _ _ Z
  apply mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x)
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_target,
    ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm, mem_inter_iff, mem_range,
    mem_preimage] at h
  exact h.2
/-
**mdifferentiableOn_extChartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_extChartAt_symm : MDiff[(extChartAt I x).target] (extCha
rtAt I x).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
· 使用定理 `mdifferentiableWithinAt_extChartAt_symm`：mdifferentiableWithinAt_extChar
tAt_symm (h : z in (extChartAt I x).target) : MDiffAt[range I] (extChartAt I x).
symm z
-/
theorem mdifferentiableOn_extChartAt_symm :
    MDiff[(extChartAt I x).target] (extChartAt I x).symm := by
  intro y hy
  exact (mdifferentiableWithinAt_extChartAt_symm hy).mono (extChartAt_target_subset_range x)

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
/-
**mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm {x : M} {y : E} (hy 
: y in (extChartAt I x).target) : (mfderiv% (extChartAt I x) ((extChartAt I x).s
ymm y)) ∘L (mfderiv[range I] (extChartAt I x).symm y) = ContinuousLinearMap.id _
 _
参数：hy : y in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.uniqueMDiffOn`：ModelWithCorners.uniqueMDiffOn {H : Type
*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : UniqueMDiff[Set.range I]
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `mfderiv_comp_mfderivWithin`：mfderiv_comp_mfderivWithin (hg : MDiffAt g (
f x)) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] (g ∘ f) x = 
(mfderiv% g (f x…
· 使用定理 `mdifferentiableAt_extChartAt`：mdifferentiableAt_extChartAt (h : y in (ch
artAt H x).source) : MDiffAt (extChartAt I x) y
· 使用定理 `mdifferentiableWithinAt_extChartAt_symm`：mdifferentiableWithinAt_extChar
tAt_symm (h : z in (extChartAt I x).target) : MDiffAt[range I] (extChartAt I x).
symm z
· 使用定理 `mfderivWithin_id`：mfderivWithin_id (hxs : UniqueMDiffAt[s] x) : mfderiv[
s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x)
· 使用定理 `Filter.EventuallyEq.mfderivWithin_eq`：Filter.EventuallyEq.mfderivWithin_
eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : mfderiv[s] f₁ x = mfderiv[s] f x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_target_mem_nhdsWithin_of_mem`：extChartAt_target_mem_nhdsWithi
n_of_mem {x : M} {y : E} (hy : y in (extChartAt I x).target) : (extChartAt I x).
target in 𝓝[range I] y
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of the derivative of `extChartAt` with the derivative of the inv
erse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`.
-/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm {x : M}
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv% (extChartAt I x) ((extChartAt I x).symm y)) ∘L
      (mfderiv[range I] (extChartAt I x).symm y) = ContinuousLinearMap.id _ _ := by
  have U : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    exact extChartAt_target_subset_range x hy
  have h'y : (extChartAt I x).symm y ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  rw [← mfderiv_comp_mfderivWithin]; rotate_left
  · apply mdifferentiableAt_extChartAt h''y
  · exact mdifferentiableWithinAt_extChartAt_symm hy
  · exact U
  rw [← mfderivWithin_id U]
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with z hz
    simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
/-
**mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' {x : M} {y : M} (hy
 : y in (extChartAt I x).source) : (mfderiv% (extChartAt I x) y) ∘L (mfderiv[ran
ge I] (extChartAt I x).symm (extChartAt I x y)) = ContinuousLinearMap.id _ _
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`：mfderiv_extChartA
t_comp_mfderivWithin_extChartAt_symm {x : M} {y : E} (hy : y in (extChartAt I x)
.target) : (mfderiv% (extChartAt I x) ((ext…
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target

--- 原说明 ---
The composition of the derivative of `extChartAt` with the derivative of the inv
erse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`.
-/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' {x : M}
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y) ∘L (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y))
    = ContinuousLinearMap.id _ _ := by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ((extChartAt I x).map_source hy)

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
/-
**mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt {y : E} (hy : y in (
extChartAt I x).target) : (mfderiv[range I] (extChartAt I x).symm y) ∘L (mfderiv
% (extChartAt I x) ((extChartAt I x).symm y)) = ContinuousLinearMap.id _ _
参数：hy : y in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `IsOpen.uniqueMDiffWithinAt`：IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (
xs : x in s) : UniqueMDiffAt[s] x
· 使用定理 `isOpen_extChartAt_source`：isOpen_extChartAt_source (x : M) : IsOpen (ext
ChartAt I x).source
· 使用定理 `mfderivWithin_eq_mfderiv`：mfderivWithin_eq_mfderiv (hs : UniqueMDiffAt[s
] x) (h : MDiffAt f x) : mfderiv[s] f x = mfderiv% f x
· 使用定理 `mdifferentiableAt_extChartAt`：mdifferentiableAt_extChartAt (h : y in (ch
artAt H x).source) : MDiffAt (extChartAt I x) y
· 使用定理 `mfderivWithin_comp_of_eq`：mfderivWithin_comp_of_eq {x : M} {y : M'} (hg 
: MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMD
iffAt[s] x) (h…
· 使用定理 `mdifferentiableWithinAt_extChartAt_symm`：mdifferentiableWithinAt_extChar
tAt_symm (h : z in (extChartAt I x).target) : MDiffAt[range I] (extChartAt I x).
symm z
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `mfderivWithin_id`：mfderivWithin_id (hxs : UniqueMDiffAt[s] x) : mfderiv[
s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x)
· 使用定理 `Filter.EventuallyEq.mfderivWithin_eq`：Filter.EventuallyEq.mfderivWithin_
eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : mfderiv[s] f₁ x = mfderiv[s] f x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_source_mem_nhdsWithin'`：extChartAt_source_mem_nhdsWithin' {x 
x' : M} (h : x' in (extChartAt I x).source) : (extChartAt I x).source in 𝓝[s] x'
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of the derivative of the inverse of `extChartAt` with the deriva
tive of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`.
-/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y) ∘L
      (mfderiv% (extChartAt I x) ((extChartAt I x).symm y))
      = ContinuousLinearMap.id _ _ := by
  have h'y : (extChartAt I x).symm y ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  have U' : UniqueMDiffAt[(extChartAt I x).source] ((extChartAt I x).symm y) :=
    (isOpen_extChartAt_source x).uniqueMDiffWithinAt h'y
  have : mfderiv% (extChartAt I x) ((extChartAt I x).symm y)
      = mfderiv[(extChartAt I x).source] (extChartAt I x) ((extChartAt I x).symm y) := by
    rw [mfderivWithin_eq_mfderiv U']
    exact mdifferentiableAt_extChartAt h''y
  rw [this, ← mfderivWithin_comp_of_eq]; rotate_left
  · exact mdifferentiableWithinAt_extChartAt_symm hy
  · exact (mdifferentiableAt_extChartAt h''y).mdifferentiableWithinAt
  · intro z hz
    apply extChartAt_target_subset_range x
    exact PartialEquiv.map_source (extChartAt I x) hz
  · exact U'
  · exact PartialEquiv.right_inv (extChartAt I x) hy
  rw [← mfderivWithin_id U']
  apply Filter.EventuallyEq.mfderivWithin_eq
  · filter_upwards [extChartAt_source_mem_nhdsWithin' h'y] with z hz
    simp only [Function.comp_def, PartialEquiv.left_inv (extChartAt I x) hz, id_eq]
  · simp only [Function.comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
/-
**mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' {y : M} (hy : y in 
(extChartAt I x).source) : (mfderiv[range I] (extChartAt I x).symm (extChartAt I
 x y)) ∘L (mfderiv% (extChartAt I x) y) = ContinuousLinearMap.id _ _
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt`：mfderivWithin_ext
ChartAt_symm_comp_mfderiv_extChartAt {y : E} (hy : y in (extChartAt I x).target)
 : (mfderiv[range I] (extChartAt I x).symm …
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target

--- 原说明 ---
The composition of the derivative of the inverse of `extChartAt` with the deriva
tive of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`.
-/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)) ∘L (mfderiv% (extChartAt I x) y)
      = ContinuousLinearMap.id _ _ := by
  have : y = (extChartAt I x).symm (extChartAt I x y) := ((extChartAt I x).left_inv hy).symm
  convert! mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ((extChartAt I x).map_source hy)
  rw [(extChartAt I x).left_inv (by simpa using hy)]
/-
**isInvertible_mfderivWithin_extChartAt_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y in (extChartAt 
I x).target) : (mfderiv[range I] (extChartAt I x).symm y).IsInvertible
参数：hy : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsInvertible.of_inverse`：∀ {R : Type u_1} {M : Type 
u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂] 
  [inst_2 : Semiring R] [inst_3 :…
· 使用引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt`：mfderivWithin_ext
ChartAt_symm_comp_mfderiv_extChartAt {y : E} (hy : y in (extChartAt I x).target)
 : (mfderiv[range I] (extChartAt I x).symm …
· 使用引理 `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`：mfderiv_extChartA
t_comp_mfderivWithin_extChartAt_symm {x : M} {y : E} (hy : y in (extChartAt I x)
.target) : (mfderiv% (extChartAt I x) ((ext…
-/
lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)
/-
**isInvertible_mfderiv_extChartAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isInvertible_mfderiv_extChartAt {y : M} (hy : y in (extChartAt I x).source
) : (mfderiv% (extChartAt I x) y).IsInvertible
参数：hy : y in (extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `ContinuousLinearMap.IsInvertible.of_inverse`：∀ {R : Type u_1} {M : Type 
u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂] 
  [inst_2 : Semiring R] [inst_3 :…
· 使用引理 `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`：mfderiv_extChartA
t_comp_mfderivWithin_extChartAt_symm {x : M} {y : E} (hy : y in (extChartAt I x)
.target) : (mfderiv% (extChartAt I x) ((ext…
· 使用引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt`：mfderivWithin_ext
ChartAt_symm_comp_mfderiv_extChartAt {y : E} (hy : y in (extChartAt I x).target)
 : (mfderiv[range I] (extChartAt I x).symm …
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y).IsInvertible := by
  have h'y : extChartAt I x y ∈ (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  rwa [this] at Z

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of the tangent bundle at a point is the manifold derivative of the
extended chart.
Use with care as this abuses the defeq `TangentSpace 𝓘(𝕜, E) y = E` for `y : E`. -/
/-
**TangentBundle.continuousLinearMapAt_trivializationAt** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：TangentBundle.continuousLinearMapAt_trivializationAt {x₀ x : M} (hx : x in
 (chartAt H x₀).source) : (trivializationAt E (TangentSpace I) x₀).continuousLin
earMapAt 𝕜 x = mfderiv% (extChartAt I x₀) x
参数：hx : x in (chartAt H x₀).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_extChartAt`：mdifferentiableAt_extChartAt (h : y in (ch
artAt H x).source) : MDiffAt (extChartAt I x) y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorBundleCore.vectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [inst
_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.trivializationAt_continuousLinearMapAt`：∀ {R : Type u_1
} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : Nor
medAddCommGroup F]   [inst_2 : NormedSpace R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tangentBundleCore_indexAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trivialization of the tangent bundle at a point is the manifold derivative o
f the
extended chart.
Use with care as this abuses the defeq `TangentSpace 𝓘(𝕜, E) y = E` for `y : E`.
-/
theorem TangentBundle.continuousLinearMapAt_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x =
      mfderiv% (extChartAt I x₀) x := by
  have : MDiffAt (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at this
  simp [hx, mfderiv, this]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse trivialization of the tangent bundle at a point is the manifold derivative of the
inverse of the extended chart.
Use with care as this abuses the defeq `TangentSpace 𝓘(𝕜, E) y = E` for `y : E`. -/
/-
**TangentBundle.symmL_trivializationAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TangentBundle.symmL_trivializationAt {x₀ x : M} (hx : x in (chartAt H x₀).
source) : (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x = mfderiv[range I] 
(extChartAt I x₀).symm (extChartAt I x₀ x)
参数：hx : x in (chartAt H x₀).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableWithinAt_extChartAt_symm`：mdifferentiableWithinAt_extChar
tAt_symm (h : z in (extChartAt I x).target) : MDiffAt[range I] (extChartAt I x).
symm z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `VectorBundleCore.vectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [inst
_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.trivializationAt_symmL`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup 
F]   [inst_2 : NormedSpace R …
· 使用定理 `tangentBundleCore_indexAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inverse trivialization of the tangent bundle at a point is the manifold deri
vative of the
inverse of the extended chart.
Use with care as this abuses the defeq `TangentSpace 𝓘(𝕜, E) y = E` for `y : E`.
-/
theorem TangentBundle.symmL_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x =
      mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x) := by
  have : MDiffAt[range I] ((chartAt H x₀).symm ∘ I.symm) (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  simp [hx, mfderivWithin, this]

omit [IsManifold I 1 M] in
/-- The `fderivWithin` of the round-trip composition `(extChartAt I x) ∘ (extChartAt I x).symm`
at the chart point in `range I` equals the identity. -/
/-
**fderivWithin_extChartAt_comp_extChartAt_symm_range** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：fderivWithin_extChartAt_comp_extChartAt_symm_range : fderivWithin 𝕜 ((extC
hartAt I x) ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) = ContinuousLi
nearMap.id 𝕜 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `fderivWithin_id`：fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] 
[T2Space E] (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E
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
· 使用定理 `UniqueDiffOn.uniqueDiffWithinAt`：UniqueDiffOn.uniqueDiffWithinAt {s : Se
t E} {x} (hs : UniqueDiffOn R s) (h : x in s) : UniqueDiffWithinAt R s x
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The `fderivWithin` of the round-trip composition `(extChartAt I x) ∘ (extChartAt
 I x).symm`
at the chart point in `range I` equals the identity.
-/
lemma fderivWithin_extChartAt_comp_extChartAt_symm_range :
    fderivWithin 𝕜 ((extChartAt I x) ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) =
      ContinuousLinearMap.id 𝕜 _ := by
  set φ := extChartAt I x
  have eq_nhd : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[𝓝[range I] (extChartAt I x x)] id :=
    Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      (fun _ ↦ (extChartAt I x).right_inv)
  rw [eq_nhd.fderivWithin_eq (by simp)]
  exact fderivWithin_id <| I.uniqueDiffOn.uniqueDiffWithinAt (mem_range_self _)

/-- The manifold derivative of `extChartAt` at the basepoint is the identity. -/
/-
**mfderiv_extChartAt_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderiv_extChartAt_self : mfderiv% (extChartAt I x) x = ContinuousLinearMa
p.id 𝕜 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TangentBundle.continuousLinearMapAt_trivializationAt`：TangentBundle.cont
inuousLinearMapAt_trivializationAt {x₀ x : M} (hx : x in (chartAt H x₀).source) 
: (trivializationAt E (TangentSpace I) x₀)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TangentBundle.continuousLinearMapAt_trivializationAt_eq_core`：continuous
LinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b in (chartAt H b₀).source
) : (trivializationAt E (TangentSpace I) b₀).conti…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `VectorBundleCore.coordChange_self`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce

--- 原说明 ---
The manifold derivative of `extChartAt` at the basepoint is the identity.
-/
lemma mfderiv_extChartAt_self :
    mfderiv% (extChartAt I x) x = ContinuousLinearMap.id 𝕜 _ := by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simp),
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp)]
  ext v
  simpa using! (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

set_option backward.isDefEq.respectTransparency false in
-- TODO: should there be a version for `extChartAt`?
/-- The manifold derivative within `range I` of `(extChartAt I x).symm` at the chart point is
the identity. -/
/-
**mfderivWithin_range_extChartAt_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_range_extChartAt_symm : mfderiv[range I] (extChartAt I x).sy
mm (extChartAt I x x) = ContinuousLinearMap.id 𝕜 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'`：mfderivWithin_ex
tChartAt_symm_comp_mfderiv_extChartAt' {y : M} (hy : y in (extChartAt I x).sourc
e) : (mfderiv[range I] (extChartAt I x).symm…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用引理 `mfderiv_extChartAt_self`：mfderiv_extChartAt_self : mfderiv% (extChartAt 
I x) x = ContinuousLinearMap.id 𝕜 _

--- 原说明 ---
The manifold derivative within `range I` of `(extChartAt I x).symm` at the chart
 point is
the identity.
-/
lemma mfderivWithin_range_extChartAt_symm :
    mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) = ContinuousLinearMap.id 𝕜 _ := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
    (mem_extChartAt_source x)
  rw [mfderiv_extChartAt_self, ContinuousLinearMap.comp_id] at hcomp
  simpa using! hcomp

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the derivative of `(extChartAt I x).symm` at the chart point,
applied to a tangent vector, gives back the tangent vector. -/
/-
**mfderivWithin_extChartAt_symm_inverse_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_extChartAt_symm_inverse_apply (v : TangentSpace I x) : (mfde
riv[range I] (extChartAt I x).symm (extChartAt I x x)).inverse v = v
参数：v : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mfderivWithin_range_extChartAt_symm`：mfderivWithin_range_extChartAt_symm
 : mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) = ContinuousLinearM
ap.id 𝕜 _
· 使用定理 `ContinuousLinearMap.inverse_id`：∀ {R : Type u_1} {M : Type u_2} [inst : 
TopologicalSpace M] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 :
 _root_.Module R M],…
· 使用定理 `ContinuousLinearMap.id_apply`：id_apply (x : M₁) : ContinuousLinearMap.id
 R₁ M₁ x = x

--- 原说明 ---
The inverse of the derivative of `(extChartAt I x).symm` at the chart point,
applied to a tangent vector, gives back the tangent vector.
-/
lemma mfderivWithin_extChartAt_symm_inverse_apply (v : TangentSpace I x) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x x)).inverse v = v := by
  rw [mfderivWithin_range_extChartAt_symm, ContinuousLinearMap.inverse_id]
  exact ContinuousLinearMap.id_apply ..

end extChartAt

