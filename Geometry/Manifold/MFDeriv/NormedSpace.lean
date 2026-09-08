/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Equivalence of manifold differentiability with the basic definition for functions between
vector spaces

The API in this file is mostly copied from `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`,
providing the same statements for higher smoothness. In this file, we do the same for
differentiability.

## Main definitions

In addition to the above, this file provides two important definitions.
* `mvfderiv I f x` is the manifold Fréchet derivative at `x : M` of a vector-valued function
  `f : M → V`, but taking values in the target normed space `V` instead of `TangentSpace% (f x) V`.
  Mathematically, this uses the global trivialization `T V ≅ V × V`, yielding an identification
  `T_v V ≅ V` for each `v : V`. In Lean, we post-compose the differential `mfderiv% f x` with
  `NormedSpace.fromTangentSpace`. If `V` is a field, this coincides with the exterior derivative
  of `f` as a section of the cotangent bundle.
  There is notation `d% f` for `mvfderiv I f` via a custom elaborator scoped to the
  `Manifold` namespace, with a corresponding delaborator,
* `mvfderivWithin` with notation `d[s] f` for `mvfderivWithin I f s` in the `Manifold` namespace:
  the analogous concept within a set, with analogous API lemmas

## Main results

This file contains
* results about the differentiability of scalar multiplication (`mfderiv_smul` and friends),
* basic lemmas about `mvfderiv` (such as addition, subtraction, multiplication and constants),
* analogous lemmas about `mvfderivWithin`,
* composition lemmas about `mvfderivWithin` and `mvfderiv`.

-/

public section

open Set ChartedSpace IsManifold
open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a `C^n` manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' n M']
  -- declare a `C^n` manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]
  -- declare a `C^n` manifold `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [IsManifold J' n N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M → M'} {s t : Set M} {x : M} {m n : ℕ∞}

section Module

/-
**DifferentiableWithinAt.comp_mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：DifferentiableWithinAt.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -
> F} {s : Set M} {t : Set F} {x : M} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (
hf : MDiffAt[s] f x) (h : MapsTo f s t) : MDiffAt[s] (g ∘ f) x
参数：hg : DifferentiableWithinAt 𝕜 g t (f x)；hf : MDiffAt[s] f x；h : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
· 使用定理 `DifferentiableWithinAt.mdifferentiableWithinAt`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace 𝕜 E] {E' : Type u…
-/
theorem DifferentiableWithinAt.comp_mdifferentiableWithinAt
    {g : F → F'} {f : M → F} {s : Set M} {t : Set F} {x : M}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : MDiffAt[s] f x) (h : MapsTo f s t) :
    MDiffAt[s] (g ∘ f) x :=
  hg.mdifferentiableWithinAt.comp x hf h
/-
**DifferentiableAt.comp_mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -> F} {
s : Set M} {x : M} (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt[s] f x) : MDi
ffAt[s] (g ∘ f) x
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `DifferentiableAt.mdifferentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
-/
theorem DifferentiableAt.comp_mdifferentiableWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x :=
  hg.mdifferentiableAt.comp_mdifferentiableWithinAt x hf
/-
**DifferentiableAt.comp_mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.comp_mdifferentiableAt {g : F -> F'} {f : M -> F} {x : M}
 (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x
参数：hg : DifferentiableAt 𝕜 g (f x)；hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_mdifferentiableWithinAt`：DifferentiableAt.comp_mdi
fferentiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differ
entiableAt 𝕜 g (f x)) (hf : MDiffAt…
-/
theorem DifferentiableAt.comp_mdifferentiableAt {g : F → F'} {f : M → F} {x : M}
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf
/-
**Differentiable.comp_mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -> F} {s 
: Set M} {x : M} (hg : Differentiable 𝕜 g) (hf : MDiffAt[s] f x) : MDiffAt[s] (g
 ∘ f) x
参数：hg : Differentiable 𝕜 g；hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_mdifferentiableWithinAt`：DifferentiableAt.comp_mdi
fferentiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differ
entiableAt 𝕜 g (f x)) (hf : MDiffAt…
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
-/
theorem Differentiable.comp_mdifferentiableWithinAt {g : F → F'} {f : M → F} {s : Set M} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x :=
  hg.differentiableAt.comp_mdifferentiableWithinAt hf
/-
**Differentiable.comp_mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.comp_mdifferentiableAt {g : F -> F'} {f : M -> F} {x : M} (
hg : Differentiable 𝕜 g) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x
参数：hg : Differentiable 𝕜 g；hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp_mdifferentiableWithinAt`：Differentiable.comp_mdiffer
entiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differenti
able 𝕜 g) (hf : MDiffAt[s] f x) :…
-/
theorem Differentiable.comp_mdifferentiableAt {g : F → F'} {f : M → F} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf
/-
**Differentiable.comp_mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.comp_mdifferentiable {g : F -> F'} {f : M -> F} (hg : Diffe
rentiable 𝕜 g) (hf : MDiff f) : MDiff (g ∘ f)
参数：hg : Differentiable 𝕜 g；hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_mdifferentiableAt`：DifferentiableAt.comp_mdifferen
tiableAt {g : F -> F'} {f : M -> F} {x : M} (hg : DifferentiableAt 𝕜 g (f x)) (h
f : MDiffAt f x) : MDiffAt (g…
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
-/
theorem Differentiable.comp_mdifferentiable {g : F → F'} {f : M → F}
    (hg : Differentiable 𝕜 g) (hf : MDiff f) : MDiff (g ∘ f) :=
  fun x ↦ hg.differentiableAt.comp_mdifferentiableAt (hf x)

end Module

section extChartAt

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F}

set_option backward.isDefEq.respectTransparency.types false in
-- TODO: add pre-composition version also
/-
**MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm (hf : 
MDiffAt[s] f x) : letI φ
参数：hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_iff`：mdifferentiableWithinAt_iff : MDiffAt[s] f 
x ↔ ContinuousWithinAt f s x ∧ DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f
 ∘ (extChartAt I …
-/
theorem MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm (hf : MDiffAt[s] f x) :
    letI φ := extChartAt I x
    DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s ∩ range I) (φ x) := by
  simpa [extChartAt_self_eq] using (mdifferentiableWithinAt_iff.1 hf).2

-- TODO: the `IsManifold I 1 M` assumption can probably be removed
/-
**DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm [Is
Manifold I 1 M] (hf : letI φ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mdifferentiableWithinAt_iff_source_of_mem_source`：mdifferentiableWithinA
t_iff_source_of_mem_source [IsManifold I 1 M] {x' : M} (hx' : x' in (chartAt H x
).source) : MDiffAt[s] f x' ↔ MDiffAt[…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `DifferentiableWithinAt.mdifferentiableWithinAt`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace 𝕜 E] {E' : Type u…
-/
theorem DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm [IsManifold I 1 M]
    (hf : letI φ := extChartAt I x
      DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s ∩ range I) (φ x)) :
    MDiffAt[s] f x := by
  refine (mdifferentiableWithinAt_iff_source_of_mem_source (mem_chart_source H x)).2 ?_
  simpa [extChartAt_self_eq] using hf.mdifferentiableWithinAt

end extChartAt

/-! ### Linear maps between normed spaces are differentiable -/

/-
**MDifferentiableWithinAt.clm_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x
 : M} (hf : MDiffAt[s] f x) : MDiffAt[s] (fun y => (f y).precomp F₃ : M -> (F₂ -
>L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x
参数：hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Differentiable.comp_mdifferentiableWithinAt`：Differentiable.comp_mdiffer
entiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differenti
able 𝕜 g) (hf : MDiffAt[s] f x) :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…

--- 原说明 ---
### Linear maps between normed spaces are differentiable
-/
theorem MDifferentiableWithinAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

nonrec theorem MDifferentiableAt.clm_precomp {f : M → F₁ →L[𝕜] F₂} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf
/-
**MDifferentiableOn.clm_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} (hf : MD
iff[s] f) : MDiff[s] (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁
 ->L[𝕜] F₃))
参数：hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableWithinAt.clm_precomp`：MDifferentiableWithinAt.clm_precomp
 {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M} (hf : MDiffAt[s] f x) : MDiffAt[s] 
(fun y => (f y).precomp F…
-/
theorem MDifferentiableOn.clm_precomp {f : M → F₁ →L[𝕜] F₂} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) :=
  fun x hx ↦ (hf x hx).clm_precomp
/-
**MDifferentiable.clm_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} (hf : MDiff f) : MDiff
 (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃))
参数：hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableAt.clm_precomp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
theorem MDifferentiable.clm_precomp {f : M → F₁ →L[𝕜] F₂} (hf : MDiff f) :
    MDiff (fun y ↦ (f y).precomp F₃ : M → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) :=
  fun x ↦ (hf x).clm_precomp
/-
**MDifferentiableWithinAt.clm_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {
x : M} (hf : MDiffAt[s] f x) : MDiffAt[s] (fun y => (f y).postcomp F₁ : M -> (F₁
 ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x
参数：hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Differentiable.comp_mdifferentiableWithinAt`：Differentiable.comp_mdiffer
entiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differenti
able 𝕜 g) (hf : MDiffAt[s] f x) :…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
theorem MDifferentiableWithinAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf
/-
**MDifferentiableAt.clm_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {x : M} (hf : MDiff
At f x) : MDiffAt (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ -
>L[𝕜] F₃)) x
参数：hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Differentiable.comp_mdifferentiableAt`：Differentiable.comp_mdifferentiab
leAt {g : F -> F'} {f : M -> F} {x : M} (hg : Differentiable 𝕜 g) (hf : MDiffAt 
f x) : MDiffAt (g ∘ f) x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
theorem MDifferentiableAt.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

nonrec theorem MDifferentiableOn.clm_postcomp {f : M → F₂ →L[𝕜] F₃} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) := fun x hx ↦
  (hf x hx).clm_postcomp
/-
**MDifferentiable.clm_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} (hf : MDiff f) : MDif
f (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃))
参数：hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableAt.clm_postcomp`：MDifferentiableAt.clm_postcomp {f : M ->
 F₂ ->L[𝕜] F₃} {x : M} (hf : MDiffAt f x) : MDiffAt (fun y => (f y).postcomp F₁ 
: M -> (F₁ ->L[𝕜] F₂…
-/
theorem MDifferentiable.clm_postcomp {f : M → F₂ →L[𝕜] F₃} (hf : MDiff f) :
    MDiff (fun y ↦ (f y).postcomp F₁ : M → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) :=
  fun x ↦ (hf x).clm_postcomp
/-
**MDifferentiableWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[
𝕜] F₁} {s : Set M} {x : M} (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) : MDiffAt
[s] (fun x => (g x).comp (f x)) x
参数：hg : MDiffAt[s] g x；hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Differentiable.comp_mdifferentiableWithinAt`：Differentiable.comp_mdiffer
entiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differenti
able 𝕜 g) (hf : MDiffAt[s] f x) :…
· 使用定理 `Differentiable.clm_comp`：Differentiable.clm_comp (hc : Differentiable 𝕜 
c) (hd : Differentiable 𝕜 d) : Differentiable 𝕜 fun y => (c y).comp (d y)
· 使用定理 `differentiable_fst`：differentiable_fst : Differentiable 𝕜 (Prod.fst : E 
× F -> E)
· 使用定理 `differentiable_snd`：differentiable_snd : Differentiable 𝕜 (Prod.snd : E 
× F -> F)
· 使用定理 `MDifferentiableWithinAt.prodMk_space`：MDifferentiableWithinAt.prodMk_spa
ce {f : M -> E'} {g : M -> E''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MD
ifferentiableWithinAt I 𝓘(…
-/
theorem MDifferentiableWithinAt.clm_comp
    {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M} {x : M}
    (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (g x).comp (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (differentiable_fst.clm_comp differentiable_snd)
    (hg.prodMk_space hf)
/-
**MDifferentiableAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
 {x : M} (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x => (g x).comp (f
 x)) x
参数：hg : MDiffAt g x；hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `MDifferentiableWithinAt.clm_comp`：MDifferentiableWithinAt.clm_comp {g : 
M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M} (hg : MDiffAt[s] 
g x) (hf : MDiffAt[s] …
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem MDifferentiableAt.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (g x).comp (f x)) x :=
  (hg.mdifferentiableWithinAt.clm_comp hf.mdifferentiableWithinAt).mdifferentiableAt Filter.univ_mem
/-
**MDifferentiableOn.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
 {s : Set M} (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x => (g x).comp
 (f x))
参数：hg : MDiff[s] g；hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableWithinAt.clm_comp`：MDifferentiableWithinAt.clm_comp {g : 
M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M} (hg : MDiffAt[s] 
g x) (hf : MDiffAt[s] …
-/
theorem MDifferentiableOn.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x ↦ (g x).comp (f x)) :=
  fun x hx ↦ (hg x hx).clm_comp (hf x hx)
/-
**MDifferentiable.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} (
hg : MDiff g) (hf : MDiff f) : MDiff fun x => (g x).comp (f x)
参数：hg : MDiff g；hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableAt.clm_comp`：MDifferentiableAt.clm_comp {g : M -> F₁ ->L[
𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M} (hg : MDiffAt g x) (hf : MDiffAt f x) : M
DiffAt (fun x =>…
-/
theorem MDifferentiable.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x ↦ (g x).comp (f x) :=
  fun x ↦ (hg x).clm_comp (hf x)

/-- Applying a linear map to a vector is differentiable within a set. Version in vector spaces. For
a version in nontrivial vector bundles, see `MDifferentiableWithinAt.clm_apply_of_inCoordinates`. -/
/-
**MDifferentiableWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s
 : Set M} {x : M} (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) : MDiffAt[s] (fun 
x => g x (f x)) x
参数：hg : MDiffAt[s] g x；hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DifferentiableWithinAt.comp_mdifferentiableWithinAt`：DifferentiableWithi
nAt.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {t : Set
 F} {x : M} (hg : DifferentiableWithinAt …
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Differentiable.clm_apply`：Differentiable.clm_apply (hc : Differentiable 
𝕜 c) (hu : Differentiable 𝕜 u) : Differentiable 𝕜 fun y => (c y) (u y)
· 使用定理 `differentiable_fst`：differentiable_fst : Differentiable 𝕜 (Prod.fst : E 
× F -> E)
· 使用定理 `differentiable_snd`：differentiable_snd : Differentiable 𝕜 (Prod.snd : E 
× F -> F)
· 使用定理 `MDifferentiableWithinAt.prodMk_space`：MDifferentiableWithinAt.prodMk_spa
ce {f : M -> E'} {g : M -> E''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MD
ifferentiableWithinAt I 𝓘(…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Applying a linear map to a vector is differentiable within a set. Version in vec
tor spaces. For
a version in nontrivial vector bundles, see `MDifferentiableWithinAt.clm_apply_o
f_inCoordinates`.
-/
theorem MDifferentiableWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
    (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ ↦ x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

/-- Applying a linear map to a vector is differentiable. Version in vector spaces. For a
version in nontrivial vector bundles, see `MDifferentiableAt.clm_apply_of_inCoordinates`. -/
/-
**MDifferentiableAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {x : M} 
(hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x => g x (f x)) x
参数：hg : MDiffAt g x；hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DifferentiableWithinAt.comp_mdifferentiableWithinAt`：DifferentiableWithi
nAt.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {t : Set
 F} {x : M} (hg : DifferentiableWithinAt …
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Differentiable.clm_apply`：Differentiable.clm_apply (hc : Differentiable 
𝕜 c) (hu : Differentiable 𝕜 u) : Differentiable 𝕜 fun y => (c y) (u y)
· 使用定理 `differentiable_fst`：differentiable_fst : Differentiable 𝕜 (Prod.fst : E 
× F -> E)
· 使用定理 `differentiable_snd`：differentiable_snd : Differentiable 𝕜 (Prod.snd : E 
× F -> F)
· 使用定理 `MDifferentiableAt.prodMk_space`：MDifferentiableAt.prodMk_space {f : M ->
 E'} {g : M -> E''} (hf : MDiffAt f x) (hg : MDiffAt g x) : MDifferentiableAt I 
𝓘(𝕜, E' × E'') (fun …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Applying a linear map to a vector is differentiable. Version in vector spaces. F
or a
version in nontrivial vector bundles, see `MDifferentiableAt.clm_apply_of_inCoor
dinates`.
-/
theorem MDifferentiableAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x ↦ g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ →L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])
/-
**MDifferentiableOn.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set
 M} (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x => g x (f x))
参数：hg : MDiff[s] g；hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableWithinAt.clm_apply`：MDifferentiableWithinAt.clm_apply {g 
: M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : MDiffAt[s] g x) (hf
 : MDiffAt[s] f x) : MD…
-/
theorem MDifferentiableOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x ↦ g x (f x)) :=
  fun x hx ↦ (hg x hx).clm_apply (hf x hx)
/-
**MDifferentiable.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} (hg : MDif
f g) (hf : MDiff f) : MDiff fun x => g x (f x)
参数：hg : MDiff g；hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableAt.clm_apply`：MDifferentiableAt.clm_apply {g : M -> F₁ ->
L[𝕜] F₂} {f : M -> F₁} {x : M} (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (
fun x => g x (f x…
-/
theorem MDifferentiable.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x ↦ g x (f x) :=
  fun x ↦ (hg x).clm_apply (hf x)
/-
**MDifferentiableWithinAt.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃
 ≃L[𝕜] F₄} {s : Set M} {x : M} (hf : MDiffAt[s] (fun x => ((f x).symm : F₂ ->L[𝕜
] F₁)) x) (hg : MDiffAt[s] (fun x => (g x : F₃ ->L[𝕜] F₄)) x) : MDiffAt[s] (fun 
y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x
参数：hf : MDiffAt[s] (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x；hg : MDiffAt[s] (fun
 x => (g x : F₃ ->L[𝕜] F₄)) x。
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
· 使用定理 `MDifferentiableWithinAt.clm_comp`：MDifferentiableWithinAt.clm_comp {g : 
M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M} (hg : MDiffAt[s] 
g x) (hf : MDiffAt[s] …
· 使用定理 `MDifferentiableWithinAt.clm_precomp`：MDifferentiableWithinAt.clm_precomp
 {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M} (hf : MDiffAt[s] f x) : MDiffAt[s] 
(fun y => (f y).precomp F…
· 使用定理 `MDifferentiableWithinAt.clm_postcomp`：MDifferentiableWithinAt.clm_postco
mp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {x : M} (hf : MDiffAt[s] f x) : MDiffAt[s
] (fun y => (f y).postcomp…
-/
theorem MDifferentiableWithinAt.cle_arrowCongr
    {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M} {x : M}
    (hf : MDiffAt[s] (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : MDiffAt[s] (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    MDiffAt[s] (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  show MDifferentiableWithinAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) s x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)
/-
**MDifferentiableAt.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜]
 F₄} {x : M} (hf : MDiffAt (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x) (hg : MDiff
At (fun x => (g x : F₃ ->L[𝕜] F₄)) x) : MDiffAt (fun y => (f y).arrowCongr (g y)
 : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x
参数：hf : MDiffAt (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x；hg : MDiffAt (fun x => 
(g x : F₃ ->L[𝕜] F₄)) x。
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
· 使用定理 `MDifferentiableAt.clm_comp`：MDifferentiableAt.clm_comp {g : M -> F₁ ->L[
𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M} (hg : MDiffAt g x) (hf : MDiffAt f x) : M
DiffAt (fun x =>…
· 使用定理 `MDifferentiableAt.clm_precomp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `MDifferentiableAt.clm_postcomp`：MDifferentiableAt.clm_postcomp {f : M ->
 F₂ ->L[𝕜] F₃} {x : M} (hf : MDiffAt f x) : MDiffAt (fun y => (f y).postcomp F₁ 
: M -> (F₁ ->L[𝕜] F₂…
-/
theorem MDifferentiableAt.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {x : M}
    (hf : MDiffAt (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)) x)
    (hg : MDiffAt (fun x ↦ (g x : F₃ →L[𝕜] F₄)) x) :
    MDiffAt (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) x :=
  show MDifferentiableAt I 𝓘(𝕜, (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄))
    (fun y ↦ (((f y).symm : F₂ →L[𝕜] F₁).precomp F₄).comp ((g y : F₃ →L[𝕜] F₄).postcomp F₁)) x
  from hf.clm_precomp (F₃ := F₄) |>.clm_comp <| hg.clm_postcomp (F₁ := F₁)
/-
**MDifferentiableOn.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜]
 F₄} {s : Set M} (hf : MDiff[s] (fun x => ((f x).symm : F₂ ->L[𝕜] F₁))) (hg : MD
iff[s] (fun x => (g x : F₃ ->L[𝕜] F₄))) : MDiff[s] (fun y => (f y).arrowCongr (g
 y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
参数：hf : MDiff[s] (fun x => ((f x).symm : F₂ ->L[𝕜] F₁))；hg : MDiff[s] (fun x => 
(g x : F₃ ->L[𝕜] F₄))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableWithinAt.cle_arrowCongr`：MDifferentiableWithinAt.cle_arro
wCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M} {x : M} (hf : M
DiffAt[s] (fun x => ((f x).s…
-/
theorem MDifferentiableOn.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : MDiff[s] (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : MDiff[s] (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    MDiff[s] (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x hx ↦
  (hf x hx).cle_arrowCongr (hg x hx)
/-
**MDifferentiable.cle_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F
₄} (hf : MDiff (fun x => ((f x).symm : F₂ ->L[𝕜] F₁))) (hg : MDiff (fun x => (g 
x : F₃ ->L[𝕜] F₄))) : MDiff (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F
₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
参数：hf : MDiff (fun x => ((f x).symm : F₂ ->L[𝕜] F₁))；hg : MDiff (fun x => (g x :
 F₃ ->L[𝕜] F₄))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableAt.cle_arrowCongr`：MDifferentiableAt.cle_arrowCongr {f : 
M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M} (hf : MDiffAt (fun x => ((f x).
symm : F₂ ->L[𝕜] F₁)) …
-/
theorem MDifferentiable.cle_arrowCongr {f : M → F₁ ≃L[𝕜] F₂} {g : M → F₃ ≃L[𝕜] F₄}
    (hf : MDiff (fun x ↦ ((f x).symm : F₂ →L[𝕜] F₁)))
    (hg : MDiff (fun x ↦ (g x : F₃ →L[𝕜] F₄))) :
    MDiff (fun y ↦ (f y).arrowCongr (g y) : M → (F₁ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₄)) := fun x ↦
  (hf x).cle_arrowCongr (hg x)
/-
**MDifferentiableWithinAt.clm_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ -
>L[𝕜] F₄} {s : Set M} {x : M} (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) : MDif
fAt[s] (fun x => (g x).prodMap (f x)) x
参数：hg : MDiffAt[s] g x；hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Differentiable.comp_mdifferentiableWithinAt`：Differentiable.comp_mdiffer
entiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M} (hg : Differenti
able 𝕜 g) (hf : MDiffAt[s] f x) :…
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `MDifferentiableWithinAt.prodMk_space`：MDifferentiableWithinAt.prodMk_spa
ce {f : M -> E'} {g : M -> E''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MD
ifferentiableWithinAt I 𝓘(…
-/
theorem MDifferentiableWithinAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    {x : M} (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

nonrec theorem MDifferentiableAt.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x ↦ (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)
/-
**MDifferentiableOn.clm_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] 
F₄} {s : Set M} (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x => (g x).p
rodMap (f x))
参数：hg : MDiff[s] g；hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableWithinAt.clm_prodMap`：MDifferentiableWithinAt.clm_prodMap
 {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M} {x : M} (hg : MDiff
At[s] g x) (hf : MDiffAt[…
-/
theorem MDifferentiableOn.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) :
    MDiff[s] (fun x ↦ (g x).prodMap (f x)) :=
  fun x hx ↦ (hg x hx).clm_prodMap (hf x hx)
/-
**MDifferentiable.clm_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄
} (hg : MDiff g) (hf : MDiff f) : MDiff fun x => (g x).prodMap (f x)
参数：hg : MDiff g；hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MDifferentiableAt.clm_prodMap`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
theorem MDifferentiable.clm_prodMap {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x ↦ (g x).prodMap (f x) :=
  fun x ↦ (hg x).clm_prodMap (hf x)

/-! ### Differentiability of scalar multiplication -/

section smul

open NormedSpace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {f : M → 𝕜} {g : M → V}

-- TODO: investigate inlining this proof entirely!
/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, if
at some point `x`, `f` has differential `f' : TangentSpace I x →L[𝕜] 𝕜` and `g` has differential
`g' : TangentSpace I x →L[𝕜] V` (both phrased using the predicate `HasMFDerivAt`), it follows that
their scalar multiplication `f • g` has differential `f x • g' + toSpanSingleton 𝕜 (g x) ∘L f'`.

In fact, the statement above is not literally true, because, for example, the differential of `g`
really takes values in the tangent space to `V` at `g x`, rather than in `V` itself. Of course, this
tangent space can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, which provides this
canonical identification. (It would also be possible to phrase the formula without this equiv,
instead using casting and definitional abuse.) -/
/-
**HasMFDerivAt.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, r
espectively, if
at some point `x`, `f` has differential `f' : TangentSpace I x →L[𝕜] 𝕜` and `g` 
has differential
`g' : TangentSpace I x →L[𝕜] V` (both phrased using the predicate `HasMFDerivAt`
), it follows that
their scalar multiplication `f • g` has differential `f x • g' + toSpanSingleton
 𝕜 (g x) ∘L f'`.

In fact, the statement above is not literally true, because, for example, the di
fferential of `g`
really takes values in the tangent space to `V` at `g x`, rather than in `V` its
elf. Of course, this
tangent space can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, w
hich provides this
canonical identification. (It would also be possible to phrase the formula witho
ut this equiv,
instead using casting and definitional abuse.)
-/
private lemma HasMFDerivAt.smul
    {f' : TangentSpace% x →L[𝕜] 𝕜}
    (hs : HasMFDerivAt% f x ((fromTangentSpace (f x)).symm.toContinuousLinearMap ∘L f'))
    {g' : TangentSpace% x →L[𝕜] V}
    (hg : HasMFDerivAt% g x ((fromTangentSpace (g x)).symm.toContinuousLinearMap ∘L g')) :
    -- canonically identify `g'` with a linear map into the tangent space at `(f • g) x`
    letI g'_ : TangentSpace% x →L[𝕜] TangentSpace 𝓘(𝕜, V) ((f • g) x) :=
      (fromTangentSpace _).symm.toContinuousLinearMap ∘L g'
    -- canonically identify `g x` with a linear map into a tangent space at `(f • g) x`
    letI gx : 𝕜 →L[𝕜] TangentSpace% ((f • g) x) :=
      toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x))
    -- now the main statement typechecks
    HasMFDerivAt% (f • g) x (f x • g'_ + gx ∘L f') := by
  constructor
  · exact hs.1.smul hg.1
  · simpa using! hs.2.smul hg.2
/-
**MDifferentiableWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.smul (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
 MDiffAt[s] (fun p => f p • g p) x
参数：hf : MDiffAt[s] f x；hg : MDiffAt[s] g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `ContMDiffSMul.contMDiff_smul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…
· 使用定理 `instContMDiffSMulModelWithCornersSelf`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {n : WithTop…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MDifferentiableWithinAt.prodMk`：MDifferentiableWithinAt.prodMk {f : M ->
 M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fu
n x => (f x, g x)) x
-/
theorem MDifferentiableWithinAt.smul
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun p ↦ f p • g p) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp_mdifferentiableWithinAt x
    (hf.prodMk hg)

@[to_fun]
/-
**MDifferentiableAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.smul (hf : MDiffAt f x) (hg : MDiffAt g x) : MDiffAt (f 
• g) x
参数：hf : MDiffAt f x；hg : MDiffAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `ContMDiffSMul.contMDiff_smul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…
· 使用定理 `instContMDiffSMulModelWithCornersSelf`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {n : WithTop…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MDifferentiableAt.prodMk`：MDifferentiableAt.prodMk {f : M -> M'} {g : M 
-> M''} (hf : MDiffAt f x) (hg : MDiffAt g x) : MDiffAt (fun x => (f x, g x)) x
-/
theorem MDifferentiableAt.smul (hf : MDiffAt f x)
    (hg : MDiffAt g x) : MDiffAt (f • g) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp x (hf.prodMk hg)

@[to_fun]
/-
**MDifferentiableOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.smul (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f •
 g)
参数：hf : MDiff[s] f；hg : MDiff[s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.smul`：MDifferentiableWithinAt.smul (hf : MDiffAt
[s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fun p => f p • g p) x
-/
theorem MDifferentiableOn.smul (hf : MDiff[s] f)
    (hg : MDiff[s] g) : MDiff[s] (f • g) :=
  fun x hx ↦ (hf x hx).smul (hg x hx)

@[to_fun]
/-
**MDifferentiable.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.smul (hf : MDiff f) (hg : MDiff g) : MDiff (f • g)
参数：hf : MDiff f；hg : MDiff g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.smul`：MDifferentiableAt.smul (hf : MDiffAt f x) (hg : 
MDiffAt g x) : MDiffAt (f • g) x
-/
theorem MDifferentiable.smul (hf : MDiff f) (hg : MDiff g) : MDiff (f • g) :=
  fun x ↦ (hf x).smul (hg x)

-- TODO: deprecate in favour of `mvfderiv_smul`, then delete this lemma
/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, i.e.
`mfderiv% (f • g) x = f x • mfderiv% g x + toSpanSingleton 𝕜 (g x) ∘L mfderiv% f x`,
but this doesn't typecheck because `mfderiv% (f • g) x` and `mfderiv% g x` take values in different
tangent spaces -- respectively the tangent spaces to `V` at `(f • g) x` and `g x`. Of course, both
these tangent spaces can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, which provides this
canonical identification. (It would also be possible to phrase the formula without this equiv,
instead using casting and definitional abuse.)

It is good practice to use the equiv `NormedSpace.fromTangentSpace` throughout a computation. If
this is done, typically `mfderiv% (f • g) x` will only turn up paired with this equiv (i.e., in an
expression `(fromTangentSpace _) ∘L mfderiv% (f • g) x`), and the more convenient lemma
`fromTangentSpace_mfderiv_smul` (see below) can be used instead. -/
/-
**mfderiv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, r
espectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, i.e.
`mfderiv% (f • g) x = f x • mfderiv% g x + toSpanSingleton 𝕜 (g x) ∘L mfderiv% f
 x`,
but this doesn't typecheck because `mfderiv% (f • g) x` and `mfderiv% g x` take 
values in different
tangent spaces -- respectively the tangent spaces to `V` at `(f • g) x` and `g x
`. Of course, both
these tangent spaces can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, w
hich provides this
canonical identification. (It would also be possible to phrase the formula witho
ut this equiv,
instead using casting and definitional abuse.)

It is good practice to use the equiv `NormedSpace.fromTangentSpace` throughout a
 computation. If
this is done, typically `mfderiv% (f • g) x` will only turn up paired with this 
equiv (i.e., in an
expression `(fromTangentSpace _) ∘L mfderiv% (f • g) x`), and the more convenien
t lemma
`fromTangentSpace_mfderiv_smul` (see below) can be used instead.
-/
private lemma mfderiv_smul (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (f • g) x
    = f x • (fromTangentSpace _).symm.toContinuousLinearMap ∘L
      ((fromTangentSpace (g x)).toContinuousLinearMap ∘L mfderiv% g x)
    + toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x)) ∘L
      ((fromTangentSpace (f x)).toContinuousLinearMap ∘L mfderiv% f x) :=
  (hf.hasMFDerivAt.smul hg.hasMFDerivAt).mfderiv

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, i.e.
`mfderiv% (f • g) x = f x • mfderiv% g x + toSpanSingleton 𝕜 (g x) ∘L mfderiv% f x`,
but this doesn't typecheck because `mfderiv% (f • g) x` and `mfderiv% g x` take values in different
tangent spaces -- respectively the tangent spaces to `V` at `(f • g) x` and `g x`. Of course, both
these tangent spaces can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, which provides this
canonical identification. (It would also be possible to phrase the formula without this equiv,
instead using casting and definitional abuse.) -/
/-
**fromTangentSpace_mfderiv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, r
espectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, i.e.
`mfderiv% (f • g) x = f x • mfderiv% g x + toSpanSingleton 𝕜 (g x) ∘L mfderiv% f
 x`,
but this doesn't typecheck because `mfderiv% (f • g) x` and `mfderiv% g x` take 
values in different
tangent spaces -- respectively the tangent spaces to `V` at `(f • g) x` and `g x
`. Of course, both
these tangent spaces can be canonically identified with `V`.

This lemma phrases the formula using the equiv `NormedSpace.fromTangentSpace`, w
hich provides this
canonical identification. (It would also be possible to phrase the formula witho
ut this equiv,
instead using casting and definitional abuse.)
-/
private lemma fromTangentSpace_mfderiv_smul (hf : MDiffAt f x) (hg : MDiffAt g x) :
    (fromTangentSpace ((f • g) x)).toContinuousLinearMap ∘L mfderiv% (f • g) x
    = f x • (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% g x
    + toSpanSingleton 𝕜 (g x) ∘L (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% f x := by
  rw [mfderiv_smul hf hg]
  rfl

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, but to get it to typecheck
we need a phrasing involving the canonical identification `NormedSpace.fromTangentSpace` between
the vector space `V` and the tangent space to this vector space at any point. This is because two
different tangent spaces (at `(f • g) x` and `g x`) appear in the equation.

This is a defeq variant of the main lemma `fromTangentSpace_mfderiv_smul`, in which we work in the
tangent space at `f x • g x` (the simp-normal form) rather than at `(f • g) x`. -/
/-
**fromTangentSpace_mfderiv_smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, r
espectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g`.

Mathematically speaking the formula is `d(f • g) = f • dg + df ⊗ g`, but to get 
it to typecheck
we need a phrasing involving the canonical identification `NormedSpace.fromTange
ntSpace` between
the vector space `V` and the tangent space to this vector space at any point. Th
is is because two
different tangent spaces (at `(f • g) x` and `g x`) appear in the equation.

This is a defeq variant of the main lemma `fromTangentSpace_mfderiv_smul`, in wh
ich we work in the
tangent space at `f x • g x` (the simp-normal form) rather than at `(f • g) x`.
-/
private lemma fromTangentSpace_mfderiv_smul' (hf : MDiffAt f x) (hg : MDiffAt g x) :
    (fromTangentSpace (f x • g x)).toContinuousLinearMap ∘L mfderiv% (f • g) x
    = f x • (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% g x
    + toSpanSingleton 𝕜 (g x) ∘L (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% f x :=
  fromTangentSpace_mfderiv_smul hf hg

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g` in the direction of
the tangent vector `v`.

Mathematically speaking the formula is `d(f • g)(v) = f • dg(v) + df(v) • g`, but to get it to
typecheck we need a phrasing involving the canonical identification `NormedSpace.fromTangentSpace`
between the vector space `V` and the tangent space to this vector space at any point. This is
because two different tangent spaces (at `(f • g) x` and `g x`) appear in the equation. -/
/-
**fromTangentSpace_mfderiv_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, r
espectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g` 
in the direction of
the tangent vector `v`.

Mathematically speaking the formula is `d(f • g)(v) = f • dg(v) + df(v) • g`, bu
t to get it to
typecheck we need a phrasing involving the canonical identification `NormedSpace
.fromTangentSpace`
between the vector space `V` and the tangent space to this vector space at any p
oint. This is
because two different tangent spaces (at `(f • g) x` and `g x`) appear in the eq
uation.
-/
private lemma fromTangentSpace_mfderiv_smul_apply (hf : MDiffAt f x) (hg : MDiffAt g x)
    (v : TangentSpace% x) :
    fromTangentSpace _ (mfderiv% (f • g) x v)
    = f x • fromTangentSpace _ (mfderiv% g x v) + fromTangentSpace _ (mfderiv% f x v) • g x := by
  simpa using congr($(fromTangentSpace_mfderiv_smul hf hg) v)

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/-- Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, respectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g` in the direction of
the tangent vector `v`.

Mathematically speaking the formula is `d(f • g)(v) = f • dg(v) + df(v) • g`, but to get it to
typecheck we need a phrasing involving the canonical identification `NormedSpace.fromTangentSpace`
between the vector space `V` and the tangent space to this vector space at any point. This is
because two different tangent spaces (at `(f • g) x` and `g x`) appear in the equation.

This is a defeq variant of the main lemma `fromTangentSpace_mfderiv_smul_apply`, in which we work in
the tangent space at `f x • g x` (the simp-normal form) rather than at `(f • g) x`. -/
/-
**fromTangentSpace_mfderiv_smul_apply'** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `f`, `g` from a manifold into a field `𝕜` and `𝕜`-vector space `V`, r
espectively, the
formula for the `mfderiv` (differential) of their scalar multiplication `f • g` 
in the direction of
the tangent vector `v`.

Mathematically speaking the formula is `d(f • g)(v) = f • dg(v) + df(v) • g`, bu
t to get it to
typecheck we need a phrasing involving the canonical identification `NormedSpace
.fromTangentSpace`
between the vector space `V` and the tangent space to this vector space at any p
oint. This is
because two different tangent spaces (at `(f • g) x` and `g x`) appear in the eq
uation.

This is a defeq variant of the main lemma `fromTangentSpace_mfderiv_smul_apply`,
 in which we work in
the tangent space at `f x • g x` (the simp-normal form) rather than at `(f • g) 
x`.
-/
private lemma fromTangentSpace_mfderiv_smul_apply' (hf : MDiffAt f x) (hg : MDiffAt g x)
    (v : TangentSpace% x) :
    fromTangentSpace (f x • g x) (mfderiv% (f • g) x v)
    = f x • fromTangentSpace _ (mfderiv% g x v) + fromTangentSpace _ (mfderiv% f x v) • g x :=
  fromTangentSpace_mfderiv_smul_apply hf hg v

end smul

/-! ### Exterior derivative of a vector-valued function -/

variable (I) in
/-- `mvfderivWithin I J f s x` is the `mfderiv` of a vector-valued function `f` on `M` at `x`
within the set `s`, but taking values in the target normed space directly.
The difference to `mfderivWithin` is explained in the module-docstring for
`Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`.

Future: this could be generalised to functions into additive torsors over abelian Lie groups.
-/
@[expose]
/-
**mvfderivWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mvfderivWithin (g : M -> F) (s : Set M) : Π x : M, TangentSpace I x ->L[𝕜]
 F
参数：g : M -> F；s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mvfderivWithin I J f s x` is the `mfderiv` of a vector-valued function `f` on `
M` at `x`
within the set `s`, but taking values in the target normed space directly.
The difference to `mfderivWithin` is explained in the module-docstring for
`Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`.

Future: this could be generalised to functions into additive torsors over abelia
n Lie groups.
-/
noncomputable def mvfderivWithin (g : M → F) (s : Set M) :
    Π x : M, TangentSpace I x →L[𝕜] F :=
  fun x ↦ (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv[s] g x)

variable (I) in
/-- `mvfderiv I J f x` is the `mfderiv` of a vector-valued function `f` on `M` at `x`,
but taking values in the target normed space directly.
The difference to `mfderiv` is explained in the module-docstring for
`Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`.

Future: this could be generalised to functions into additive torsors over abelian Lie groups.
-/
@[expose]
/-
**mvfderiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mvfderiv (g : M -> F) : Π x : M, TangentSpace% x ->L[𝕜] F
参数：g : M -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mvfderiv I J f x` is the `mfderiv` of a vector-valued function `f` on `M` at `x
`,
but taking values in the target normed space directly.
The difference to `mfderiv` is explained in the module-docstring for
`Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`.

Future: this could be generalised to functions into additive torsors over abelia
n Lie groups.
-/
noncomputable def mvfderiv (g : M → F) :
    Π x : M, TangentSpace% x →L[𝕜] F :=
  fun x ↦ (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x)
@[deprecated (since := "2026-05-17")] alias extDerivFun := mvfderiv

namespace Manifold
open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic

/-- `d[s] f x` (scoped to the `Manifold` namespace) elaborates to `mvfderivWithin I J f s x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "d[" s:term "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, _tgtI) ← findModels e none
  mkAppM ``mvfderivWithin #[srcI, e, es]

/-- `d% f x` (scoped to the `Manifold` namespace) elaborates to `mvfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "d%" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, _tgtI) ← findModels e none
  mkAppM ``mvfderiv #[srcI, e]

open Bundle PrettyPrinter Delaborator SubExpr

/-- Delaborator for `mvfderivWithin`. -/
-- There is no need to special-case any arguments which could use the `T%` elaborator:
-- the argument to `mvfderivWithin` is a vector-valued function, which a map to a total space
-- can never be.
@[app_delab mvfderivWithin] meta def delabMVFDerivWithin : Delab := do
  whenPPOption getPPNotation do
  withOverApp 16 do
  let ss ← withAppArg delab
  let fs ← withNaryArg 14 <| delab
  `(d[$ss] $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `mvfderiv`. -/
-- There is no need to special-case any arguments which could use the `T%` elaborator:
-- the argument to `mvfderiv` is a vector-valued function, which a map to a total space
-- can never be.
@[app_delab mvfderiv] meta def delabMVFDeriv : Delab := do
  whenPPOption getPPNotation do
  withOverApp 15 do
  let fs ← withAppArg delab
  `(d% $fs) >>= annotateGoToSyntaxDef

end Manifold

/-
**mvfderivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {F : Type u_8} [inst_6 : NormedAddCom
mGroup F]   [inst_7 : NormedSpace 𝕜 F] {f : M → F}, d[Set.univ] f = d% f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, mfld_simps] lemma mvfderivWithin_univ {f : M → F} : d[(univ : Set M)] f = d% f := by
  ext X
  simp [mvfderiv, mvfderivWithin]
/-
**mvfderivWithin_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_const (c : F) {x : M} : d[s] (fun _ : M => c) x = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderivWithin_const`：mfderivWithin_const : mfderiv[s] (fun _ : M => c) x
 = (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mvfderivWithin_const (c : F) {x : M} : d[s] (fun _ : M ↦ c) x = 0 := by
  simp [mvfderivWithin, mfderivWithin_const]

@[simp, to_fun mvfderivWithin_fun_add]
/-
**mvfderivWithin_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_add {g g' : M -> F} {x : M} (hg : MDiffAt[s] g x) (hg' : MD
iffAt[s] g' x) (hs : UniqueMDiffAt[s] x) : d[s](g + g') x = d[s]g x + d[s]g' x
参数：hg : MDiffAt[s] g x；hg' : MDiffAt[s] g' x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderivWithin_add`：mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt
[s] g z) (hs : UniqueMDiffAt[s] z) : (mfderiv[s] (f + g) z : TangentSpace% z ->L
[𝕜] E')…
-/
lemma mvfderivWithin_add {g g' : M → F} {x : M}
    (hg : MDiffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffAt[s] x) :
    d[s](g + g') x = d[s]g x + d[s]g' x := by
  simp [mvfderivWithin, mfderivWithin_add hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_sub]
/-
**mvfderivWithin_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_sub {g g' : M -> F} {x : M} (hg : MDiffAt[s] g x) (hg' : MD
iffAt[s] g' x) (hs : UniqueMDiffAt[s] x) : d[s](g - g') x = d[s]g x - d[s]g' x
参数：hg : MDiffAt[s] g x；hg' : MDiffAt[s] g' x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderivWithin_sub`：mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt
[s] g z) (hs : UniqueMDiffAt[s] z) : (mfderiv[s] (f - g) z : TangentSpace% z ->L
[𝕜] E')…
-/
lemma mvfderivWithin_sub {g g' : M → F} {x : M}
    (hg : MDiffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffAt[s] x) :
    d[s](g - g') x = d[s]g x - d[s]g' x := by
  simp [mvfderivWithin, mfderivWithin_sub hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_neg]
/-
**mvfderivWithin_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_neg {g : M -> F} {x : M} (hs : UniqueMDiffAt[s] x) : d[s](-
g) x = -d[s]g x
参数：hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderivWithin_neg`：mfderivWithin_neg (hs : UniqueMDiffAt[s] x) : mfderiv
[s] (-f) x = -mfderiv[s] f x
-/
lemma mvfderivWithin_neg {g : M → F} {x : M} (hs : UniqueMDiffAt[s] x) :
    d[s](-g) x = -d[s]g x := by
  simp [mvfderivWithin, mfderivWithin_neg hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_smul]
/-
**mvfderivWithin_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_smul {a : M -> 𝕜} (ha : MDiffAt[s] a x) {g : M -> F} (hg : 
MDiffAt[s] g x) (hs : UniqueMDiffAt[s] x) : d[s](a • g) x = a x • d[s] g x + (d[
s] a x).smulRight (g x)
参数：ha : MDiffAt[s] a x；hg : MDiffAt[s] g x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousWithinAt.smul`：ContinuousWithinAt.smul (hf : ContinuousWithinA
t f s b) (hg : ContinuousWithinAt g s b) : ContinuousWithinAt (f • g) s b
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousLinearMap.smulRight.congr_simp`：∀ {M₁ : Type u_4} [inst : Topo
logicalSpace M₁] [inst_1 : AddCommMonoid M₁] {M₂ : Type u_6}   [inst_2 : Topolog
icalSpace M₂] [inst_3 : AddCom…
· 使用定理 `HasFDerivWithinAt.smul`：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c
 c' s x) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f'
 + c'.smulRi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
lemma mvfderivWithin_smul {a : M → 𝕜} (ha : MDiffAt[s] a x) {g : M → F} (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    d[s](a • g) x =
      a x • d[s] g x + (d[s] a x).smulRight (g x) := by
  refine HasMFDerivWithinAt.mfderivWithin ⟨ha.1.smul hg.1, ?_⟩ hs
  convert! ha.hasMFDerivWithinAt.2.smul hg.hasMFDerivWithinAt.2
  simp
  rfl

@[simp, to_fun mvfderivWithin_fun_mul]
/-
**mvfderivWithin_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_mul {f g : M -> 𝕜} {x : M} (hf : MDiffAt[s] f x) (hg : MDif
fAt[s] g x) (hs : UniqueMDiffAt[s] x) : d[s](f * g) x = f x • d[s]g x + (g x) • 
(d[s]f x)
参数：hf : MDiffAt[s] f x；hg : MDiffAt[s] g x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `mvfderivWithin_smul`：mvfderivWithin_smul {a : M -> 𝕜} (ha : MDiffAt[s] a
 x) {g : M -> F} (hg : MDiffAt[s] g x) (hs : UniqueMDiffAt[s] x) : d[s](a • g) x
 = a x • …
-/
lemma mvfderivWithin_mul {f g : M → 𝕜} {x : M} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    d[s](f * g) x = f x • d[s]g x + (g x) • (d[s]f x) := by
  convert! mvfderivWithin_smul hf hg hs
  ext v
  simp [mul_comm]

@[simp]
/-
**mvfderivWithin_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderivWithin_zero {s : Set M} (hs : UniqueMDiffAt[s] x) : d[s] (0 : M ->
 F) x = 0
参数：hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mvfderivWithin_add`：mvfderivWithin_add {g g' : M -> F} {x : M} (hg : MDi
ffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffAt[s] x) : d[s](g + g') x 
= d[s]g …
· 使用定理 `mdifferentiableWithinAt_const`：mdifferentiableWithinAt_const : MDiffAt[s
] (fun _ : M => c) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma mvfderivWithin_zero {s : Set M} (hs : UniqueMDiffAt[s] x) :
    d[s] (0 : M → F) x = 0 := by
  have : d[s] (0 : M → F) x + d[s] (0 : M → F) x = d[s] (0 : M → F) x := by
    rw [← mvfderivWithin_add (by exact mdifferentiableWithinAt_const)
      (by exact mdifferentiableWithinAt_const) hs]
    simp
  simpa using this
/-
**mvfderiv_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_const (c : F) {x : M} : d% (fun _ : M => c) x = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderiv_const`：mfderiv_const : mfderiv% (fun _ : M => c) x = (0 : Tangen
tSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mvfderiv_const (c : F) {x : M} : d% (fun _ : M ↦ c) x = 0 := by
  simp [mvfderiv, mfderiv_const]

@[simp, to_fun mvfderiv_fun_add]
/-
**mvfderiv_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_add {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' 
x) : d% (g + g') x = d% g x + d% g' x
参数：hg : MDiffAt g x；hg' : MDiffAt g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderiv_add`：mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) : (mfderi
v% (f + g) z : TangentSpace% z ->L[𝕜] E') = (by exact mfderiv% f z) + (by exact 
m…
-/
lemma mvfderiv_add {g g' : M → F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x) :
    d% (g + g') x = d% g x + d% g' x := by
  simp [mvfderiv, mfderiv_add hg hg']
  rfl
@[deprecated (since := "2026-05-17")] alias extDerivFun_add := mvfderiv_add

@[simp, to_fun mvfderiv_fun_sub]
/-
**mvfderiv_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_sub {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' 
x) : d% (g - g') x = d% g x - d% g' x
参数：hg : MDiffAt g x；hg' : MDiffAt g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderiv_sub`：mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) : (mfderi
v% (f - g) z : TangentSpace% z ->L[𝕜] E') = (by exact mfderiv% f z) - (by exact 
m…
-/
lemma mvfderiv_sub {g g' : M → F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x) :
    d% (g - g') x = d% g x - d% g' x := by
  simp [mvfderiv, mfderiv_sub hg hg']
  rfl

@[simp, to_fun mvfderiv_fun_neg]
/-
**mvfderiv_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_neg {g : M -> F} {x : M} : d% (-g) x = -d% g x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderiv_neg`：mfderiv_neg : mfderiv% (-f) x = -mfderiv% f x
-/
lemma mvfderiv_neg {g : M → F} {x : M} :
    d% (-g) x = -d% g x := by
  simp [mvfderiv, mfderiv_neg]
  rfl

@[simp, to_fun mvfderiv_fun_smul]
/-
**mvfderiv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_smul {x : M} {a : M -> 𝕜} (ha : MDiffAt a x) {g : M -> F} (hg : M
DiffAt g x) : d% (a • g) x = a x • d% g x + (d% a x).smulRight (g x)
参数：ha : MDiffAt a x；hg : MDiffAt g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Geometry.Manifold.MFDeriv.NormedSpace.0.fromTangentSpac
e_mfderiv_smul_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : T
ype u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type 
u_…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mvfderiv_smul {x : M} {a : M → 𝕜} (ha : MDiffAt a x) {g : M → F} (hg : MDiffAt g x) :
    d% (a • g) x = a x • d% g x + (d% a x).smulRight (g x) := by
  ext v
  simp [mvfderiv, -Pi.smul_apply', fromTangentSpace_mfderiv_smul_apply ha hg]

@[simp, to_fun mvfderiv_fun_mul]
/-
**mvfderiv_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_mul {f g : M -> 𝕜} {x : M} (hf : MDiffAt f x) (hg : MDiffAt g x) 
: d% (f * g) x = f x • d% g x + (g x) • (d% f x)
参数：hf : MDiffAt f x；hg : MDiffAt g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `_private.Mathlib.Geometry.Manifold.MFDeriv.NormedSpace.0.mfderiv_smul`：∀
 {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : Norm
edAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.comp_add`：comp_add [ContinuousAdd M₂] [ContinuousAdd
 M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f₂ : M₁ ->SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f
₁ + g ∘SL f₂
· 使用定理 `ContinuousLinearMap.comp_smulₛₗ`：comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [S
MulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂] [ContinuousConstSMul R₃ M₃] (
h : M₂ ->SL[σ₂₃] M₃) …
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mvfderiv_mul {f g : M → 𝕜} {x : M} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f * g) x = f x • d% g x + (g x) • (d% f x) := by
  ext v
  simp only [mvfderiv, ← smul_eq_mul, mfderiv_smul hf hg]
  simp [mul_comm _ (g x)]

@[simp]
/-
**mvfderiv_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mvfderiv_zero {x : M} : d% (0 : M -> F) x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mvfderiv_add`：mvfderiv_add {g g' : M -> F} {x : M} (hg : MDiffAt g x) (h
g' : MDiffAt g' x) : d% (g + g') x = d% g x + d% g' x
· 使用定理 `mdifferentiable_const`：mdifferentiable_const : MDiff fun _ : M => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma mvfderiv_zero {x : M} : d% (0 : M → F) x = 0 := by
  have : d% (0 : M → F) x + d% (0 : M → F) x = d% (0 : M → F) x := by
    rw [← mvfderiv_add (by exact mdifferentiable_const ..) (by exact mdifferentiable_const ..)]
    simp
  simpa using this
@[deprecated (since := "2026-05-17")] alias extDerivFun_zero := mvfderiv_zero

-- TODO: the next two lemmas are more type correct than their `mvfderiv` cousins, but not entirely:
-- the right hand side should be of the form `fderiv ∘SL TangentSpaceCastModel`.
/-
**MDifferentiableWithinAt.mvfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentia
bleWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {s : Set M} {x : M} {f : M → E'},   MD
iffAt[s] f x →     d[s] f x =       fderivWithin 𝕜 (writtenInExtChartAt I (model
WithCornersSelf 𝕜 E') x f)         (↑(extChartAt I x).symm ⁻¹' s ∩ Set.range ↑I)
 (↑(extChartAt I x) x)
参数：writtenInExtChartAt I (modelWithCornersSelf 𝕜 E') x f；↑(extChartAt I x).symm 
⁻¹' s ∩ Set.range ↑I；↑(extChartAt I x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
-/
protected theorem MDifferentiableWithinAt.mvfderivWithin {f : M → E'} (h : MDiffAt[s] f x) :
    d[s] f x = fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, E') x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  convert! h.mfderivWithin
/-
**MDifferentiableAt.mvfderiv** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {x : M} {f : M → E'},   MDiffAt f x → 
    d% f x = fderivWithin 𝕜 (writtenInExtChartAt I (modelWithCornersSelf 𝕜 E') x
 f) (Set.range ↑I) (↑(extChartAt I x) x)
参数：writtenInExtChartAt I (modelWithCornersSelf 𝕜 E') x f；Set.range ↑I；↑(extChart
At I x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
-/
protected theorem MDifferentiableAt.mvfderiv {f : M → E'} (h : MDiffAt f x) :
    d% f x = fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, E') x f) (range I) (extChartAt I x x) := by
  convert! h.mfderiv

/-! ## Composition lemmas for `mvfderiv(Within)` -/
section

variable {f : M' → M} {g : M → 𝕜} {x : M'} {y : M} {u : Set M} {s : Set M'}

/-
**mvfderivWithin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderivWithin_comp (x : M') (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f 
x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : d[s] (g ∘ f) x = (d[u] 
g (f x)).comp (mfderiv[s] f x)
参数：x : M'；hg : MDiffAt[u] g (f x)；hf : MDiffAt[s] f x；h : s subseteq f ⁻¹' u；hxs
 : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
-/
theorem mvfderivWithin_comp (x : M') (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
    (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x) :=
  mfderivWithin_comp x hg hf h hxs
/-
**mvfderivWithin_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderivWithin_comp_of_eq (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h :
 s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) : d[s] (g ∘ f) x 
= (d[u] g y).comp (mfderiv[s] f x)
参数：hg : MDiffAt[u] g y；hf : MDiffAt[s] f x；h : s subseteq f ⁻¹' u；hxs : UniqueMD
iffAt[s] x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_comp_of_eq`：mfderivWithin_comp_of_eq {x : M} {y : M'} (hg 
: MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMD
iffAt[s] x) (h…
-/
theorem mvfderivWithin_comp_of_eq (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x)
    (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    d[s] (g ∘ f) x = (d[u] g y).comp (mfderiv[s] f x) :=
  mfderivWithin_comp_of_eq hg hf h hxs hy
/-
**mvfderivWithin_comp_of_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderivWithin_comp_of_preimage_mem_nhdsWithin (x : M') (hg : MDiffAt[u] g
 (f x)) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x)
 : d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x)
参数：x : M'；hg : MDiffAt[u] g (f x)；hf : MDiffAt[s] f x；h : f ⁻¹' u in 𝓝[s] x；hxs 
: UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_comp_of_preimage_mem_nhdsWithin`：mfderivWithin_comp_of_pre
image_mem_nhdsWithin (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : f ⁻¹' 
u in 𝓝[s] x) (hxs : UniqueMDiffAt[s…
-/
theorem mvfderivWithin_comp_of_preimage_mem_nhdsWithin (x : M') (hg : MDiffAt[u] g (f x))
    (hf : MDiffAt[s] f x) (h : f ⁻¹' u ∈ 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x) :=
  mfderivWithin_comp_of_preimage_mem_nhdsWithin x hg hf h hxs
/-
**mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq (x : M') (hg : MDiffA
t[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] 
x) (hy : f x = y) : d[s] (g ∘ f) x = (d[u] g y).comp (mfderiv[s] f x)
参数：x : M'；hg : MDiffAt[u] g y；hf : MDiffAt[s] f x；h : f ⁻¹' u in 𝓝[s] x；hxs : Un
iqueMDiffAt[s] x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq`：mfderivWithin_comp_
of_preimage_mem_nhdsWithin_of_eq {y : M'} (hg : MDiffAt[u] g y) (hf : MDiffAt[s]
 f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : Uniq…
-/
theorem mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq (x : M') (hg : MDiffAt[u] g y)
    (hf : MDiffAt[s] f x) (h : f ⁻¹' u ∈ 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    d[s] (g ∘ f) x = (d[u] g y).comp (mfderiv[s] f x) :=
  mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq x hg hf h hxs hy
/-
**mvfderiv_comp_mfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderiv_comp_mfderivWithin (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt[
s] f x) (hxs : UniqueMDiffAt[s] x) : d[s] (g ∘ f) x = (d% g (f x)).comp (mfderiv
[s] f x)
参数：x : M'；hg : MDiffAt g (f x)；hf : MDiffAt[s] f x；hxs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_mfderivWithin`：mfderiv_comp_mfderivWithin (hg : MDiffAt g (
f x)) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] (g ∘ f) x = 
(mfderiv% g (f x…
-/
theorem mvfderiv_comp_mfderivWithin
    (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d% g (f x)).comp (mfderiv[s] f x) :=
  mfderiv_comp_mfderivWithin x hg hf hxs
/-
**mvfderiv_comp_mfderivWithin_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderiv_comp_mfderivWithin_of_eq (hg : MDiffAt g y) (hf : MDiffAt[s] f x)
 (hxs : UniqueMDiffAt[s] x) (hy : f x = y) : d[s] (g ∘ f) x = (d% g y).comp (mfd
eriv[s] f x)
参数：hg : MDiffAt g y；hf : MDiffAt[s] f x；hxs : UniqueMDiffAt[s] x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_mfderivWithin_of_eq`：mfderiv_comp_mfderivWithin_of_eq {x : 
M} {y : M'} (hg : MDiffAt g y) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) 
(hy : f x = y) : mfder…
-/
theorem mvfderiv_comp_mfderivWithin_of_eq
    (hg : MDiffAt g y) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    d[s] (g ∘ f) x = (d% g y).comp (mfderiv[s] f x) :=
  mfderiv_comp_mfderivWithin_of_eq hg hf hxs hy
/-
**mvfderiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderiv_comp (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : d% (g ∘
 f) x = (d% g (f x)).comp (mfderiv% f x)
参数：x : M'；hg : MDiffAt g (f x)；hf : MDiffAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
-/
theorem mvfderiv_comp (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    d% (g ∘ f) x = (d% g (f x)).comp (mfderiv% f x) :=
  mfderiv_comp x hg hf
/-
**mvfderiv_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderiv_comp_of_eq {y : M} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f 
x = y) : d% (g ∘ f) x = (d% g (f x)).comp (mfderiv% f x)
参数：hg : MDiffAt g y；hf : MDiffAt f x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_of_eq`：mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDiffAt g 
y) (hf : MDiffAt f x) (hy : f x = y) : mfderiv% (g ∘ f) x = (mfderiv% g (f x)).c
omp (mfd…
-/
theorem mvfderiv_comp_of_eq {y : M} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) :
    d% (g ∘ f) x = (d% g (f x)).comp (mfderiv% f x) :=
  mfderiv_comp_of_eq hg hf hy
/-
**mvfderiv_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderiv_comp_apply (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v 
: TangentSpace% x) : d% (g ∘ f) x v = (d% g (f x)) ((mfderiv% f x) v)
参数：x : M'；hg : MDiffAt g (f x)；hf : MDiffAt f x；v : TangentSpace% x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_apply`：mfderiv_comp_apply (hg : MDiffAt g (f x)) (hf : MDif
fAt f x) (v : TangentSpace% x) : mfderiv% (g ∘ f) x v = (mfderiv% g (f x)) ((mfd
eriv% f …
-/
theorem mvfderiv_comp_apply
    (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentSpace% x) :
    d% (g ∘ f) x v = (d% g (f x)) ((mfderiv% f x) v) :=
  mfderiv_comp_apply x hg hf v
/-
**mvfderiv_comp_apply_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mvfderiv_comp_apply_of_eq (x : M') (hg : MDiffAt g y) (hf : MDiffAt f x) (
hy : f x = y) (v : TangentSpace% x) : d% (g ∘ f) x v = (d% g y) ((mfderiv% f x) 
v)
参数：x : M'；hg : MDiffAt g y；hf : MDiffAt f x；hy : f x = y；v : TangentSpace% x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_apply_of_eq`：mfderiv_comp_apply_of_eq {y : M'} (hg : MDiffA
t g y) (hf : MDiffAt f x) (hy : f x = y) (v : TangentSpace% x) : mfderiv% (g ∘ f
) x v = (mfder…
-/
theorem mvfderiv_comp_apply_of_eq
    (x : M') (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) (v : TangentSpace% x) :
    d% (g ∘ f) x v = (d% g y) ((mfderiv% f x) v) :=
  mfderiv_comp_apply_of_eq x hg hf hy v

end

