/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Calculus in inner product spaces

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `NormedSpace ℝ E`
instance. Though we can deduce this structure from `InnerProductSpace 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[NormedSpace ℝ E]`.

We also prove that functions to a `EuclideanSpace` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `PiLp`.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter

section DerivInner

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) [NormedSpace ℝ E]

/-- Derivative of the inner product. -/
/-
**fderivInnerCLM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fderivInnerCLM (p : E × E) : E × E ->L[Real] 𝕜
参数：p : E × E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Derivative of the inner product.
-/
def fderivInnerCLM (p : E × E) : E × E →L[ℝ] 𝕜 :=
  isBoundedBilinearMap_inner.deriv p

@[simp]
/-
**fderivInnerCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivInnerCLM_apply (p x : E × E) : fderivInnerCLM 𝕜 p x = ⟪p.1, x.2⟫ + ⟪
x.1, p.2⟫
参数：p x : E × E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fderivInnerCLM_apply (p x : E × E) : fderivInnerCLM 𝕜 p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ :=
  rfl

variable {𝕜}
/-
**contDiff_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_inner {n} : ContDiff Real n fun p : E × E => ⟪p.1, p.2⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [in
st_3 : NormedSpa…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem contDiff_inner {n} : ContDiff ℝ n fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMap_inner.contDiff
/-
**contDiffAt_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_inner {p : E × E} {n} : ContDiffAt Real n (fun p : E × E => ⟪p.
1, p.2⟫) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_inner`：contDiff_inner {n} : ContDiff Real n fun p : E × E => ⟪p
.1, p.2⟫
-/
theorem contDiffAt_inner {p : E × E} {n} : ContDiffAt ℝ n (fun p : E × E => ⟪p.1, p.2⟫) p :=
  ContDiff.contDiffAt contDiff_inner
/-
**differentiable_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_inner : Differentiable Real fun p : E × E => ⟪p.1, p.2⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.differentiableAt`：IsBoundedBilinearMap.differentiab
leAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : DifferentiableAt 𝕜 b p
· 使用定理 `isBoundedBilinearMap_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [in
st_3 : NormedSpa…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem differentiable_inner : Differentiable ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMap_inner.differentiableAt

variable (𝕜)
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : G → E} {f' g' : G →L[ℝ] E}
  {s : Set G} {x : G} {n : WithTop ℕ∞}
/-
**ContDiffWithinAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.inner (hf : ContDiffWithinAt Real n f s x) (hg : ContDiff
WithinAt Real n g s x) : ContDiffWithinAt Real n (fun x => ⟪f x, g x⟫) s x
参数：hf : ContDiffWithinAt Real n f s x；hg : ContDiffWithinAt Real n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `contDiffAt_inner`：contDiffAt_inner {p : E × E} {n} : ContDiffAt Real n (
fun p : E × E => ⟪p.1, p.2⟫) p
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
-/
theorem ContDiffWithinAt.inner (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x) :
    ContDiffWithinAt ℝ n (fun x => ⟪f x, g x⟫) s x :=
  contDiffAt_inner.comp_contDiffWithinAt x (hf.prodMk hg)

nonrec theorem ContDiffAt.inner (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  hf.inner 𝕜 hg
/-
**ContDiffOn.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.inner (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s)
 : ContDiffOn Real n (fun x => ⟪f x, g x⟫) s
参数：hf : ContDiffOn Real n f s；hg : ContDiffOn Real n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.inner`：ContDiffWithinAt.inner (hf : ContDiffWithinAt Re
al n f s x) (hg : ContDiffWithinAt Real n g s x) : ContDiffWithinAt Real n (fun 
x => ⟪f x, g…
-/
theorem ContDiffOn.inner (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner 𝕜 (hg x hx)
/-
**ContDiff.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.inner (hf : ContDiff Real n f) (hg : ContDiff Real n g) : ContDif
f Real n fun x => ⟪f x, g x⟫
参数：hf : ContDiff Real n f；hg : ContDiff Real n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_inner`：contDiff_inner {n} : ContDiff Real n fun p : E × E => ⟪p
.1, p.2⟫
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)
-/
theorem ContDiff.inner (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => ⟪f x, g x⟫ :=
  contDiff_inner.comp (hf.prodMk hg)
/-
**HasFDerivWithinAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.inner (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivW
ithinAt g g' s x) : HasFDerivWithinAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (
f x, g x)).comp <| f'.prod g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `isBoundedBilinearMap_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [in
st_3 : NormedSpa…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.inner (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') s
      x := by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
    |>.hasFDerivAt (f x, g x) |>.comp_hasFDerivWithinAt x (hf.prodMk hg)
/-
**HasStrictFDerivAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.inner (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDe
rivAt g g' x) : HasStrictFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x,
 g x)).comp <| f'.prod g') x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `isBoundedBilinearMap_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [in
st_3 : NormedSpa…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.inner (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x :=
  isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
    |>.hasStrictFDerivAt (f x, g x) |>.comp x (hf.prodMk hg)
/-
**HasFDerivAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) : Ha
sFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g
') x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `isBoundedBilinearMap_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [in
st_3 : NormedSpa…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x := by
  -- `by exact` to handle a tricky unification.
  exact isBoundedBilinearMap_inner (𝕜 := 𝕜) (E := E)
    |>.hasFDerivAt (f x, g x) |>.comp x (hf.prodMk hg)
/-
**HasDerivWithinAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.inner {f g : Real -> E} {f' g' : E} {s : Set Real} {x : R
eal} (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) : HasDeri
vWithinAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x
参数：hf : HasDerivWithinAt f f' s x；hg : HasDerivWithinAt g g' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.inner`：HasFDerivWithinAt.inner (hf : HasFDerivWithinAt
 f f' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun t => ⟪f t,
 g t⟫) ((fder…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.inner {f g : ℝ → E} {f' g' : E} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x := by
  simpa using (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).hasDerivWithinAt
/-
**HasDerivAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.inner {f g : Real -> E} {f' g' : E} {x : Real} : HasDerivAt f f
' x -> HasDerivAt g g' x -> HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g
 x⟫) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `HasDerivWithinAt.inner`：HasDerivWithinAt.inner {f g : Real -> E} {f' g' 
: E} {s : Set Real} {x : Real} (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWi
thinAt g g' …
-/
theorem HasDerivAt.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
    HasDerivAt f f' x → HasDerivAt g g' x →
      HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x := by
  simpa only [← hasDerivWithinAt_univ] using HasDerivWithinAt.inner 𝕜
/-
**DifferentiableWithinAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.inner (hf : DifferentiableWithinAt Real f s x) (hg 
: DifferentiableWithinAt Real g s x) : DifferentiableWithinAt Real (fun x => ⟪f 
x, g x⟫) s x
参数：hf : DifferentiableWithinAt Real f s x；hg : DifferentiableWithinAt Real g s x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.inner`：HasFDerivWithinAt.inner (hf : HasFDerivWithinAt
 f f' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun t => ⟪f t,
 g t⟫) ((fder…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.inner (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) : DifferentiableWithinAt ℝ (fun x => ⟪f x, g x⟫) s x :=
  (hf.hasFDerivWithinAt.inner 𝕜 hg.hasFDerivWithinAt).differentiableWithinAt
/-
**DifferentiableAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.inner (hf : DifferentiableAt Real f x) (hg : Differentiab
leAt Real g x) : DifferentiableAt Real (fun x => ⟪f x, g x⟫) x
参数：hf : DifferentiableAt Real f x；hg : DifferentiableAt Real g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.inner`：HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : Has
FDerivAt g g' x) : HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g 
x)).com…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.inner (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun x => ⟪f x, g x⟫) x :=
  (hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).differentiableAt
/-
**DifferentiableOn.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.inner (hf : DifferentiableOn Real f s) (hg : Differentiab
leOn Real g s) : DifferentiableOn Real (fun x => ⟪f x, g x⟫) s
参数：hf : DifferentiableOn Real f s；hg : DifferentiableOn Real g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.inner`：DifferentiableWithinAt.inner (hf : Differe
ntiableWithinAt Real f s x) (hg : DifferentiableWithinAt Real g s x) : Different
iableWithinAt Real…
-/
theorem DifferentiableOn.inner (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s) :
    DifferentiableOn ℝ (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner 𝕜 (hg x hx)
/-
**Differentiable.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.inner (hf : Differentiable Real f) (hg : Differentiable Rea
l g) : Differentiable Real fun x => ⟪f x, g x⟫
参数：hf : Differentiable Real f；hg : Differentiable Real g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.inner`：DifferentiableAt.inner (hf : DifferentiableAt Re
al f x) (hg : DifferentiableAt Real g x) : DifferentiableAt Real (fun x => ⟪f x,
 g x⟫) x
-/
theorem Differentiable.inner (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ fun x => ⟪f x, g x⟫ := fun x => (hf x).inner 𝕜 (hg x)
/-
**fderiv_inner_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_inner_apply (hf : DifferentiableAt Real f x) (hg : DifferentiableAt
 Real g x) (y : G) : fderiv Real (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv Real g
 x y⟫ + ⟪fderiv Real f x y, g x⟫
参数：hf : DifferentiableAt Real f x；hg : DifferentiableAt Real g x；y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.inner`：HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : Has
FDerivAt g g' x) : HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g 
x)).com…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_inner_apply (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (y : G) :
    fderiv ℝ (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ := by
  rw [(hf.hasFDerivAt.inner 𝕜 hg.hasFDerivAt).fderiv]; rfl
/-
**deriv_inner_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_inner_apply {f g : Real -> E} {x : Real} (hf : DifferentiableAt Real
 f x) (hg : DifferentiableAt Real g x) : deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, d
eriv g x⟫ + ⟪deriv f x, g x⟫
参数：hf : DifferentiableAt Real f x；hg : DifferentiableAt Real g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.inner`：HasDerivAt.inner {f g : Real -> E} {f' g' : E} {x : Re
al} : HasDerivAt f f' x -> HasDerivAt g g' x -> HasDerivAt (fun t => ⟪f t, g t⟫)
 (⟪f x…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
  (hf.hasDerivAt.inner 𝕜 hg.hasDerivAt).deriv

section
include 𝕜

/-
**contDiff_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_self_eq_norm_sq`：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^
 2
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `ContDiff.inner`：ContDiff.inner (hf : ContDiff Real n f) (hg : ContDiff R
eal n g) : ContDiff Real n fun x => ⟪f x, g x⟫
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiff_norm_sq : ContDiff ℝ n fun x : E => ‖x‖ ^ 2 := by
  convert! (reCLM : 𝕜 →L[ℝ] ℝ).contDiff.comp ((contDiff_id (E := E)).inner 𝕜 (contDiff_id (E := E)))
  exact (inner_self_eq_norm_sq _).symm
/-
**ContDiff.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.norm_sq (hf : ContDiff Real n f) : ContDiff Real n fun x => ‖f x‖
 ^ 2
参数：hf : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_norm_sq`：contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 
2
-/
theorem ContDiff.norm_sq (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => ‖f x‖ ^ 2 :=
  (contDiff_norm_sq 𝕜).comp hf
/-
**ContDiffWithinAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt Real n f s x) : ContDiffWi
thinAt Real n (fun y => ‖f y‖ ^ 2) s x
参数：hf : ContDiffWithinAt Real n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_norm_sq`：contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 
2
-/
theorem ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖ ^ 2) s x :=
  (contDiff_norm_sq 𝕜).contDiffAt.comp_contDiffWithinAt x hf

nonrec theorem ContDiffAt.norm_sq (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (‖f ·‖ ^ 2) x :=
  hf.norm_sq 𝕜
/-
**contDiffAt_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_norm {x : E} (hx : x != 0) : ContDiffAt Real n norm x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContDiffAt.sqrt`：ContDiffAt.sqrt (hf : ContDiffAt Real n f x) (hx : f x 
!= 0) : ContDiffAt Real n (fun y => √(f y)) x
· 使用定理 `ContDiffAt.norm_sq`：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [InnerProductSpace 𝕜 E]   [inst : NormedSpace ℝ E]
 {G : Ty…
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
-/
theorem contDiffAt_norm {x : E} (hx : x ≠ 0) : ContDiffAt ℝ n norm x := by
  have : ‖id x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using (contDiffAt_id.norm_sq 𝕜).sqrt this
/-
**ContDiffAt.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.norm (hf : ContDiffAt Real n f x) (h0 : f x != 0) : ContDiffAt 
Real n (fun y => ‖f y‖) x
参数：hf : ContDiffAt Real n f x；h0 : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_norm`：contDiffAt_norm {x : E} (hx : x != 0) : ContDiffAt Real
 n norm x
-/
theorem ContDiffAt.norm (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => ‖f y‖) x :=
  (contDiffAt_norm 𝕜 h0).comp x hf
/-
**ContDiffAt.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.dist (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) 
(hne : f x != g x) : ContDiffAt Real n (fun y => dist (f y) (g y)) x
参数：hf : ContDiffAt Real n f x；hg : ContDiffAt Real n g x；hne : f x != g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `ContDiffAt.norm`：ContDiffAt.norm (hf : ContDiffAt Real n f x) (h0 : f x 
!= 0) : ContDiffAt Real n (fun y => ‖f y‖) x
· 使用定理 `ContDiffAt.sub`：ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x - g x) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem ContDiffAt.dist (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (hne : f x ≠ g x) :
    ContDiffAt ℝ n (fun y => dist (f y) (g y)) x := by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
/-
**ContDiffWithinAt.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.norm (hf : ContDiffWithinAt Real n f s x) (h0 : f x != 0)
 : ContDiffWithinAt Real n (fun y => ‖f y‖) s x
参数：hf : ContDiffWithinAt Real n f s x；h0 : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `contDiffAt_norm`：contDiffAt_norm {x : E} (hx : x != 0) : ContDiffAt Real
 n norm x
-/
theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt ℝ n f s x) (h0 : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖) s x :=
  (contDiffAt_norm 𝕜 h0).comp_contDiffWithinAt x hf
/-
**ContDiffWithinAt.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.dist (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffW
ithinAt Real n g s x) (hne : f x != g x) : ContDiffWithinAt Real n (fun y => dis
t (f y) (g y)) s x
参数：hf : ContDiffWithinAt Real n f s x；hg : ContDiffWithinAt Real n g s x；hne : f
 x != g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `ContDiffWithinAt.norm`：ContDiffWithinAt.norm (hf : ContDiffWithinAt Real
 n f s x) (h0 : f x != 0) : ContDiffWithinAt Real n (fun y => ‖f y‖) s x
· 使用定理 `ContDiffWithinAt.sub`：ContDiffWithinAt.sub {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem ContDiffWithinAt.dist (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (hne : f x ≠ g x) : ContDiffWithinAt ℝ n (fun y => dist (f y) (g y)) s x := by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
/-
**ContDiffOn.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.norm_sq (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun y
 => ‖f y‖ ^ 2) s
参数：hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.norm_sq`：ContDiffWithinAt.norm_sq (hf : ContDiffWithinA
t Real n f s x) : ContDiffWithinAt Real n (fun y => ‖f y‖ ^ 2) s x
-/
theorem ContDiffOn.norm_sq (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun y => ‖f y‖ ^ 2) s :=
  fun x hx => (hf x hx).norm_sq 𝕜
/-
**ContDiffOn.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.norm (hf : ContDiffOn Real n f s) (h0 : forall x in s, f x != 0
) : ContDiffOn Real n (fun y => ‖f y‖) s
参数：hf : ContDiffOn Real n f s；h0 : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.norm`：ContDiffWithinAt.norm (hf : ContDiffWithinAt Real
 n f s x) (h0 : f x != 0) : ContDiffWithinAt Real n (fun y => ‖f y‖) s x
-/
theorem ContDiffOn.norm (hf : ContDiffOn ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm 𝕜 (h0 x hx)
/-
**ContDiffOn.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.dist (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s) 
(hne : forall x in s, f x != g x) : ContDiffOn Real n (fun y => dist (f y) (g y)
) s
参数：hf : ContDiffOn Real n f s；hg : ContDiffOn Real n g s；hne : forall x in s, f 
x != g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.dist`：ContDiffWithinAt.dist (hf : ContDiffWithinAt Real
 n f s x) (hg : ContDiffWithinAt Real n g s x) (hne : f x != g x) : ContDiffWith
inAt Real n…
-/
theorem ContDiffOn.dist (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : ContDiffOn ℝ n (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)
/-
**ContDiff.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.norm (hf : ContDiff Real n f) (h0 : forall x, f x != 0) : ContDif
f Real n fun y => ‖f y‖
参数：hf : ContDiff Real n f；h0 : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.norm`：ContDiffAt.norm (hf : ContDiffAt Real n f x) (h0 : f x 
!= 0) : ContDiffAt Real n (fun y => ‖f y‖) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.norm (hf : ContDiff ℝ n f) (h0 : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => ‖f y‖ :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.norm 𝕜 (h0 x)
/-
**ContDiff.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.dist (hf : ContDiff Real n f) (hg : ContDiff Real n g) (hne : for
all x, f x != g x) : ContDiff Real n fun y => dist (f y) (g y)
参数：hf : ContDiff Real n f；hg : ContDiff Real n g；hne : forall x, f x != g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.dist`：ContDiffAt.dist (hf : ContDiffAt Real n f x) (hg : Cont
DiffAt Real n g x) (hne : f x != g x) : ContDiffAt Real n (fun y => dist (f y) (
g y))…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hne : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun y => dist (f y) (g y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.dist 𝕜 hg.contDiffAt (hne x)

end

section
open scoped RealInnerProductSpace

/-
**hasStrictFDerivAt_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_norm_sq (x : F) : HasStrictFDerivAt (fun x => ‖x‖ ^ 2) (
2 • (innerSL Real x)) x
参数：x : F。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_norm_mul_norm`：inner_self_eq_norm_mul_norm (x : E) : re ⟪x
, x⟫ = ‖x‖ * ‖x‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.inner`：HasStrictFDerivAt.inner (hf : HasStrictFDerivAt
 f f' x) (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (fun t => ⟪f t, g t
⟫) ((fderivIn…
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
-/
theorem hasStrictFDerivAt_norm_sq (x : F) :
    HasStrictFDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL ℝ x)) x := by
  simp only [sq, ← @inner_self_eq_norm_mul_norm ℝ]
  convert! (hasStrictFDerivAt_id x).inner ℝ (hasStrictFDerivAt_id x)
  ext y
  simp [two_smul, real_inner_comm]

@[simp]
/-
**fderiv_norm_sq_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_norm_sq_apply (x : F) : fderiv Real (fun (x : F) => ‖x‖ ^ 2) x = 2 
• innerSL Real x
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `hasStrictFDerivAt_norm_sq`：hasStrictFDerivAt_norm_sq (x : F) : HasStrict
FDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL Real x)) x
-/
theorem fderiv_norm_sq_apply (x : F) : fderiv ℝ (fun (x : F) ↦ ‖x‖ ^ 2) x = 2 • innerSL ℝ x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv
/-
**fderiv_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_norm_sq : fderiv Real (fun (x : F) => ‖x‖ ^ 2) = 2 • (innerSL Real 
(E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_norm_sq_apply`：fderiv_norm_sq_apply (x : F) : fderiv Real (fun (x
 : F) => ‖x‖ ^ 2) x = 2 • innerSL Real x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_norm_sq : fderiv ℝ (fun (x : F) ↦ ‖x‖ ^ 2) = 2 • (innerSL ℝ (E := F)) := by
  ext1; simp
/-
**HasFDerivAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.norm_sq {f : G -> F} {f' : G ->L[Real] F} (hf : HasFDerivAt f 
f' x) : HasFDerivAt (‖f ·‖ ^ 2) (2 • (innerSL Real (f x)).comp f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `hasStrictFDerivAt_norm_sq`：hasStrictFDerivAt_norm_sq (x : F) : HasStrict
FDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL Real x)) x
-/
theorem HasFDerivAt.norm_sq {f : G → F} {f' : G →L[ℝ] F} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (‖f ·‖ ^ 2) (2 • (innerSL ℝ (f x)).comp f') x :=
  (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp x hf
/-
**HasDerivAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.norm_sq {f : Real -> F} {f' : F} {x : Real} (hf : HasDerivAt f 
f' x) : HasDerivAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫) x
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
· 使用定理 `ContinuousLinearMap.instIsMulApplyEqCompId`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.norm_sq`：HasFDerivAt.norm_sq {f : G -> F} {f' : G ->L[Real] 
F} (hf : HasFDerivAt f f' x) : HasFDerivAt (‖f ·‖ ^ 2) (2 • (innerSL Real (f x))
.comp f')…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.norm_sq {f : ℝ → F} {f' : F} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫) x := by
  simpa using hf.hasFDerivAt.norm_sq.hasDerivAt
/-
**HasFDerivWithinAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.norm_sq {f : G -> F} {f' : G ->L[Real] F} (hf : HasFDeri
vWithinAt f f' s x) : HasFDerivWithinAt (‖f ·‖ ^ 2) (2 • (innerSL Real (f x)).co
mp f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `hasStrictFDerivAt_norm_sq`：hasStrictFDerivAt_norm_sq (x : F) : HasStrict
FDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL Real x)) x
-/
theorem HasFDerivWithinAt.norm_sq {f : G → F} {f' : G →L[ℝ] F} (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (‖f ·‖ ^ 2) (2 • (innerSL ℝ (f x)).comp f') s x :=
  (hasStrictFDerivAt_norm_sq _).hasFDerivAt.comp_hasFDerivWithinAt x hf
/-
**HasDerivWithinAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.norm_sq {f : Real -> F} {f' : F} {s : Set Real} {x : Real
} (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫
) s x
参数：hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
· 使用定理 `ContinuousLinearMap.instIsMulApplyEqCompId`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.norm_sq`：HasFDerivWithinAt.norm_sq {f : G -> F} {f' : 
G ->L[Real] F} (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (‖f ·‖ ^ 2)
 (2 • (innerSL …
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.norm_sq {f : ℝ → F} {f' : F} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫) s x := by
  simpa using hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt

end

section
include 𝕜

/-
**DifferentiableAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.norm_sq (hf : DifferentiableAt Real f x) : Differentiable
At Real (fun y => ‖f y‖ ^ 2) x
参数：hf : DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiffAt.norm_sq`：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [InnerProductSpace 𝕜 E]   [inst : NormedSpace ℝ E]
 {G : Ty…
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem DifferentiableAt.norm_sq (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => ‖f y‖ ^ 2) x :=
  ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp x hf
/-
**DifferentiableAt.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.norm (hf : DifferentiableAt Real f x) (h0 : f x != 0) : D
ifferentiableAt Real (fun y => ‖f y‖) x
参数：hf : DifferentiableAt Real f x；h0 : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `contDiffAt_norm`：contDiffAt_norm {x : E} (hx : x != 0) : ContDiffAt Real
 n norm x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem DifferentiableAt.norm (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => ‖f y‖) x :=
  ((contDiffAt_norm 𝕜 h0).differentiableAt one_ne_zero).comp x hf
/-
**DifferentiableAt.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.dist (hf : DifferentiableAt Real f x) (hg : Differentiabl
eAt Real g x) (hne : f x != g x) : DifferentiableAt Real (fun y => dist (f y) (g
 y)) x
参数：hf : DifferentiableAt Real f x；hg : DifferentiableAt Real g x；hne : f x != g 
x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `DifferentiableAt.norm`：DifferentiableAt.norm (hf : DifferentiableAt Real
 f x) (h0 : f x != 0) : DifferentiableAt Real (fun y => ‖f y‖) x
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem DifferentiableAt.dist (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hne : f x ≠ g x) : DifferentiableAt ℝ (fun y => dist (f y) (g y)) x := by
  simp only [dist_eq_norm]; exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
/-
**Differentiable.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.norm_sq (hf : Differentiable Real f) : Differentiable Real 
fun y => ‖f y‖ ^ 2
参数：hf : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.norm_sq`：DifferentiableAt.norm_sq (hf : DifferentiableA
t Real f x) : DifferentiableAt Real (fun y => ‖f y‖ ^ 2) x
-/
theorem Differentiable.norm_sq (hf : Differentiable ℝ f) : Differentiable ℝ fun y => ‖f y‖ ^ 2 :=
  fun x => (hf x).norm_sq 𝕜
/-
**Differentiable.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.norm (hf : Differentiable Real f) (h0 : forall x, f x != 0)
 : Differentiable Real fun y => ‖f y‖
参数：hf : Differentiable Real f；h0 : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.norm`：DifferentiableAt.norm (hf : DifferentiableAt Real
 f x) (h0 : f x != 0) : DifferentiableAt Real (fun y => ‖f y‖) x
-/
theorem Differentiable.norm (hf : Differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => ‖f y‖ := fun x => (hf x).norm 𝕜 (h0 x)
/-
**Differentiable.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.dist (hf : Differentiable Real f) (hg : Differentiable Real
 g) (hne : forall x, f x != g x) : Differentiable Real fun y => dist (f y) (g y)
参数：hf : Differentiable Real f；hg : Differentiable Real g；hne : forall x, f x != 
g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.dist`：DifferentiableAt.dist (hf : DifferentiableAt Real
 f x) (hg : DifferentiableAt Real g x) (hne : f x != g x) : DifferentiableAt Rea
l (fun y =>…
-/
theorem Differentiable.dist (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hne : ∀ x, f x ≠ g x) : Differentiable ℝ fun y => dist (f y) (g y) := fun x =>
  (hf x).dist 𝕜 (hg x) (hne x)
/-
**DifferentiableWithinAt.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt Real f s x) : 
DifferentiableWithinAt Real (fun y => ‖f y‖ ^ 2) s x
参数：hf : DifferentiableWithinAt Real f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiffAt.norm_sq`：∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [InnerProductSpace 𝕜 E]   [inst : NormedSpace ℝ E]
 {G : Ty…
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖ ^ 2) s x :=
  ((contDiffAt_id.norm_sq 𝕜).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf
/-
**DifferentiableWithinAt.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.norm (hf : DifferentiableWithinAt Real f s x) (h0 :
 f x != 0) : DifferentiableWithinAt Real (fun y => ‖f y‖) s x
参数：hf : DifferentiableWithinAt Real f s x；h0 : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiffAt.norm`：ContDiffAt.norm (hf : ContDiffAt Real n f x) (h0 : f x 
!= 0) : ContDiffAt Real n (fun y => ‖f y‖) x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt ℝ f s x) (h0 : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖) s x :=
  ((contDiffAt_id.norm 𝕜 h0).differentiableAt one_ne_zero).comp_differentiableWithinAt x hf
/-
**DifferentiableWithinAt.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.dist (hf : DifferentiableWithinAt Real f s x) (hg :
 DifferentiableWithinAt Real g s x) (hne : f x != g x) : DifferentiableWithinAt 
Real (fun y => dist (f y) (g y)) s x
参数：hf : DifferentiableWithinAt Real f s x；hg : DifferentiableWithinAt Real g s x
；hne : f x != g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `DifferentiableWithinAt.norm`：DifferentiableWithinAt.norm (hf : Different
iableWithinAt Real f s x) (h0 : f x != 0) : DifferentiableWithinAt Real (fun y =
> ‖f y‖) s x
· 使用定理 `DifferentiableWithinAt.sub`：DifferentiableWithinAt.sub (hf : Differentia
bleWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithi
nAt 𝕜 (f - g) s …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (hne : f x ≠ g x) :
    DifferentiableWithinAt ℝ (fun y => dist (f y) (g y)) s x := by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne)
/-
**DifferentiableOn.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.norm_sq (hf : DifferentiableOn Real f s) : Differentiable
On Real (fun y => ‖f y‖ ^ 2) s
参数：hf : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.norm_sq`：DifferentiableWithinAt.norm_sq (hf : Dif
ferentiableWithinAt Real f s x) : DifferentiableWithinAt Real (fun y => ‖f y‖ ^ 
2) s x
-/
theorem DifferentiableOn.norm_sq (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun y => ‖f y‖ ^ 2) s := fun x hx => (hf x hx).norm_sq 𝕜
/-
**DifferentiableOn.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.norm (hf : DifferentiableOn Real f s) (h0 : forall x in s
, f x != 0) : DifferentiableOn Real (fun y => ‖f y‖) s
参数：hf : DifferentiableOn Real f s；h0 : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.norm`：DifferentiableWithinAt.norm (hf : Different
iableWithinAt Real f s x) (h0 : f x != 0) : DifferentiableWithinAt Real (fun y =
> ‖f y‖) s x
-/
theorem DifferentiableOn.norm (hf : DifferentiableOn ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm 𝕜 (h0 x hx)
/-
**DifferentiableOn.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.dist (hf : DifferentiableOn Real f s) (hg : Differentiabl
eOn Real g s) (hne : forall x in s, f x != g x) : DifferentiableOn Real (fun y =
> dist (f y) (g y)) s
参数：hf : DifferentiableOn Real f s；hg : DifferentiableOn Real g s；hne : forall x 
in s, f x != g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.dist`：DifferentiableWithinAt.dist (hf : Different
iableWithinAt Real f s x) (hg : DifferentiableWithinAt Real g s x) (hne : f x !=
 g x) : Different…
-/
theorem DifferentiableOn.dist (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : DifferentiableOn ℝ (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

end

end DerivInner

section PiLike

/-! ### Convenience aliases of `PiLp` lemmas for `EuclideanSpace` -/

open ContinuousLinearMap

variable {𝕜 ι H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {f : H → EuclideanSpace 𝕜 ι} {f' : H →L[𝕜] EuclideanSpace 𝕜 ι} {t : Set H} {y : H}

section finite

variable [Finite ι]

/-
**differentiableWithinAt_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_euclidean : DifferentiableWithinAt 𝕜 f t y ↔ forall
 i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_piLp`：differentiableWithinAt_piLp : Differentiabl
eWithinAt 𝕜 f t y ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem differentiableWithinAt_euclidean :
    DifferentiableWithinAt 𝕜 f t y ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y :=
  differentiableWithinAt_piLp _
/-
**differentiableAt_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_euclidean : DifferentiableAt 𝕜 f y ↔ forall i, Differenti
ableAt 𝕜 (fun x => f x i) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_piLp`：differentiableAt_piLp : DifferentiableAt 𝕜 f y ↔ 
forall i, DifferentiableAt 𝕜 (fun x => f x i) y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem differentiableAt_euclidean :
    DifferentiableAt 𝕜 f y ↔ ∀ i, DifferentiableAt 𝕜 (fun x => f x i) y :=
  differentiableAt_piLp _
/-
**differentiableOn_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_euclidean : DifferentiableOn 𝕜 f t ↔ forall i, Differenti
ableOn 𝕜 (fun x => f x i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_piLp`：differentiableOn_piLp : DifferentiableOn 𝕜 f t ↔ 
forall i, DifferentiableOn 𝕜 (fun x => f x i) t
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem differentiableOn_euclidean :
    DifferentiableOn 𝕜 f t ↔ ∀ i, DifferentiableOn 𝕜 (fun x => f x i) t :=
  differentiableOn_piLp _
/-
**differentiable_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_euclidean : Differentiable 𝕜 f ↔ forall i, Differentiable 𝕜
 fun x => f x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_piLp`：differentiable_piLp : Differentiable 𝕜 f ↔ forall i
, Differentiable 𝕜 fun x => f x i
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem differentiable_euclidean : Differentiable 𝕜 f ↔ ∀ i, Differentiable 𝕜 fun x => f x i :=
  differentiable_piLp _
/-
**hasStrictFDerivAt_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_euclidean : HasStrictFDerivAt f f' y ↔ forall i, HasStri
ctFDerivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_piLp`：hasStrictFDerivAt_piLp : HasStrictFDerivAt f f' 
y ↔ forall i, HasStrictFDerivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem hasStrictFDerivAt_euclidean :
    HasStrictFDerivAt f f' y ↔
      ∀ i, HasStrictFDerivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y :=
  hasStrictFDerivAt_piLp _
/-
**hasFDerivWithinAt_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_euclidean : HasFDerivWithinAt f f' t y ↔ forall i, HasFD
erivWithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_piLp`：hasFDerivWithinAt_piLp : HasFDerivWithinAt f f' 
t y ↔ forall i, HasFDerivWithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem hasFDerivWithinAt_euclidean :
    HasFDerivWithinAt f f' t y ↔
      ∀ i, HasFDerivWithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y :=
  hasFDerivWithinAt_piLp _

end finite

section fintype

variable [Fintype ι]

/-
**contDiffWithinAt_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_euclidean {n : WithTop Nat∞} : ContDiffWithinAt 𝕜 n f t y
 ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_piLp`：contDiffWithinAt_piLp : ContDiffWithinAt 𝕜 n f t 
y ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem contDiffWithinAt_euclidean {n : WithTop ℕ∞} :
    ContDiffWithinAt 𝕜 n f t y ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y :=
  contDiffWithinAt_piLp _
/-
**contDiffAt_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_euclidean {n : WithTop Nat∞} : ContDiffAt 𝕜 n f y ↔ forall i, C
ontDiffAt 𝕜 n (fun x => f x i) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffAt_piLp`：contDiffAt_piLp : ContDiffAt 𝕜 n f y ↔ forall i, ContDi
ffAt 𝕜 n (fun x => f x i) y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem contDiffAt_euclidean {n : WithTop ℕ∞} :
    ContDiffAt 𝕜 n f y ↔ ∀ i, ContDiffAt 𝕜 n (fun x => f x i) y :=
  contDiffAt_piLp _
/-
**contDiffOn_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_euclidean {n : WithTop Nat∞} : ContDiffOn 𝕜 n f t ↔ forall i, C
ontDiffOn 𝕜 n (fun x => f x i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffOn_piLp`：contDiffOn_piLp : ContDiffOn 𝕜 n f t ↔ forall i, ContDi
ffOn 𝕜 n (fun x => f x i) t
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem contDiffOn_euclidean {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n f t ↔ ∀ i, ContDiffOn 𝕜 n (fun x => f x i) t :=
  contDiffOn_piLp _
/-
**contDiff_euclidean** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_euclidean {n : WithTop Nat∞} : ContDiff 𝕜 n f ↔ forall i, ContDif
f 𝕜 n fun x => f x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiff_piLp`：contDiff_piLp : ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n f
un x => f x i
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem contDiff_euclidean {n : WithTop ℕ∞} : ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n fun x => f x i :=
  contDiff_piLp _

end fintype

end PiLike

section DiffeomorphUnitBall

open Metric hiding mem_nhds_iff

variable {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
**OpenPartialHomeomorph.contDiff_univUnitBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.contDiff_univUnitBall : ContDiff Real n (univUnitBal
l : E -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `ContDiff.inv`：ContDiff.inv {f : E -> 𝕜'} (hf : ContDiff 𝕜 n f) (h : fora
ll x, f x != 0) : ContDiff 𝕜 n f⁻¹
· 使用定理 `ContDiff.sqrt`：ContDiff.sqrt (hf : ContDiff Real n f) (h : forall x, f x
 != 0) : ContDiff Real n fun y => √(f y)
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_norm_sq`：contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 
2
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_ne_zero'`：sqrt_ne_zero' : √x != 0 ↔ 0 < x
· 使用定理 `ContDiff.smul`：ContDiff.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDiff 𝕜
 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f • g)
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem OpenPartialHomeomorph.contDiff_univUnitBall : ContDiff ℝ n (univUnitBall : E → E) := by
  suffices ContDiff ℝ n fun x : E => (√(1 + ‖x‖ ^ 2 : ℝ))⁻¹ from this.smul contDiff_id
  have h : ∀ x : E, (0 : ℝ) < (1 : ℝ) + ‖x‖ ^ 2 := fun x => by positivity
  refine ContDiff.inv ?_ fun x => Real.sqrt_ne_zero'.mpr (h x)
  exact (contDiff_const.add <| contDiff_norm_sq ℝ).sqrt fun x => (h x).ne'
/-
**OpenPartialHomeomorph.contDiffOn_univUnitBall_symm** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：OpenPartialHomeomorph.contDiffOn_univUnitBall_symm : ContDiffOn Real n uni
vUnitBall.symm (ball (0 : E) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `ContDiffAt.inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {
n : …
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Real.contDiffAt_sqrt`：contDiffAt_sqrt {x : Real} {n : WithTop Nat∞} (hx 
: x != 0) : ContDiffAt Real n (√·) x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ContDiffAt.sub`：ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x - g x) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_norm_sq`：contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 
2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_ne_zero'`：sqrt_ne_zero' : √x != 0 ↔ 0 < x
· 使用定理 `ContDiffAt.smul`：ContDiffAt.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDi
ffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (f • g) x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
-/
theorem OpenPartialHomeomorph.contDiffOn_univUnitBall_symm :
    ContDiffOn ℝ n univUnitBall.symm (ball (0 : E) 1) := fun y hy ↦ by
  apply ContDiffAt.contDiffWithinAt
  suffices ContDiffAt ℝ n (fun y : E => (√(1 - ‖y‖ ^ 2 : ℝ))⁻¹) y from this.smul contDiffAt_id
  have h : (0 : ℝ) < (1 : ℝ) - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm, ← sq_lt_sq, one_pow, ← sub_pos] at hy
  refine ContDiffAt.inv ?_ (Real.sqrt_ne_zero'.mpr h)
  change ContDiffAt ℝ n ((fun y ↦ √(y)) ∘ fun y ↦ (1 - ‖y‖ ^ 2)) y
  refine (contDiffAt_sqrt h.ne').comp y ?_
  exact contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
/-
**Homeomorph.contDiff_unitBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.contDiff_unitBall : ContDiff Real n fun x : E => (unitBall x : 
E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.contDiff_univUnitBall`：OpenPartialHomeomorph.contD
iff_univUnitBall : ContDiff Real n (univUnitBall : E -> E)
-/
theorem Homeomorph.contDiff_unitBall : ContDiff ℝ n fun x : E => (unitBall x : E) :=
  OpenPartialHomeomorph.contDiff_univUnitBall

namespace OpenPartialHomeomorph

variable {c : E} {r : ℝ}

/-
**OpenPartialHomeomorph.contDiff_unitBallBall** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：contDiff_unitBallBall (hr : 0 < r) : ContDiff Real n (unitBallBall c r hr)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.const_smul`：ContDiff.const_smul {f : E -> F} (c : R) (hf : Cont
Diff 𝕜 n f) : ContDiff 𝕜 n fun y => c • f y
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiff_unitBallBall (hr : 0 < r) : ContDiff ℝ n (unitBallBall c r hr) :=
  (contDiff_id.const_smul r).add contDiff_const
/-
**OpenPartialHomeomorph.contDiff_unitBallBall_symm** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：contDiff_unitBallBall_symm (hr : 0 < r) : ContDiff Real n (unitBallBall c 
r hr).symm
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.const_smul`：ContDiff.const_smul {f : E -> F} (c : R) (hf : Cont
Diff 𝕜 n f) : ContDiff 𝕜 n fun y => c • f y
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiff.sub`：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiff_unitBallBall_symm (hr : 0 < r) : ContDiff ℝ n (unitBallBall c r hr).symm :=
  (contDiff_id.sub contDiff_const).const_smul r⁻¹
/-
**OpenPartialHomeomorph.contDiff_univBall** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：contDiff_univBall : ContDiff Real n (univBall c r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `OpenPartialHomeomorph.contDiff_unitBallBall`：contDiff_unitBallBall (hr :
 0 < r) : ContDiff Real n (unitBallBall c r hr)
· 使用定理 `OpenPartialHomeomorph.contDiff_univUnitBall`：OpenPartialHomeomorph.contD
iff_univUnitBall : ContDiff Real n (univUnitBall : E -> E)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiff_univBall : ContDiff ℝ n (univBall c r) := by
  unfold univBall; split_ifs with h
  · exact (contDiff_unitBallBall h).comp contDiff_univUnitBall
  · exact contDiff_id.add contDiff_const
/-
**OpenPartialHomeomorph.contDiffOn_univBall_symm** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：contDiffOn_univBall_symm : ContDiffOn Real n (univBall c r).symm (ball c r
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `OpenPartialHomeomorph.contDiffOn_univUnitBall_symm`：OpenPartialHomeomorp
h.contDiffOn_univUnitBall_symm : ContDiffOn Real n univUnitBall.symm (ball (0 : 
E) 1)
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `OpenPartialHomeomorph.contDiff_unitBallBall_symm`：contDiff_unitBallBall_
symm (hr : 0 < r) : ContDiff Real n (unitBallBall c r hr).symm
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.unitBallBall_source`：∀ {E : Type u_1} [inst : Semi
normedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {P : Type u_2}   [inst_2 : Pseu
doMetricSpace P] [inst_3 : Norm…
· 使用定理 `OpenPartialHomeomorph.unitBallBall_target`：∀ {E : Type u_1} [inst : Semi
normedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {P : Type u_2}   [inst_2 : Pseu
doMetricSpace P] [inst_3 : Norm…
· 使用定理 `OpenPartialHomeomorph.mapsTo_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y), Set.MapsTo (↑e.…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `ContDiffOn.sub`：ContDiffOn.sub {s : Set E} {f g : E -> F} (hf : ContDiff
On 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `contDiffOn_const`：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n 
(fun _ : E => c) s
-/
theorem contDiffOn_univBall_symm :
    ContDiffOn ℝ n (univBall c r).symm (ball c r) := by
  unfold univBall; split_ifs with h
  · refine contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm h).contDiffOn ?_
    rw [← unitBallBall_source c r h, ← unitBallBall_target c r h]
    apply OpenPartialHomeomorph.mapsTo_symm
  · exact contDiffOn_id.sub contDiffOn_const

end OpenPartialHomeomorph

end DiffeomorphUnitBall

