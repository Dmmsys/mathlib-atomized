/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Operator.Conformal

/-!
# Conformal Maps

A continuous linear map between real normed spaces `X` and `Y` is `ConformalAt` some point `x`
if it is real differentiable at that point and its differential is a conformal linear map.

## Main definitions

* `ConformalAt`: the main definition of conformal maps
* `Conformal`: maps that are conformal at every point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformalAt_iff_isConformalMap_fderiv`: an equivalent definition of the conformality of a map

In `Analysis.Calculus.Conformal.InnerProduct`:
* `conformalAt_iff`: an equivalent definition of the conformality of a map

In `Geometry.Euclidean.Angle.Unoriented.Conformal`:
* `ConformalAt.preserves_angle`: if a map is conformal at `x`, then its differential preserves
  all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/

@[expose] public section


noncomputable section

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]

section LocConformality

open LinearIsometry ContinuousLinearMap

/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
/-
**ConformalAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConformalAt (f : X -> Y) (x : X)
参数：f : X -> Y；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` is said to be conformal if it has a conformal differential `f'`.
-/
def ConformalAt (f : X → Y) (x : X) :=
  ∃ f' : X →L[ℝ] Y, HasFDerivAt f f' x ∧ IsConformalMap f'
/-
**conformalAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalAt_id (x : X) : ConformalAt _root_.id x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `isConformalMap_id`：isConformalMap_id : IsConformalMap (.id R M)
-/
theorem conformalAt_id (x : X) : ConformalAt _root_.id x :=
  ⟨.id ℝ X, hasFDerivAt_id _, isConformalMap_id⟩
/-
**conformalAt_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalAt_const_smul {c : Real} (h : c != 0) (x : X) : ConformalAt (fun 
x' : X => c • x') x
参数：h : c != 0；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.const_smul`：HasFDerivAt.const_smul (h : HasFDerivAt f f' x) 
(c : R) : HasFDerivAt (c • f) (c • f') x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `isConformalMap_const_smul`：isConformalMap_const_smul (hc : c != 0) : IsC
onformalMap (c • .id R M)
-/
theorem conformalAt_const_smul {c : ℝ} (h : c ≠ 0) (x : X) : ConformalAt (fun x' : X => c • x') x :=
  ⟨c • ContinuousLinearMap.id ℝ X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩

@[nontriviality]
/-
**Subsingleton.conformalAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.conformalAt [Subsingleton X] (f : X -> Y) (x : X) : Conformal
At f x
参数：f : X -> Y；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_of_subsingleton`：hasFDerivAt_of_subsingleton [h : Subsinglet
on E] (f : E -> F) (x : E) : HasFDerivAt f (0 : E ->L[𝕜] F) x
· 使用定理 `isConformalMap_of_subsingleton`：isConformalMap_of_subsingleton [Subsingl
eton M] (f' : M ->L[R] N) : IsConformalMap f'
-/
theorem Subsingleton.conformalAt [Subsingleton X] (f : X → Y) (x : X) : ConformalAt f x :=
  ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩

/-- A function is a conformal map if and only if its differential is a conformal linear map -/
/-
**conformalAt_iff_isConformalMap_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalAt_iff_isConformalMap_fderiv {f : X -> Y} {x : X} : ConformalAt f
 x ↔ IsConformalMap (fderiv Real f x)
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `IsConformalMap.ne_zero`：ne_zero [Nontrivial M'] {f' : M' ->L[R] N} (hf' 
: IsConformalMap f') : f' != 0

--- 原说明 ---
A function is a conformal map if and only if its differential is a conformal lin
ear map
-/
theorem conformalAt_iff_isConformalMap_fderiv {f : X → Y} {x : X} :
    ConformalAt f x ↔ IsConformalMap (fderiv ℝ f x) := by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt ℝ f x
    · exact ⟨fderiv ℝ f x, h.hasFDerivAt, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero

namespace ConformalAt

/-
**ConformalAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ConformalAt`。
形式化陈述：differentiableAt {f : X -> Y} {x : X} (h : ConformalAt f x) : Differentiab
leAt Real f x
参数：h : ConformalAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
-/
theorem differentiableAt {f : X → Y} {x : X} (h : ConformalAt f x) : DifferentiableAt ℝ f x :=
  let ⟨_, h₁, _⟩ := h
  h₁.differentiableAt
/-
**ConformalAt.congr** 是 Mathlib 中的一个定理，位于命名空间 `ConformalAt`。
形式化陈述：congr {f g : X -> Y} {x : X} {u : Set X} (hx : x in u) (hu : IsOpen u) (hf
 : ConformalAt f x) (h : forall x : X, x in u -> g x = f x) : ConformalAt g x
参数：hx : x in u；hu : IsOpen u；hf : ConformalAt f x；h : forall x : X, x in u -> g 
x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.congr_of_eventuallyEq`：HasFDerivAt.congr_of_eventuallyEq (h 
: HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasFDerivAt f₁ f' x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
-/
theorem congr {f g : X → Y} {x : X} {u : Set X} (hx : x ∈ u) (hu : IsOpen u) (hf : ConformalAt f x)
    (h : ∀ x : X, x ∈ u → g x = f x) : ConformalAt g x :=
  let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩
/-
**ConformalAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ConformalAt`。
形式化陈述：comp {f : X -> Y} {g : Y -> Z} (x : X) (hg : ConformalAt g (f x)) (hf : Co
nformalAt f x) : ConformalAt (g ∘ f) x
参数：x : X；hg : ConformalAt g (f x)；hf : ConformalAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `IsConformalMap.comp`：comp (hg : IsConformalMap g) (hf : IsConformalMap f
) : IsConformalMap (g.comp f)
-/
theorem comp {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
    ConformalAt (g ∘ f) x := by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩
/-
**ConformalAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `ConformalAt`。
形式化陈述：const_smul {f : X -> Y} {x : X} {c : Real} (hc : c != 0) (hf : ConformalAt
 f x) : ConformalAt (c • f) x
参数：hc : c != 0；hf : ConformalAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConformalAt.comp`：comp {f : X -> Y} {g : Y -> Z} (x : X) (hg : Conformal
At g (f x)) (hf : ConformalAt f x) : ConformalAt (g ∘ f) x
· 使用定理 `conformalAt_const_smul`：conformalAt_const_smul {c : Real} (h : c != 0) (
x : X) : ConformalAt (fun x' : X => c • x') x
-/
theorem const_smul {f : X → Y} {x : X} {c : ℝ} (hc : c ≠ 0) (hf : ConformalAt f x) :
    ConformalAt (c • f) x :=
  (conformalAt_const_smul hc <| f x).comp x hf

end ConformalAt

end LocConformality

section GlobalConformality

/-- A map `f` is conformal if it's conformal at every point. -/
/-
**Conformal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Conformal (f : X -> Y)
参数：f : X -> Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` is conformal if it's conformal at every point.
-/
def Conformal (f : X → Y) :=
  ∀ x : X, ConformalAt f x
/-
**conformal_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformal_id : Conformal (id : X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `conformalAt_id`：conformalAt_id (x : X) : ConformalAt _root_.id x
-/
theorem conformal_id : Conformal (id : X → X) := fun x => conformalAt_id x
/-
**conformal_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformal_const_smul {c : Real} (h : c != 0) : Conformal fun x : X => c • 
x
参数：h : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `conformalAt_const_smul`：conformalAt_const_smul {c : Real} (h : c != 0) (
x : X) : ConformalAt (fun x' : X => c • x') x
-/
theorem conformal_const_smul {c : ℝ} (h : c ≠ 0) : Conformal fun x : X => c • x := fun x =>
  conformalAt_const_smul h x

namespace Conformal

/-
**Conformal.conformalAt** 是 Mathlib 中的一个定理，位于命名空间 `Conformal`。
形式化陈述：conformalAt {f : X -> Y} (h : Conformal f) (x : X) : ConformalAt f x
参数：h : Conformal f；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conformalAt {f : X → Y} (h : Conformal f) (x : X) : ConformalAt f x :=
  h x
/-
**Conformal.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `Conformal`。
形式化陈述：differentiable {f : X -> Y} (h : Conformal f) : Differentiable Real f
参数：h : Conformal f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConformalAt.differentiableAt`：differentiableAt {f : X -> Y} {x : X} (h :
 ConformalAt f x) : DifferentiableAt Real f x
-/
theorem differentiable {f : X → Y} (h : Conformal f) : Differentiable ℝ f := fun x =>
  (h x).differentiableAt
/-
**Conformal.comp** 是 Mathlib 中的一个定理，位于命名空间 `Conformal`。
形式化陈述：comp {f : X -> Y} {g : Y -> Z} (hf : Conformal f) (hg : Conformal g) : Con
formal (g ∘ f)
参数：hf : Conformal f；hg : Conformal g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConformalAt.comp`：comp {f : X -> Y} {g : Y -> Z} (x : X) (hg : Conformal
At g (f x)) (hf : ConformalAt f x) : ConformalAt (g ∘ f) x
-/
theorem comp {f : X → Y} {g : Y → Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
  fun x => (hg <| f x).comp x (hf x)
/-
**Conformal.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Conformal`。
形式化陈述：const_smul {f : X -> Y} (hf : Conformal f) {c : Real} (hc : c != 0) : Conf
ormal (c • f)
参数：hf : Conformal f；hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConformalAt.const_smul`：const_smul {f : X -> Y} {x : X} {c : Real} (hc :
 c != 0) (hf : ConformalAt f x) : ConformalAt (c • f) x
-/
theorem const_smul {f : X → Y} (hf : Conformal f) {c : ℝ} (hc : c ≠ 0) : Conformal (c • f) :=
  fun x => (hf x).const_smul hc

end Conformal

end GlobalConformality

