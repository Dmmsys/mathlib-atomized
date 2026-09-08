/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Implicit function theorem

In this file, we apply the generalised implicit function theorem to the more familiar case and show
that the implicit function preserves the smoothness class of the implicit equation.

Let `E₁`, `E₂`, and `F` be real or complex Banach spaces. Let `f : E₁ × E₂ → F` be a function that
is $C^n$ at a point `(u₁, u₂) : E₁ × E₂`, where `n ≥ 1`. Let `f'` be the derivative of `f` at
`(u₁, u₂)`. If the map `y ↦ f' (0, y)` is a Banach space isomorphism, then there exists a function
`ψ : E₁ → E₂` such that `ψ u₁ = u₂`, and `f (x, ψ x) = f (u₁, u₂)` holds for all `x` in a
neighbourhood of `u₁`. Furthermore, `ψ` is $C^n$ at `u₁`.

## Tags

implicit function, inverse function
-/

public section

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

open scoped Topology ContDiff

namespace ImplicitFunctionData

/-- The implicit function defined by a $C^n$ implicit equation is $C^n$. This applies to the general
form of the implicit function theorem. -/
/-
**ImplicitFunctionData.contDiffAt_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `Im
plicitFunctionData`。
形式化陈述：contDiffAt_implicitFunction {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : Nat∞
ω} (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt) (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (p
n : n != 0) : ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt)
参数：hl : ContDiffAt 𝕜 n φ.leftFun φ.pt；hr : ContDiffAt 𝕜 n φ.rightFun φ.pt；pn : n
 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ImplicitFunctionData.implicitFunction_def`：implicitFunction_def : implic
itFunction φ = Function.curry (φ.hasStrictFDerivAt.toOpenPartialHomeomorph _).sy
mm
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasStrictFDerivAt.localInverse_def`：localInverse_def (hf : HasStrictFDer
ivAt f (f' : E ->L[𝕜] F) a) : hf.localInverse f _ _ = (hf.toOpenPartialHomeomorp
h f).symm
· 使用定理 `ContDiffAt.to_localInverse`：to_localInverse (hf : ContDiffAt 𝕂 n f a) (h
f' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) : ContDiffAt 𝕂 n (hf.local
Inverse hf' hn) …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ImplicitFunctionData.prodFun_apply`：prodFun_apply (x : E) : φ.prodFun x 
= (φ.leftFun x, φ.rightFun x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…

--- 原说明 ---
The implicit function defined by a $C^n$ implicit equation is $C^n$. This applie
s to the general
form of the implicit function theorem.
-/
theorem contDiffAt_implicitFunction {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : ℕ∞ω}
    (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt) (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (pn : n ≠ 0) :
    ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction_def, Function.uncurry_curry, ← HasStrictFDerivAt.localInverse_def]
  refine ContDiffAt.to_localInverse ?_ (φ.hasStrictFDerivAt.hasFDerivAt) pn
  convert! hl.prodMk hr <;> simp

end ImplicitFunctionData

namespace ContDiffAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {n : ℕ∞ω}

/-- Implicit function `ψ` defined by `f (x, ψ x) = f u`. -/
/-
**ContDiffAt.implicitFunction** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffAt`。
形式化陈述：implicitFunction (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜
 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : E₁ -> E₂
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implicit function `ψ` defined by `f (x, ψ x) = f u`.
-/
noncomputable def implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ → E₂ :=
  (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂
/-
**ContDiffAt.implicitFunction_def** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：implicitFunction_def (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fder
iv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : cdf.implicitFunction pn if₂ = (cdf.has
StrictFDerivAt pn).implicitFunctionOfProdDomain if₂
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem implicitFunction_def
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    cdf.implicitFunction pn if₂ = (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂ := by
  rfl

/-- At the base point `u.1`, the implicit function evaluates to `u.2`. -/
/-
**ContDiffAt.implicitFunction_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：implicitFunction_apply_self (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ 
: (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : cdf.implicitFunction pn if₂ u.1
 = u.2
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_tendsto_nhds`：eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] 
{f : X -> Y} {x : X} {y : Y} (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain`：tendsto_implicit
FunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁
 E₂).IsInvertible) : Tendsto (dfu.implicitFu…
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x

--- 原说明 ---
At the base point `u.1`, the implicit function evaluates to `u.2`.
-/
theorem implicitFunction_apply_self
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    cdf.implicitFunction pn if₂ u.1 = u.2 :=
  eq_of_tendsto_nhds ((cdf.hasStrictFDerivAt pn).tendsto_implicitFunctionOfProdDomain if₂)

/-- `implicitFunction` is indeed the (local) implicit function defined by `f`. -/
/-
**ContDiffAt.eventually_apply_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `ContDi
ffAt`。
形式化陈述：eventually_apply_implicitFunction (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0)
 (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ x in 𝓝 u.1, f (x,
 cdf.implicitFunction pn if₂ x) = f u
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain`：eventua
lly_apply_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u :
 (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ x in 𝓝…
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x

--- 原说明 ---
`implicitFunction` is indeed the (local) implicit function defined by `f`.
-/
theorem eventually_apply_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, f (x, cdf.implicitFunction pn if₂ x) = f u :=
  (cdf.hasStrictFDerivAt pn).eventually_apply_implicitFunctionOfProdDomain if₂
/-
**ContDiffAt.eventually_apply_eq_iff_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 
`ContDiffAt`。
形式化陈述：eventually_apply_eq_iff_implicitFunction (cdf : ContDiffAt 𝕜 n f u) (pn : 
n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ v in 𝓝 u, 
f v = f u ↔ cdf.implicitFunction pn if₂ v.1 = v.2
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain`：
eventually_apply_eq_iff_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f 
f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ…
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x
-/
theorem eventually_apply_eq_iff_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ cdf.implicitFunction pn if₂ v.1 = v.2 :=
  (cdf.hasStrictFDerivAt pn).eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂
/-
**ContDiffAt.hasStrictFDerivAt_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `ContD
iffAt`。
形式化陈述：hasStrictFDerivAt_implicitFunction (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0
) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : HasStrictFDerivAt (cdf.i
mplicitFunction pn if₂) (-(fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (fderiv 𝕜 f 
u ∘L .inl 𝕜 E₁ E₂)) u.1
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain`：hasStr
ictFDerivAt_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u
 : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : HasStrictFDer…
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x
-/
theorem hasStrictFDerivAt_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (cdf.implicitFunction pn if₂)
      (-(fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (fderiv 𝕜 f u ∘L .inl 𝕜 E₁ E₂)) u.1 :=
  (cdf.hasStrictFDerivAt pn).hasStrictFDerivAt_implicitFunctionOfProdDomain if₂

/-- If the implicit equation `f` is $C^n$ at `(u₁, u₂)`, then its implicit function `ψ` around `u₁`
is also $C^n$ at `u₁`. -/
/-
**ContDiffAt.contDiffAt_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：contDiffAt_implicitFunction (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ 
: (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : ContDiffAt 𝕜 n (cdf.implicitFun
ction pn if₂) u.1
参数：cdf : ContDiffAt 𝕜 n f u；pn : n != 0；if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.hasStrictFDerivAt`：ContDiffAt.hasStrictFDerivAt {f : E' -> F'
} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) : HasStrictFDerivAt f (fderiv
 𝕂 f x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffAt.implicitFunction_def`：implicitFunction_def (cdf : ContDiffAt 
𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : cdf
.implicitFunction pn …
· 使用定理 `HasStrictFDerivAt.implicitFunctionOfProdDomain_def`：implicitFunctionOfPr
odDomain_def {dfu : HasStrictFDerivAt f f'u u} {if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsI
nvertible} : dfu.implicitFunctionOfProdD…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain`：∀ {𝕜 : Type u_1} 
[inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_1 : NormedAddCommGroup 
E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 :…
· 使用定理 `ImplicitFunctionData.prodFun_apply`：prodFun_apply (x : E) : φ.prodFun x 
= (φ.leftFun x, φ.rightFun x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain`：∀ {𝕜 : Type 
u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_1 : NormedAddCommG
roup E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 :…
· 使用定理 `HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain`：∀ {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_1 : NormedAddComm
Group E₁]   [inst_2 : NormedSpace 𝕜 E₁] [inst_3 :…
· 使用定理 `ImplicitFunctionData.contDiffAt_implicitFunction`：contDiffAt_implicitFun
ction {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : Nat∞ω} (hl : ContDiffAt 𝕜 n φ.le
ftFun φ.pt) (hr : ContDiffAt 𝕜 n φ.rig…
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p
· 使用定理 `ContDiffAt.snd`：ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).2) x
· 使用定理 `ContDiffAt.fun_comp`：ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g 
(f x)) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => g (f x)) x
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x

--- 原说明 ---
If the implicit equation `f` is $C^n$ at `(u₁, u₂)`, then its implicit function 
`ψ` around `u₁`
is also $C^n$ at `u₁`.
-/
theorem contDiffAt_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ContDiffAt 𝕜 n (cdf.implicitFunction pn if₂) u.1 := by
  rw [ContDiffAt.implicitFunction_def, HasStrictFDerivAt.implicitFunctionOfProdDomain_def]
  set φ := (cdf.hasStrictFDerivAt pn).implicitFunctionDataOfProdDomain if₂
  have : ContDiffAt 𝕜 n φ.implicitFunction.uncurry (f u, u.1) := by
    simpa [φ] using φ.contDiffAt_implicitFunction
      (by simpa [φ] using cdf) (by simpa [φ] using contDiffAt_fst) pn
  fun_prop

end ContDiffAt

/-- A predicate stating the sufficient conditions on an implicit equation `f : E₁ × E₂ → F` that
will lead to a $C^n$ implicit function `ψ : E₁ → E₂`. -/
@[deprecated "ContDiffAt.implicitFunction does not require this" (since := "2026-01-27")]
/-
**IsContDiffImplicitAt** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : RCLike 𝕜] →     {E₁ : Type u_2} →       [inst_1
 : NormedAddCommGroup E₁] →         [inst_2 : NormedSpace 𝕜 E₁] →           {E₂ 
: Type u_3} →             [inst_3 : NormedAddCommGroup E₂] →               [inst
_4 : NormedSpace 𝕜 E₂] →                 {F : Type u_4} →                   [ins
t_5 : NormedAddCommGroup F] →                     [inst_6 : NormedSpace 𝕜 F] → W
ithTop ℕ∞ → (E₁ × E₂ → F) → (E₁ × E₂ →L[𝕜] F) → E₁ × E₂ → Prop
参数：E₁ × E₂ → F；E₁ × E₂ →L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate stating the sufficient conditions on an implicit equation `f : E₁ × 
E₂ → F` that
will lead to a $C^n$ implicit function `ψ : E₁ → E₂`.
-/
structure IsContDiffImplicitAt (n : ℕ∞ω) (f : E₁ × E₂ → F) (f' : E₁ × E₂ →L[𝕜] F)
    (u : E₁ × E₂) : Prop where
  hasFDerivAt : HasFDerivAt f f' u
  contDiffAt : ContDiffAt 𝕜 n f u
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂))
  ne_zero : n ≠ 0

namespace IsContDiffImplicitAt

@[deprecated (since := "2026-01-27")]
alias implicitFunction := ContDiffAt.implicitFunction

@[deprecated (since := "2026-01-27")]
alias implicitFunction_def := ContDiffAt.implicitFunction_def

@[deprecated (since := "2026-01-27")]
alias apply_implicitFunction := ContDiffAt.eventually_apply_implicitFunction

@[deprecated (since := "2026-01-27")]
alias eventually_implicitFunction_apply_eq := ContDiffAt.eventually_apply_eq_iff_implicitFunction

@[deprecated (since := "2026-01-27")]
alias contDiffAt_implicitFunction := ContDiffAt.contDiffAt_implicitFunction

end IsContDiffImplicitAt

end

