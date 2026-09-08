/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
/-!
# Derivatives of affine maps

In this file we prove formulas for one-dimensional derivatives of affine maps `f : 𝕜 →ᵃ[𝕜] E`. We
also specialise some of these results to `AffineMap.lineMap` because it is useful to transfer MVT
from dimension 1 to a domain in higher dimension.

## TODO

Add theorems about `deriv`s and `fderiv`s of `ContinuousAffineMap`s once they will be ported to
Mathlib 4.

## Keywords

affine map, derivative, differentiability
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : 𝕜 →ᵃ[𝕜] E) {a b : E} {L : Filter (𝕜 × 𝕜)} {s : Set 𝕜} {x : 𝕜}

namespace AffineMap

/-
**AffineMap.hasDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.decomp`：decomp (f : V1 ->ᵃ[k] V2) : (f : V1 -> V2) = ⇑f.linear
 + fun _ => f 0
· 使用定理 `HasDerivAtFilter.add_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{f : 𝕜 → F} {f' …
· 使用定理 `LinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{L : Filter (𝕜 ×…
-/
theorem hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) L := by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)
/-
**AffineMap.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasStrictDerivAt : HasStrictDerivAt f (f.linear 1) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.hasDerivAtFilter`：hasDerivAtFilter : HasDerivAtFilter f (f.lin
ear 1) L
-/
theorem hasStrictDerivAt : HasStrictDerivAt f (f.linear 1) x := f.hasDerivAtFilter
/-
**AffineMap.hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasDerivWithinAt : HasDerivWithinAt f (f.linear 1) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.hasDerivAtFilter`：hasDerivAtFilter : HasDerivAtFilter f (f.lin
ear 1) L
-/
theorem hasDerivWithinAt : HasDerivWithinAt f (f.linear 1) s x := f.hasDerivAtFilter
/-
**AffineMap.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasDerivAt : HasDerivAt f (f.linear 1) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.hasDerivAtFilter`：hasDerivAtFilter : HasDerivAtFilter f (f.lin
ear 1) L
-/
theorem hasDerivAt : HasDerivAt f (f.linear 1) x := f.hasDerivAtFilter
/-
**AffineMap.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →ᵃ[𝕜] E) {s : Set 𝕜
} {x : 𝕜},   UniqueDiffWithinAt 𝕜 s x → derivWithin (⇑f) s x = f.linear 1
参数：f : 𝕜 →ᵃ[𝕜] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `AffineMap.hasDerivWithinAt`：hasDerivWithinAt : HasDerivWithinAt f (f.lin
ear 1) s x
-/
protected theorem derivWithin (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f.linear 1 :=
  f.hasDerivWithinAt.derivWithin hs
/-
**AffineMap.deriv** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →ᵃ[𝕜] E) {x : 𝕜}, d
eriv (⇑f) x = f.linear 1
参数：f : 𝕜 →ᵃ[𝕜] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `AffineMap.hasDerivAt`：hasDerivAt : HasDerivAt f (f.linear 1) x
-/
@[simp] protected theorem deriv : deriv f x = f.linear 1 := f.hasDerivAt.deriv
/-
**AffineMap.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →ᵃ[𝕜] E) {x : 𝕜}, D
ifferentiableAt 𝕜 (⇑f) x
参数：f : 𝕜 →ᵃ[𝕜] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `AffineMap.hasDerivAt`：hasDerivAt : HasDerivAt f (f.linear 1) x
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 f x := f.hasDerivAt.differentiableAt
/-
**AffineMap.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →ᵃ[𝕜] E), Different
iable 𝕜 ⇑f
参数：f : 𝕜 →ᵃ[𝕜] E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] (f : 𝕜 →ᵃ[𝕜]…
-/
protected theorem differentiable : Differentiable 𝕜 f := fun _ ↦ f.differentiableAt
/-
**AffineMap.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →ᵃ[𝕜] E) {s : Set 𝕜
} {x : 𝕜}, DifferentiableWithinAt 𝕜 (⇑f) s x
参数：f : 𝕜 →ᵃ[𝕜] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `AffineMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] (f : 𝕜 →ᵃ[𝕜]…
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt
/-
**AffineMap.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →ᵃ[𝕜] E) {s : Set 𝕜
}, DifferentiableOn 𝕜 (⇑f) s
参数：f : 𝕜 →ᵃ[𝕜] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.differentiableWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] (f : 𝕜 →ᵃ[𝕜]…
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 f s := fun _ _ ↦ f.differentiableWithinAt

/-!
### Line map

In this section we specialize some lemmas to `AffineMap.lineMap` because this map is very useful to
deduce higher-dimensional lemmas from one-dimensional versions.
-/

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.hasStrictDerivAt_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasStrictDerivAt_lineMap : HasStrictDerivAt (lineMap a b) (b - a) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_linear`：lineMap_linear (p₀ p₁ : P1) : (lineMap p₀ p₁ :
 k ->ᵃ[k] P1).linear = LinearMap.id.smulRight (p₁ -ᵥ p₀)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AffineMap.hasStrictDerivAt`：hasStrictDerivAt : HasStrictDerivAt f (f.lin
ear 1) x

--- 原说明 ---
### Line map

In this section we specialize some lemmas to `AffineMap.lineMap` because this ma
p is very useful to
deduce higher-dimensional lemmas from one-dimensional versions.
-/
theorem hasStrictDerivAt_lineMap : HasStrictDerivAt (lineMap a b) (b - a) x := by
  simpa using (lineMap a b : 𝕜 →ᵃ[𝕜] E).hasStrictDerivAt

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.hasDerivAt_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasDerivAt_lineMap : HasDerivAt (lineMap a b) (b - a) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `AffineMap.hasStrictDerivAt_lineMap`：hasStrictDerivAt_lineMap : HasStrict
DerivAt (lineMap a b) (b - a) x
-/
theorem hasDerivAt_lineMap : HasDerivAt (lineMap a b) (b - a) x :=
  hasStrictDerivAt_lineMap.hasDerivAt

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.hasDerivWithinAt_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：hasDerivWithinAt_lineMap : HasDerivWithinAt (lineMap a b) (b - a) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `AffineMap.hasDerivAt_lineMap`：hasDerivAt_lineMap : HasDerivAt (lineMap a
 b) (b - a) x
-/
theorem hasDerivWithinAt_lineMap : HasDerivWithinAt (lineMap a b) (b - a) s x :=
  hasDerivAt_lineMap.hasDerivWithinAt

end AffineMap

