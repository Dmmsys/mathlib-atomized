/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of continuous linear maps from the base field

In this file we prove that `f : 𝕜 →L[𝕜] E` (or `f : 𝕜 →ₗ[𝕜] E`) has derivative `f 1`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, linear map
-/

public section


universe u v w

open Topology Filter

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/

variable (e : 𝕜 →L[𝕜] F)

/-
**ContinuousLinearMap.hasDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {L : Filter (𝕜 × 𝕜)} (e : 𝕜 →L
[𝕜] F), HasDerivAtFilter (⇑e) (e 1) L
参数：𝕜 × 𝕜；e : 𝕜 →L[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) L :=
  e.hasFDerivAtFilter.hasDerivAtFilter
/-
**ContinuousLinearMap.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →L[𝕜] F), HasSt
rictDerivAt (⇑e) (e 1) x
参数：e : 𝕜 →L[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : Nontriviall
yNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedS
pace 𝕜 F] {L : Filter (𝕜 ×…
-/
protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasDerivAtFilter
/-
**ContinuousLinearMap.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →L[𝕜] F), HasDe
rivAt (⇑e) (e 1) x
参数：e : 𝕜 →L[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : Nontriviall
yNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedS
pace 𝕜 F] {L : Filter (𝕜 ×…
-/
protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
/-
**ContinuousLinearMap.hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} {s : Set 𝕜} (e : 𝕜 →L[
𝕜] F), HasDerivWithinAt (⇑e) (e 1) s x
参数：e : 𝕜 →L[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : Nontriviall
yNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedS
pace 𝕜 F] {L : Filter (𝕜 ×…
-/
protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter

@[simp]
/-
**ContinuousLinearMap.deriv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →L[𝕜] F), deriv
 (⇑e) x = e 1
参数：e : 𝕜 →L[𝕜] F；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `ContinuousLinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜
 F] {x : 𝕜} (e : 𝕜 →…
-/
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
/-
**ContinuousLinearMap.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} {s : Set 𝕜} (e : 𝕜 →L[
𝕜] F), UniqueDiffWithinAt 𝕜 s x → derivWithin (⇑e) s x = e 1
参数：e : 𝕜 →L[𝕜] F；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `ContinuousLinearMap.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : Nontriviall
yNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedS
pace 𝕜 F] {x : 𝕜} {s : Set…
-/
protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/

variable (e : 𝕜 →ₗ[𝕜] F)

/-
**LinearMap.hasDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {L : Filter (𝕜 × 𝕜)} (e : 𝕜 →ₗ
[𝕜] F), HasDerivAtFilter (⇑e) (e 1) L
参数：𝕜 × 𝕜；e : 𝕜 →ₗ[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : Nontriviall
yNormedField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedS
pace 𝕜 F] {L : Filter (𝕜 ×…
-/
protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) L :=
  e.toContinuousLinearMap₁.hasDerivAtFilter
/-
**LinearMap.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →ₗ[𝕜] F), HasSt
rictDerivAt (⇑e) (e 1) x
参数：e : 𝕜 →ₗ[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{L : Filter (𝕜 ×…
-/
protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasDerivAtFilter
/-
**LinearMap.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →ₗ[𝕜] F), HasDe
rivAt (⇑e) (e 1) x
参数：e : 𝕜 →ₗ[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{L : Filter (𝕜 ×…
-/
protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
/-
**LinearMap.hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} {s : Set 𝕜} (e : 𝕜 →ₗ[
𝕜] F), HasDerivWithinAt (⇑e) (e 1) s x
参数：e : 𝕜 →ₗ[𝕜] F；⇑e；e 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{L : Filter (𝕜 ×…
-/
protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter

@[simp]
/-
**LinearMap.deriv** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →ₗ[𝕜] F), deriv
 (⇑e) x = e 1
参数：e : 𝕜 →ₗ[𝕜] F；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `LinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜
} (e : 𝕜 →…
-/
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
/-
**LinearMap.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} {s : Set 𝕜} (e : 𝕜 →ₗ[
𝕜] F), UniqueDiffWithinAt 𝕜 s x → derivWithin (⇑e) s x = e 1
参数：e : 𝕜 →ₗ[𝕜] F；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `LinearMap.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{x : 𝕜} {s : Set…
-/
protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs

end LinearMap

