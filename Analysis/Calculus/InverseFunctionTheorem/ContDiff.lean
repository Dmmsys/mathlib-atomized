/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, `C^r` case

In this file we specialize the inverse function theorem to `C^r`-smooth functions.
-/

@[expose] public section

noncomputable section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
variable [CompleteSpace E] (f : E → F) {f' : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns an `OpenPartialHomeomorph` with `to_fun = f` and `a ∈ source`. -/
/-
**ContDiffAt.toOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffAt`。
形式化陈述：toOpenPartialHomeomorph (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f'
 : E ->L[𝕂] F) a) (hn : n != 0) : OpenPartialHomeomorph E F
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns an `OpenPartialHomeomorph` with `to_fun = f` and `a ∈
 source`.
-/
def toOpenPartialHomeomorph (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : n ≠ 0) : OpenPartialHomeomorph E F :=
  (hf.hasStrictFDerivAt' hf' hn).toOpenPartialHomeomorph f

variable {f}

@[simp]
/-
**ContDiffAt.toOpenPartialHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：toOpenPartialHomeomorph_coe (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f
 (f' : E ->L[𝕂] F) a) (hn : n != 0) : (hf.toOpenPartialHomeomorph f hf' hn : E -
> F) = f
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_coe (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    (hf.toOpenPartialHomeomorph f hf' hn : E → F) = f :=
  rfl
/-
**ContDiffAt.mem_toOpenPartialHomeomorph_source** 是 Mathlib 中的一个定理，位于命名空间 `ContD
iffAt`。
形式化陈述：mem_toOpenPartialHomeomorph_source (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDe
rivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) : a in (hf.toOpenPartialHomeomorph f 
hf' hn).source
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
· 使用定理 `ContDiffAt.hasStrictFDerivAt'`：ContDiffAt.hasStrictFDerivAt' {f : E' -> 
F'} {f' : E' ->L[𝕂] F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f 
f' x) (hn : n != 0)…
-/
theorem mem_toOpenPartialHomeomorph_source (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    a ∈ (hf.toOpenPartialHomeomorph f hf' hn).source :=
  (hf.hasStrictFDerivAt' hf' hn).mem_toOpenPartialHomeomorph_source
/-
**ContDiffAt.image_mem_toOpenPartialHomeomorph_target** 是 Mathlib 中的一个定理，位于命名空间 
`ContDiffAt`。
形式化陈述：image_mem_toOpenPartialHomeomorph_target (hf : ContDiffAt 𝕂 n f a) (hf' : 
HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) : f a in (hf.toOpenPartialHomeo
morph f hf' hn).target
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target`：image_mem_to
OpenPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : f 
a in (hf.toOpenPartialHomeomorph f).target
· 使用定理 `ContDiffAt.hasStrictFDerivAt'`：ContDiffAt.hasStrictFDerivAt' {f : E' -> 
F'} {f' : E' ->L[𝕂] F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f 
f' x) (hn : n != 0)…
-/
theorem image_mem_toOpenPartialHomeomorph_target (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    f a ∈ (hf.toOpenPartialHomeomorph f hf' hn).target :=
  (hf.hasStrictFDerivAt' hf' hn).image_mem_toOpenPartialHomeomorph_target

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
/-
**ContDiffAt.localInverse** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffAt`。
形式化陈述：localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L[𝕂]
 F) a) (hn : n != 0) : F -> E
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible de
rivative
at `a`, returns a function that is locally inverse to `f`.
-/
def localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : n ≠ 0) : F → E :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a
/-
**ContDiffAt.localInverse_apply_image** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：localInverse_apply_image (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f
' : E ->L[𝕂] F) a) (hn : n != 0) : hf.localInverse hf' hn (f a) = a
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.localInverse_apply_image`：localInverse_apply_image (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : hf.localInverse f f' a (f a) = a
· 使用定理 `ContDiffAt.hasStrictFDerivAt'`：ContDiffAt.hasStrictFDerivAt' {f : E' -> 
F'} {f' : E' ->L[𝕂] F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f 
f' x) (hn : n != 0)…
-/
theorem localInverse_apply_image (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `ContDiff.toOpenPartialHomeomorph`) is
also `ContDiff`. -/
/-
**ContDiffAt.to_localInverse** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：to_localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L
[𝕂] F) a) (hn : n != 0) : ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a)
参数：hf : ContDiffAt 𝕂 n f a；hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.localInverse_apply_image`：localInverse_apply_image (hf : Cont
DiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) : hf.loc
alInverse hf' hn (f a) = …
· 使用定理 `OpenPartialHomeomorph.contDiffAt_symm`：OpenPartialHomeomorph.contDiffAt_
symm [CompleteSpace E] (f : OpenPartialHomeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
 (ha : a in f.target) (hf₀'…
· 使用定理 `ContDiffAt.image_mem_toOpenPartialHomeomorph_target`：image_mem_toOpenPar
tialHomeomorph_target (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L
[𝕂] F) a) (hn : n != 0) : f a in (hf.toOp…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible de
rivative
at `a`, the inverse function (produced by `ContDiff.toOpenPartialHomeomorph`) is
also `ContDiff`.
-/
theorem to_localInverse (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert! hf'
  · convert! hf

end ContDiffAt

