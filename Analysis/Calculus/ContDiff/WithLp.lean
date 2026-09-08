/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Derivatives on `WithLp`
-/

public section

open scoped ENNReal

section PiLp

open ContinuousLinearMap WithLp

variable {𝕜 ι : Type*} {E : ι → Type*} {H : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [NormedSpace 𝕜 H] [Fintype ι] (p) [Fact (1 ≤ p)]
  {n : WithTop ℕ∞} {f : H → PiLp p E} {f' : H →L[𝕜] PiLp p E} {t : Set H} {y : H}

/-
**contDiffWithinAt_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_piLp : ContDiffWithinAt 𝕜 n f t y ↔ forall i, ContDiffWit
hinAt 𝕜 n (fun x => f x i) t y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_contDiffWithinAt_iff`：ContinuousLinearEquiv.c
omp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) : ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ Co
ntDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiffWithinAt_pi`：contDiffWithinAt_pi : ContDiffWithinAt 𝕜 n Φ s x ↔ 
forall i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffWithinAt_piLp :
    ContDiffWithinAt 𝕜 n f t y ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffWithinAt_iff, contDiffWithinAt_pi]
  rfl

@[fun_prop]
/-
**contDiffWithinAt_piLp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_piLp' (hf : forall i, ContDiffWithinAt 𝕜 n (fun x => f x 
i) t y) : ContDiffWithinAt 𝕜 n f t y
参数：hf : forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffWithinAt_piLp`：contDiffWithinAt_piLp : ContDiffWithinAt 𝕜 n f t 
y ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y
-/
theorem contDiffWithinAt_piLp' (hf : ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y) :
    ContDiffWithinAt 𝕜 n f t y :=
  (contDiffWithinAt_piLp p).2 hf

@[fun_prop]
/-
**contDiffWithinAt_piLp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_piLp_apply {i : ι} {t : Set (PiLp p E)} {y : PiLp p E} : 
ContDiffWithinAt 𝕜 n (fun f : PiLp p E => f i) t y
参数：PiLp p E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_piLp`：contDiffWithinAt_piLp : ContDiffWithinAt 𝕜 n f t 
y ↔ forall i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
-/
theorem contDiffWithinAt_piLp_apply {i : ι} {t : Set (PiLp p E)} {y : PiLp p E} :
    ContDiffWithinAt 𝕜 n (fun f : PiLp p E => f i) t y :=
  (contDiffWithinAt_piLp p).1 contDiffWithinAt_id i
/-
**contDiffAt_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_piLp : ContDiffAt 𝕜 n f y ↔ forall i, ContDiffAt 𝕜 n (fun x => 
f x i) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_contDiffAt_iff`：ContinuousLinearEquiv.comp_co
ntDiffAt_iff (e : F ≃L[𝕜] G) : ContDiffAt 𝕜 n (e ∘ f) x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `contDiffAt_pi`：contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ forall i, ContDiffAt
 𝕜 n (fun x => Φ x i) x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffAt_piLp :
    ContDiffAt 𝕜 n f y ↔ ∀ i, ContDiffAt 𝕜 n (fun x => f x i) y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffAt_iff, contDiffAt_pi]
  rfl

@[fun_prop]
/-
**contDiffAt_piLp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_piLp' (hf : forall i, ContDiffAt 𝕜 n (fun x => f x i) y) : Cont
DiffAt 𝕜 n f y
参数：hf : forall i, ContDiffAt 𝕜 n (fun x => f x i) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffAt_piLp`：contDiffAt_piLp : ContDiffAt 𝕜 n f y ↔ forall i, ContDi
ffAt 𝕜 n (fun x => f x i) y
-/
theorem contDiffAt_piLp' (hf : ∀ i, ContDiffAt 𝕜 n (fun x => f x i) y) :
    ContDiffAt 𝕜 n f y :=
  (contDiffAt_piLp p).2 hf

@[fun_prop]
/-
**contDiffAt_piLp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_piLp_apply {i : ι} {y : PiLp p E} : ContDiffAt 𝕜 n (fun f : PiL
p p E => f i) y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffAt_piLp`：contDiffAt_piLp : ContDiffAt 𝕜 n f y ↔ forall i, ContDi
ffAt 𝕜 n (fun x => f x i) y
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
-/
theorem contDiffAt_piLp_apply {i : ι} {y : PiLp p E} :
    ContDiffAt 𝕜 n (fun f : PiLp p E => f i) y :=
  (contDiffAt_piLp p).1 contDiffAt_id i
/-
**contDiffOn_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_piLp : ContDiffOn 𝕜 n f t ↔ forall i, ContDiffOn 𝕜 n (fun x => 
f x i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_contDiffOn_iff`：ContinuousLinearEquiv.comp_co
ntDiffOn_iff (e : F ≃L[𝕜] G) : ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `contDiffOn_pi`：contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ forall i, ContDiffOn
 𝕜 n (fun x => Φ x i) s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffOn_piLp :
    ContDiffOn 𝕜 n f t ↔ ∀ i, ContDiffOn 𝕜 n (fun x => f x i) t := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiffOn_iff, contDiffOn_pi]
  rfl

@[fun_prop]
/-
**contDiffOn_piLp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_piLp' (hf : forall i, ContDiffOn 𝕜 n (fun x => f x i) t) : Cont
DiffOn 𝕜 n f t
参数：hf : forall i, ContDiffOn 𝕜 n (fun x => f x i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_piLp`：contDiffOn_piLp : ContDiffOn 𝕜 n f t ↔ forall i, ContDi
ffOn 𝕜 n (fun x => f x i) t
-/
theorem contDiffOn_piLp' (hf : ∀ i, ContDiffOn 𝕜 n (fun x => f x i) t) :
    ContDiffOn 𝕜 n f t :=
  (contDiffOn_piLp p).2 hf

@[fun_prop]
/-
**contDiffOn_piLp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_piLp_apply {i : ι} {t : Set (PiLp p E)} : ContDiffOn 𝕜 n (fun f
 : PiLp p E => f i) t
参数：PiLp p E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_piLp`：contDiffOn_piLp : ContDiffOn 𝕜 n f t ↔ forall i, ContDi
ffOn 𝕜 n (fun x => f x i) t
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
-/
theorem contDiffOn_piLp_apply {i : ι} {t : Set (PiLp p E)} :
    ContDiffOn 𝕜 n (fun f : PiLp p E => f i) t :=
  (contDiffOn_piLp p).1 contDiffOn_id i
/-
**contDiff_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_piLp : ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n fun x => f x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_contDiff_iff`：ContinuousLinearEquiv.comp_cont
Diff_iff (e : F ≃L[𝕜] G) : ContDiff 𝕜 n (e ∘ f) ↔ ContDiff 𝕜 n f
· 使用定理 `contDiff_pi`：contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x
 => Φ x i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiff_piLp : ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n fun x => f x i := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_contDiff_iff, contDiff_pi]
  rfl

@[fun_prop]
/-
**contDiff_piLp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_piLp' (hf : forall i, ContDiff 𝕜 n (fun x => f x i)) : ContDiff 𝕜
 n f
参数：hf : forall i, ContDiff 𝕜 n (fun x => f x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_piLp`：contDiff_piLp : ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n f
un x => f x i
-/
theorem contDiff_piLp' (hf : ∀ i, ContDiff 𝕜 n (fun x => f x i)) :
    ContDiff 𝕜 n f :=
  (contDiff_piLp p).2 hf

@[fun_prop]
/-
**contDiff_piLp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_piLp_apply {i : ι} : ContDiff 𝕜 n (fun f : PiLp p E => f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_piLp`：contDiff_piLp : ContDiff 𝕜 n f ↔ forall i, ContDiff 𝕜 n f
un x => f x i
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiff_piLp_apply {i : ι} :
    ContDiff 𝕜 n (fun f : PiLp p E => f i) :=
  (contDiff_piLp p).1 contDiff_id i

variable {p}
/-
**PiLp.contDiff_ofLp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PiLp.contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (Π i, E i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
-/
lemma PiLp.contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (Π i, E i)) :=
  (continuousLinearEquiv p 𝕜 E).contDiff
/-
**PiLp.contDiff_toLp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PiLp.contDiff_toLp : ContDiff 𝕜 n (@toLp p (Π i, E i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
-/
lemma PiLp.contDiff_toLp : ContDiff 𝕜 n (@toLp p (Π i, E i)) :=
  (continuousLinearEquiv p 𝕜 E).symm.contDiff

end PiLp

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : WithTop ℕ∞}

/-
**WithLp.contDiff_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (E × F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
-/
lemma contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (E × F)) :=
  (prodContinuousLinearEquiv p 𝕜 E F).contDiff
/-
**WithLp.contDiff_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：contDiff_toLp : ContDiff 𝕜 n (@toLp p (E × F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
-/
lemma contDiff_toLp : ContDiff 𝕜 n (@toLp p (E × F)) :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.contDiff

end WithLp

