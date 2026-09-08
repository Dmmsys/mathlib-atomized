/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main results

* `ContinuousAffineMap.contDiff`: a continuous affine map is smooth.
* `AffineMap.contDiff_lineMap_uncurry`: `AffineMap.lineMap` is smooth in its three arguments,
  jointly and pointwise.

-/

public section
namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
/-
**ContinuousAffineMap.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：contDiff {n : WithTop Nat∞} (f : V ->ᴬ[𝕜] W) : ContDiff 𝕜 n f
参数：f : V ->ᴬ[𝕜] W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.decomp`：∀ {R : Type u_1} {V : Type u_2} {W : Type u_
3} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   [ins
t_3 : Topologica…
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c

--- 原说明 ---
A continuous affine map between normed vector spaces is smooth.
-/
theorem contDiff {n : WithTop ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

end ContinuousAffineMap

namespace AffineMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option backward.isDefEq.respectTransparency.types false in
/-- `AffineMap.lineMap` is smooth in all three arguments. -/
@[fun_prop]
/-
**AffineMap.contDiff_lineMap_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：contDiff_lineMap_uncurry {n : WithTop Nat∞} : ContDiff 𝕜 n (fun pqc : V × 
V × 𝕜 => AffineMap.lineMap pqc.1 pqc.2.1 pqc.2.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : T
ype uF}…
· 使用定理 `ContDiff.sub`：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `ContDiff.snd`：ContDiff.snd {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).2
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `ContDiff.fst`：ContDiff.fst {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).1

--- 原说明 ---
`AffineMap.lineMap` is smooth in all three arguments.
-/
theorem contDiff_lineMap_uncurry {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun pqc : V × V × 𝕜 ↦ AffineMap.lineMap pqc.1 pqc.2.1 pqc.2.2) := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-- `AffineMap.lineMap` is smooth as a function `𝕜 → V`. -/
/-
**AffineMap.contDiff_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：contDiff_lineMap (p₀ p₁ : V) {n : WithTop Nat∞} : ContDiff 𝕜 n (AffineMap.
lineMap p₀ p₁ : 𝕜 -> V)
参数：p₀ p₁ : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.fun_comp`：ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : Con
tDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => g (f x))
· 使用定理 `AffineMap.contDiff_lineMap_uncurry`：contDiff_lineMap_uncurry {n : WithTo
p Nat∞} : ContDiff 𝕜 n (fun pqc : V × V × 𝕜 => AffineMap.lineMap pqc.1 pqc.2.1 p
qc.2.2)
· 使用定理 `contDiff_prodMk_right`：contDiff_prodMk_right (e₀ : E) : ContDiff 𝕜 n fun
 f : F => (e₀, f)

--- 原说明 ---
`AffineMap.lineMap` is smooth as a function `𝕜 → V`.
-/
theorem contDiff_lineMap (p₀ p₁ : V) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (AffineMap.lineMap p₀ p₁ : 𝕜 → V) := by
  fun_prop

end AffineMap

section LineMapComp

variable {𝕜 V E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f₁ f₂ : E → V} {g : E → 𝕜} {s : Set E} {x : E} {n : WithTop ℕ∞}

set_option backward.isDefEq.respectTransparency.types false in
@[fun_prop]
/-
**ContDiffWithinAt.lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.lineMap (h₁ : ContDiffWithinAt 𝕜 n f₁ s x) (h₂ : ContDiff
WithinAt 𝕜 n f₂ s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (f
un x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s x
参数：h₁ : ContDiffWithinAt 𝕜 n f₁ s x；h₂ : ContDiffWithinAt 𝕜 n f₂ s x；hg : ContDi
ffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `ContDiffWithinAt.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF}…
· 使用定理 `ContDiffWithinAt.sub`：ContDiffWithinAt.sub {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
-/
theorem ContDiffWithinAt.lineMap (h₁ : ContDiffWithinAt 𝕜 n f₁ s x)
    (h₂ : ContDiffWithinAt 𝕜 n f₂ s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s x := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**ContDiffAt.lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.lineMap (h₁ : ContDiffAt 𝕜 n f₁ x) (h₂ : ContDiffAt 𝕜 n f₂ x) (
hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂
 x) (g x)) x
参数：h₁ : ContDiffAt 𝕜 n f₁ x；h₂ : ContDiffAt 𝕜 n f₂ x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.fun_comp`：ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g 
(f x)) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => g (f x)) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `AffineMap.contDiff_lineMap_uncurry`：contDiff_lineMap_uncurry {n : WithTo
p Nat∞} : ContDiff 𝕜 n (fun pqc : V × V × 𝕜 => AffineMap.lineMap pqc.1 pqc.2.1 p
qc.2.2)
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
-/
theorem ContDiffAt.lineMap (h₁ : ContDiffAt 𝕜 n f₁ x)
    (h₂ : ContDiffAt 𝕜 n f₂ x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) x := by
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**ContDiffOn.lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.lineMap (h₁ : ContDiffOn 𝕜 n f₁ s) (h₂ : ContDiffOn 𝕜 n f₂ s) (
hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂
 x) (g x)) s
参数：h₁ : ContDiffOn 𝕜 n f₁ s；h₂ : ContDiffOn 𝕜 n f₂ s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.fun_comp_contDiffOn`：ContDiff.fun_comp_contDiffOn {s : Set E} {
g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContD
iffOn 𝕜 n (fun x =…
· 使用定理 `AffineMap.contDiff_lineMap_uncurry`：contDiff_lineMap_uncurry {n : WithTo
p Nat∞} : ContDiff 𝕜 n (fun pqc : V × V × 𝕜 => AffineMap.lineMap pqc.1 pqc.2.1 p
qc.2.2)
· 使用定理 `ContDiffOn.prodMk`：ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> 
G} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x :
 E => (…
-/
theorem ContDiffOn.lineMap (h₁ : ContDiffOn 𝕜 n f₁ s)
    (h₂ : ContDiffOn 𝕜 n f₂ s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s := by
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**ContDiff.lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.lineMap (h₁ : ContDiff 𝕜 n f₁) (h₂ : ContDiff 𝕜 n f₂) (hg : ContD
iff 𝕜 n g) : ContDiff 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x))
参数：h₁ : ContDiff 𝕜 n f₁；h₂ : ContDiff 𝕜 n f₂；hg : ContDiff 𝕜 n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.fun_comp`：ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : Con
tDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => g (f x))
· 使用定理 `AffineMap.contDiff_lineMap_uncurry`：contDiff_lineMap_uncurry {n : WithTo
p Nat∞} : ContDiff 𝕜 n (fun pqc : V × V × 𝕜 => AffineMap.lineMap pqc.1 pqc.2.1 p
qc.2.2)
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)
-/
theorem ContDiff.lineMap (h₁ : ContDiff 𝕜 n f₁)
    (h₂ : ContDiff 𝕜 n f₂) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) := by
  fun_prop

end LineMapComp

