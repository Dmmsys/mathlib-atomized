/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Algebra.Star.Basic

/-!
# Continuity of `star`

This file defines the `ContinuousStar` typeclass, along with instances on `Pi`, `Prod`,
`MulOpposite`, and `Units`.
-/

@[expose] public section

open Filter Topology

/-- Basic hypothesis to talk about a topological space with a continuous `star` operator. -/
/-
**ContinuousStar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [TopologicalSpace R] → [Star R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a topological space with a continuous `star` oper
ator.
-/
class ContinuousStar (R : Type*) [TopologicalSpace R] [Star R] : Prop where
  /-- The `star` operator is continuous. -/
  continuous_star : Continuous (star : R → R)

export ContinuousStar (continuous_star)

section Continuity

variable {α R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R]

/-
**continuousOn_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_star {s : Set R} : ContinuousOn star s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem continuousOn_star {s : Set R} : ContinuousOn star s :=
  continuous_star.continuousOn
/-
**continuousWithinAt_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.continuousWithinAt
/-
**continuousAt_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_star {x : R} : ContinuousAt star x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem continuousAt_star {x : R} : ContinuousAt star x :=
  continuous_star.continuousAt
/-
**tendsto_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a))
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_star`：continuousAt_star {x : R} : ContinuousAt star x
-/
theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuousAt_star
/-
**Filter.Tendsto.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.star {f : α -> R} {l : Filter α} {y : R} (h : Tendsto f l (
𝓝 y)) : Tendsto (fun x => star (f x)) l (𝓝 (star y))
参数：h : Tendsto f l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem Filter.Tendsto.star {f : α → R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.tendsto y).comp h

variable [TopologicalSpace α] {f : α → R} {s : Set α} {x : α}

@[continuity, fun_prop]
/-
**Continuous.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.star (hf : Continuous f) : Continuous fun x => star (f x)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) :=
  continuous_star.comp hf

@[fun_prop]
/-
**ContinuousAt.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f
 x)) x
参数：hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_star`：continuousAt_star {x : R} : ContinuousAt star x
-/
theorem ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f x)) x :=
  continuousAt_star.comp hf

@[fun_prop]
/-
**ContinuousOn.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f
 x)) s
参数：hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f x)) s :=
  continuous_star.comp_continuousOn hf
/-
**ContinuousWithinAt.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) : ContinuousWithin
At (fun x => star (f x)) s x
参数：hf : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.star`：Filter.Tendsto.star {f : α -> R} {l : Filter α} {y 
: R} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => star (f x)) l (𝓝 (star y))
-/
theorem ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => star (f x)) s x :=
  Filter.Tendsto.star hf

/-- The star operation bundled as a continuous map. -/
@[simps]
/-
**starContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starContinuousMap : C(R, R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star

--- 原说明 ---
The star operation bundled as a continuous map.
-/
def starContinuousMap : C(R, R) :=
  ⟨star, continuous_star⟩

end Continuity

section Instances

variable {R S ι : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star R] [Star S] [TopologicalSpace R] [TopologicalSpace S] [ContinuousStar R]
    [ContinuousStar S] : ContinuousStar (R × S) :=
  ⟨(continuous_star.comp continuous_fst).prodMk (continuous_star.comp continuous_snd)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Star (C i)]
    [∀ i, ContinuousStar (C i)] : ContinuousStar (∀ i, C i) where
  continuous_star := continuous_pi fun i => Continuous.star (continuous_apply i)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.star⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] :
    ContinuousStar Rˣ :=
  ⟨continuous_induced_rng.2 Units.continuous_embedProduct.star⟩

end Instances

