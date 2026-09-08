/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Snowflaking of a metric space

Given a (pseudo) (extended) metric space `X` and a number `0 < α ≤ 1`,
one can consider the metric given by `d x y = (dist x y) ^ α`.
The metric space determined by this new metric is said to be the `α`-snowflaking  (or `α`-snowflake)
of `X`. In this file we define `Metric.Snowflaking X α hα₀ hα₁` to be a one-field structure wrapper
around `X` with metric given by this formula.

The use of the term *snowflaking* arises from the fact that if one chooses `X := Set.Icc 0 1` and
`α := log 3 / log 4`, then `Metric.Snowflaking X α … …` is isometric to the von Koch snowflake,
where we equip that space with the natural metric induced by the `α⁻¹`-Hausdorff measure of paths.

Snowflake metrics are used regularly in the geometry of metric spaces where, among other things,
they characterize doubling metrics. In particular, a metric is doubling if and only
if every `α`-snowflaking (with `0 < α < 1`) of it is bilipschitz equivalent to a subset of some
Euclidean space (the dimension of the Euclidean space depends on `α`). See [heinonen2001].

Another reason to introduce this definition is the following.
In the proof of his version of the Morse-Sard theorem,
Moreira [Moreira2001] studies maps of two variables that are Lipschitz continuous in one variable,
but satisfy a stronger assumption `‖f (a, y) - f (a, b)‖ = O(‖y - b‖ ^ (k + α))`
along the second variable, as long as `(a, b)` is one of the "interesting" points.

If we want to apply Vitali covering theorem in this context, we need to cover the set by products
`closedBall a (R ^ (k + α)) ×ˢ closedBall b R` so that both components make a similar contribution
to `‖f (x, y) - f (a, b)‖`. These sets aren't balls in the original metric
(or even subsets of balls that occupy at least a fixed fraction of the volume,
as we require in our version of Vitali theorem).

However, if we change the metric on the first component to the one introduced in this file,
then these sets become balls, and we can apply Vitali theorem.

## References
* [Carlos Gustavo T. de A. Moreira, _Hausdorff measures and the Morse-Sard theorem_]
  [Moreira2001]
-/

@[expose] public section

open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

namespace Metric

/-- A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure. -/
@[ext]
/-
**Metric.Snowflaking** 是 Mathlib 中的一个归纳类型，位于命名空间 `Metric`。
形式化陈述：Type u_1 → (α : ℝ) → 0 < α → α ≤ 1 → Type u_1
参数：α : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure.
-/
structure Snowflaking (X : Type*) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) where
  /-- The value wrapped in `x : Snowflaking X α hα₀ hα₁`. -/
  val : X

namespace Snowflaking

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

/-- The natural equivalence between `Snowflaking X α hr₀ hr₁` and `X`. -/
/-
**Metric.Snowflaking.ofSnowflaking** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Snowflaking
`。
形式化陈述：ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between `Snowflaking X α hr₀ hr₁` and `X`.
-/
def ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The natural equivalence between `X` and `Snowflaking X α hr₀ hr₁`. -/
/-
**Metric.Snowflaking.toSnowflaking** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Snowflaking
`。
形式化陈述：toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural equivalence between `X` and `Snowflaking X α hr₀ hr₁`.
-/
def toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁ := ofSnowflaking.symm

@[simp]
/-
**Metric.Snowflaking.toSnowflaking.sizeOf_spec** 是 Mathlib 中的一个定理，位于命名空间 `Metric
.Snowflaking.toSnowflaking`。
形式化陈述：∀ {X : Type u_1} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1} [inst : SizeOf X] (x 
: X),   sizeOf (Metric.Snowflaking.toSnowflaking x) = 1 + sizeOf x
参数：x : X；Metric.Snowflaking.toSnowflaking x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSnowflaking.sizeOf_spec [SizeOf X] (x : X) :
    sizeOf (toSnowflaking x : Snowflaking X α hα₀ hα₁) = 1 + sizeOf x :=
  rfl

attribute [nolint simpNF] mk.injEq

/-- This definition makes `cases x` and `induction x` use `toSnowflaking` instead of `mk`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Metric.Snowflaking.casesOn_toSnowflaking** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Sno
wflaking`。
形式化陈述：casesOn_toSnowflaking {motive : Snowflaking X α hα₀ hα₁ -> Sort*} (toSnowf
laking : forall x, motive (Snowflaking.toSnowflaking x)) (x : Snowflaking X α hα
₀ hα₁) : motive x
参数：toSnowflaking : forall x, motive (Snowflaking.toSnowflaking x)；x : Snowflakin
g X α hα₀ hα₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition makes `cases x` and `induction x` use `toSnowflaking` instead of
 `mk`.
-/
def casesOn_toSnowflaking {motive : Snowflaking X α hα₀ hα₁ → Sort*}
    (toSnowflaking : ∀ x, motive (Snowflaking.toSnowflaking x)) (x : Snowflaking X α hα₀ hα₁) :
    motive x :=
  toSnowflaking x.val

@[simp]
/-
**Metric.Snowflaking.mk_eq_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Snowf
laking`。
形式化陈述：mk_eq_toSnowflaking : (mk : X -> Snowflaking X α hα₀ hα₁) = toSnowflaking
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq_toSnowflaking : (mk : X → Snowflaking X α hα₀ hα₁) = toSnowflaking := rfl

@[simp]
/-
**Metric.Snowflaking.val_eq_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Snow
flaking`。
形式化陈述：val_eq_ofSnowflaking : (val : Snowflaking X α hα₀ hα₁ -> X) = ofSnowflakin
g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_ofSnowflaking : (val : Snowflaking X α hα₀ hα₁ → X) = ofSnowflaking := rfl

@[simp]
/-
**Metric.Snowflaking.symm_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Snowfl
aking`。
形式化陈述：symm_toSnowflaking : (toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁).symm = 
ofSnowflaking
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_toSnowflaking :
    (toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁).symm = ofSnowflaking :=
  rfl

@[simp]
/-
**Metric.Snowflaking.symm_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Snowfl
aking`。
形式化陈述：symm_ofSnowflaking : (ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X).symm = 
toSnowflaking
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_ofSnowflaking :
    (ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X).symm = toSnowflaking :=
  rfl

@[simp]
/-
**Metric.Snowflaking.toSnowflaking_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic.Snowflaking`。
形式化陈述：toSnowflaking_ofSnowflaking (x : Snowflaking X α hα₀ hα₁) : toSnowflaking 
x.ofSnowflaking = x
参数：x : Snowflaking X α hα₀ hα₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSnowflaking_ofSnowflaking (x : Snowflaking X α hα₀ hα₁) :
    toSnowflaking x.ofSnowflaking = x :=
  rfl

@[simp]
/-
**Metric.Snowflaking.ofSnowflaking_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic.Snowflaking`。
形式化陈述：ofSnowflaking_toSnowflaking (x : X) : (toSnowflaking x : Snowflaking X α h
α₀ hα₁).ofSnowflaking = x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSnowflaking_toSnowflaking (x : X) :
    (toSnowflaking x : Snowflaking X α hα₀ hα₁).ofSnowflaking = x :=
  rfl

@[simp]
/-
**Metric.Snowflaking.ofSnowflaking_comp_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 
`Metric.Snowflaking`。
形式化陈述：ofSnowflaking_comp_toSnowflaking : (ofSnowflaking : Snowflaking X α hα₀ hα
₁ -> X) ∘ toSnowflaking = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSnowflaking_comp_toSnowflaking :
    (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) ∘ toSnowflaking = id :=
  rfl

@[simp]
/-
**Metric.Snowflaking.toSnowflaking_comp_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 
`Metric.Snowflaking`。
形式化陈述：toSnowflaking_comp_ofSnowflaking : (toSnowflaking : X -> Snowflaking X α h
α₀ hα₁) ∘ ofSnowflaking = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSnowflaking_comp_ofSnowflaking :
    (toSnowflaking : X → Snowflaking X α hα₀ hα₁) ∘ ofSnowflaking = id :=
  rfl
/-
**Metric.Snowflaking.image_toSnowflaking_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.Snowflaking`。
形式化陈述：image_toSnowflaking_eq_preimage (s : Set X) : (toSnowflaking '' s : Set (S
nowflaking X α hα₀ hα₁)) = ofSnowflaking ⁻¹' s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_toSnowflaking_eq_preimage (s : Set X) :
    (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = ofSnowflaking ⁻¹' s :=
  toSnowflaking.image_eq_preimage_symm _
/-
**Metric.Snowflaking.image_ofSnowflaking_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.Snowflaking`。
形式化陈述：image_ofSnowflaking_eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSn
owflaking '' s = toSnowflaking ⁻¹' s
参数：s : Set (Snowflaking X α hα₀ hα₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_ofSnowflaking_eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) :
    ofSnowflaking '' s = toSnowflaking ⁻¹' s :=
  ofSnowflaking.image_eq_preimage_symm _

@[simp]
/-
**Metric.Snowflaking.image_toSnowflaking_image_ofSnowflaking** 是 Mathlib 中的一个定理，
位于命名空间 `Metric.Snowflaking`。
形式化陈述：image_toSnowflaking_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)
) : toSnowflaking '' ofSnowflaking '' s = s
参数：s : Set (Snowflaking X α hα₀ hα₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem image_toSnowflaking_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    toSnowflaking '' ofSnowflaking '' s = s :=
  ofSnowflaking.symm_image_image _

@[simp]
/-
**Metric.Snowflaking.image_ofSnowflaking_image_toSnowflaking** 是 Mathlib 中的一个定理，
位于命名空间 `Metric.Snowflaking`。
形式化陈述：image_ofSnowflaking_image_toSnowflaking (s : Set X) : ofSnowflaking '' (to
Snowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
-/
theorem image_ofSnowflaking_image_toSnowflaking (s : Set X) :
    ofSnowflaking '' (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = s :=
  ofSnowflaking.image_symm_image _

/-!
### Topological space structure

The topology on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section TopologicalSpace

variable [TopologicalSpace X]

/-- The topological space structure on `Snowflaking X α _ _` is induced from the original space. -/
/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological space structure on `Snowflaking X α _ _` is induced from the ori
ginal space.
-/
instance : TopologicalSpace (Snowflaking X α hα₀ hα₁) := .induced Snowflaking.ofSnowflaking ‹_›

@[fun_prop]
/-
**Metric.Snowflaking.continuous_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric.
Snowflaking`。
形式化陈述：continuous_ofSnowflaking : Continuous (ofSnowflaking : Snowflaking X α hα₀
 hα₁ -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_ofSnowflaking : Continuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) :=
  continuous_induced_dom

@[fun_prop]
/-
**Metric.Snowflaking.continuous_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric.
Snowflaking`。
形式化陈述：continuous_toSnowflaking : Continuous (toSnowflaking : X -> Snowflaking X 
α hα₀ hα₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_toSnowflaking : Continuous (toSnowflaking : X → Snowflaking X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id

/-- The natural homeomorphism between `Snowflaking X α hα₀ hα₁` and `X`. -/
@[simps! -fullyApplied toEquiv apply symm_apply]
/-
**Metric.Snowflaking.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Snowflaking`。
形式化陈述：homeomorph : Snowflaking X α hα₀ hα₁ ≃ₜ X where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.Snowflaking.continuous_toSnowflaking`：continuous_toSnowflaking : 
Continuous (toSnowflaking : X -> Snowflaking X α hα₀ hα₁)

--- 原说明 ---
The natural homeomorphism between `Snowflaking X α hα₀ hα₁` and `X`.
-/
def homeomorph : Snowflaking X α hα₀ hα₁ ≃ₜ X where
  toEquiv := ofSnowflaking
  continuous_invFun := continuous_toSnowflaking

/-!
We copy some instances from the underlying space `X` to `Snowflaking X α hα₀ hα₁`.
In the future, we can add more of them, if needed,
or even copy all the topology-related classes, if we get a tactic to do it automatically.
-/

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We copy some instances from the underlying space `X` to `Snowflaking X α hα₀ hα₁
`.
In the future, we can add more of them, if needed,
or even copy all the topology-related classes, if we get a tactic to do it autom
atically.
-/
instance [T0Space X] : T0Space (Snowflaking X α hα₀ hα₁) :=
  homeomorph.symm.t0Space
/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space X] : T2Space (Snowflaking X α hα₀ hα₁) :=
  homeomorph.symm.t2Space
/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SecondCountableTopology X] : SecondCountableTopology (Snowflaking X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology

end TopologicalSpace

/-!
### Bornology

The bornology on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section Bornology

variable [Bornology X]

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bornology (Snowflaking X α hα₀ hα₁) := .induced ofSnowflaking

open Bornology

@[simp]
/-
**Metric.Snowflaking.isBounded_image_ofSnowflaking_iff** 是 Mathlib 中的一个定理，位于命名空间
 `Metric.Snowflaking`。
形式化陈述：isBounded_image_ofSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} : Is
Bounded (ofSnowflaking '' s) ↔ IsBounded s
参数：Snowflaking X α hα₀ hα₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Bornology.isBounded_induced`：isBounded_induced {α β : Type*} [Bornology 
β] {f : α -> β} {s : Set α} : @IsBounded α (Bornology.induced f) s ↔ IsBounded (
f '' s)
-/
theorem isBounded_image_ofSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
    IsBounded (ofSnowflaking '' s) ↔ IsBounded s :=
  isBounded_induced.symm

@[simp]
/-
**Metric.Snowflaking.isBounded_preimage_toSnowflaking_iff** 是 Mathlib 中的一个定理，位于命
名空间 `Metric.Snowflaking`。
形式化陈述：isBounded_preimage_toSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
 IsBounded (toSnowflaking ⁻¹' s) ↔ IsBounded s
参数：Snowflaking X α hα₀ hα₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_eq_preimage`：image_ofSnowflaking_
eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSnowflaking '' s = toSnowfla
king ⁻¹' s
· 使用定理 `Metric.Snowflaking.isBounded_image_ofSnowflaking_iff`：isBounded_image_of
Snowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} : IsBounded (ofSnowflaking '
' s) ↔ IsBounded s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_preimage_toSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
    IsBounded (toSnowflaking ⁻¹' s) ↔ IsBounded s := by
  rw [← image_ofSnowflaking_eq_preimage, isBounded_image_ofSnowflaking_iff]

@[simp]
/-
**Metric.Snowflaking.isBounded_image_toSnowflaking_iff** 是 Mathlib 中的一个定理，位于命名空间
 `Metric.Snowflaking`。
形式化陈述：isBounded_image_toSnowflaking_iff {s : Set X} : IsBounded (toSnowflaking '
' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.Snowflaking.isBounded_image_ofSnowflaking_iff`：isBounded_image_of
Snowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} : IsBounded (ofSnowflaking '
' s) ↔ IsBounded s
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_image_toSnowflaking`：image_ofSnow
flaking_image_toSnowflaking (s : Set X) : ofSnowflaking '' (toSnowflaking '' s :
 Set (Snowflaking X α hα₀ hα₁)) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_image_toSnowflaking_iff {s : Set X} :
    IsBounded (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_ofSnowflaking_iff, image_ofSnowflaking_image_toSnowflaking]

@[simp]
/-
**Metric.Snowflaking.isBounded_preimage_ofSnowflaking_iff** 是 Mathlib 中的一个定理，位于命
名空间 `Metric.Snowflaking`。
形式化陈述：isBounded_preimage_ofSnowflaking_iff {s : Set X} : IsBounded (ofSnowflakin
g ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eq_preimage`：image_toSnowflaking_
eq_preimage (s : Set X) : (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) =
 ofSnowflaking ⁻¹' s
· 使用定理 `Metric.Snowflaking.isBounded_image_toSnowflaking_iff`：isBounded_image_to
Snowflaking_iff {s : Set X} : IsBounded (toSnowflaking '' s : Set (Snowflaking X
 α hα₀ hα₁)) ↔ IsBounded s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_preimage_ofSnowflaking_iff {s : Set X} :
    IsBounded (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_toSnowflaking_eq_preimage, isBounded_image_toSnowflaking_iff]

end Bornology

/-!
### Uniform space structure

The uniform space structure on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section UniformSpace

variable [UniformSpace X]

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace (Snowflaking X α hα₀ hα₁) :=
  UniformSpace.comap Snowflaking.ofSnowflaking ‹_›
/-
**Metric.Snowflaking.uniformContinuous_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.Snowflaking`。
形式化陈述：uniformContinuous_ofSnowflaking : UniformContinuous (ofSnowflaking : Snowf
laking X α hα₀ hα₁ -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
-/
theorem uniformContinuous_ofSnowflaking :
    UniformContinuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) :=
  uniformContinuous_comap
/-
**Metric.Snowflaking.uniformContinuous_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.Snowflaking`。
形式化陈述：uniformContinuous_toSnowflaking : UniformContinuous (toSnowflaking : X -> 
Snowflaking X α hα₀ hα₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap'`：uniformContinuous_comap' {f : γ -> β} {g : α -
> γ} [v : UniformSpace β] [u : UniformSpace α] (h : UniformContinuous (f ∘ g)) :
 @UniformConti…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_toSnowflaking :
    UniformContinuous (toSnowflaking : X → Snowflaking X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id

/-- The natural uniform space equivalence between `Snowflaking X α hα hα₁`
and the underlying space. -/
@[simps! toEquiv apply symm_apply]
/-
**Metric.Snowflaking.uniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Snowflaking`
。
形式化陈述：uniformEquiv : Snowflaking X α hα₀ hα₁ ≃ᵤ X where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.Snowflaking.uniformContinuous_ofSnowflaking`：uniformContinuous_of
Snowflaking : UniformContinuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X)
· 使用定理 `Metric.Snowflaking.uniformContinuous_toSnowflaking`：uniformContinuous_to
Snowflaking : UniformContinuous (toSnowflaking : X -> Snowflaking X α hα₀ hα₁)

--- 原说明 ---
The natural uniform space equivalence between `Snowflaking X α hα hα₁`
and the underlying space.
-/
def uniformEquiv : Snowflaking X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := ofSnowflaking
  uniformContinuous_toFun := uniformContinuous_ofSnowflaking
  uniformContinuous_invFun := uniformContinuous_toSnowflaking

end UniformSpace

/-!
### Extended distance and a (pseudo) extended metric space structure

Th extended distance on `Snowflaking X α hα₀ hα₁`
is given by `edist x y = (edist x.ofSnowflaking y.ofSnowflaking) ^ α`.

If the original space is a (pseudo) extended metric space, then so is `Snowflaking X α hα₀ hα₁`.
-/

section EDist

variable [EDist X]

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EDist (Snowflaking X α hα₀ hα₁) where
  edist x y := edist x.ofSnowflaking y.ofSnowflaking ^ α
/-
**Metric.Snowflaking.edist_def** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Snowflaking`。
形式化陈述：edist_def (x y : Snowflaking X α hα₀ hα₁) : edist x y = edist x.ofSnowflak
ing y.ofSnowflaking ^ α
参数：x y : Snowflaking X α hα₀ hα₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_def (x y : Snowflaking X α hα₀ hα₁) :
    edist x y = edist x.ofSnowflaking y.ofSnowflaking ^ α :=
  rfl

@[simp]
/-
**Metric.Snowflaking.edist_toSnowflaking_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间
 `Metric.Snowflaking`。
形式化陈述：edist_toSnowflaking_toSnowflaking (x y : X) : edist (toSnowflaking x : Sno
wflaking X α hα₀ hα₁) (toSnowflaking y) = edist x y ^ α
参数：x y : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_toSnowflaking_toSnowflaking (x y : X) :
    edist (toSnowflaking x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = edist x y ^ α :=
  rfl

@[simp]
/-
**Metric.Snowflaking.edist_ofSnowflaking_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间
 `Metric.Snowflaking`。
形式化陈述：edist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) : edist 
x.ofSnowflaking y.ofSnowflaking = edist x y ^ α⁻¹
参数：x y : Snowflaking X α hα₀ hα₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.edist_def`：edist_def (x y : Snowflaking X α hα₀ hα₁) 
: edist x y = edist x.ofSnowflaking y.ofSnowflaking ^ α
· 使用定理 `ENNReal.rpow_rpow_inv`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y) ^ y⁻¹
 = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem edist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) :
    edist x.ofSnowflaking y.ofSnowflaking = edist x y ^ α⁻¹ := by
  rw [edist_def, ENNReal.rpow_rpow_inv hα₀.ne']

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoEMetricSpace (Snowflaking X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.ofSnowflaking y.ofSnowflaking z.ofSnowflaking,
      ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ ↦ by positivity) fun ε hε ↦
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]
/-
**Metric.Snowflaking.preimage_ofSnowflaking_eball** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric.Snowflaking`。
形式化陈述：preimage_ofSnowflaking_eball (x : X) (r : Real>=0∞) : ofSnowflaking ⁻¹' Me
tric.eball x r = Metric.eball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α
)
参数：x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_ofSnowflaking_eball (x : X) (r : ℝ≥0∞) :
    ofSnowflaking ⁻¹' Metric.eball x r =
      Metric.eball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricBall := preimage_ofSnowflaking_eball

@[simp]
/-
**Metric.Snowflaking.image_toSnowflaking_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric
.Snowflaking`。
形式化陈述：image_toSnowflaking_eball (x : X) (r : Real>=0∞) : toSnowflaking '' Metric
.eball x r = Metric.eball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α)
参数：x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eq_preimage`：image_toSnowflaking_
eq_preimage (s : Set X) : (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) =
 ofSnowflaking ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_ofSnowflaking_eball`：preimage_ofSnowflaking_
eball (x : X) (r : Real>=0∞) : ofSnowflaking ⁻¹' Metric.eball x r = Metric.eball
 (toSnowflaking x : Snowflaking X α h…
-/
theorem image_toSnowflaking_eball (x : X) (r : ℝ≥0∞) :
    toSnowflaking '' Metric.eball x r =
      Metric.eball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricBall := image_toSnowflaking_eball

@[simp]
/-
**Metric.Snowflaking.preimage_toSnowflaking_eball** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric.Snowflaking`。
形式化陈述：preimage_toSnowflaking_eball (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) 
: toSnowflaking ⁻¹' Metric.eball x d = Metric.eball x.ofSnowflaking (d ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；d : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eball`：image_toSnowflaking_eball 
(x : X) (r : Real>=0∞) : toSnowflaking '' Metric.eball x r = Metric.eball (toSno
wflaking x : Snowflaking X α hα₀ h…
· 使用定理 `Metric.Snowflaking.toSnowflaking_ofSnowflaking`：toSnowflaking_ofSnowflak
ing (x : Snowflaking X α hα₀ hα₁) : toSnowflaking x.ofSnowflaking = x
· 使用定理 `ENNReal.rpow_inv_rpow`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y⁻¹) ^ y
 = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem preimage_toSnowflaking_eball (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    toSnowflaking ⁻¹' Metric.eball x d = Metric.eball x.ofSnowflaking (d ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_eball,
    toSnowflaking_ofSnowflaking, ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricBall := preimage_toSnowflaking_eball

@[simp]
/-
**Metric.Snowflaking.image_ofSnowflaking_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric
.Snowflaking`。
形式化陈述：image_ofSnowflaking_eball (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) : o
fSnowflaking '' Metric.eball x d = Metric.eball x.ofSnowflaking (d ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；d : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_eq_preimage`：image_ofSnowflaking_
eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSnowflaking '' s = toSnowfla
king ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_toSnowflaking_eball`：preimage_toSnowflaking_
eball (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) : toSnowflaking ⁻¹' Metric.eb
all x d = Metric.eball x.ofSnowflakin…
-/
theorem image_ofSnowflaking_eball (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    ofSnowflaking '' Metric.eball x d = Metric.eball x.ofSnowflaking (d ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_eball]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricBall := image_ofSnowflaking_eball

@[simp]
/-
**Metric.Snowflaking.preimage_ofSnowflaking_closedEBall** 是 Mathlib 中的一个定理，位于命名空
间 `Metric.Snowflaking`。
形式化陈述：preimage_ofSnowflaking_closedEBall (x : X) (r : Real>=0∞) : ofSnowflaking 
⁻¹' Metric.closedEBall x r = Metric.closedEBall (toSnowflaking x : Snowflaking X
 α hα₀ hα₁) (r ^ α)
参数：x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_ofSnowflaking_closedEBall (x : X) (r : ℝ≥0∞) :
    ofSnowflaking ⁻¹' Metric.closedEBall x r =
      Metric.closedEBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[deprecated (since := "2026-01-24")]
alias preimage_ofSnowflaking_emetricClosedBall := preimage_ofSnowflaking_closedEBall

@[simp]
/-
**Metric.Snowflaking.image_toSnowflaking_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.Snowflaking`。
形式化陈述：image_toSnowflaking_closedEBall (x : X) (r : Real>=0∞) : toSnowflaking '' 
Metric.closedEBall x r = Metric.closedEBall (toSnowflaking x : Snowflaking X α h
α₀ hα₁) (r ^ α)
参数：x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eq_preimage`：image_toSnowflaking_
eq_preimage (s : Set X) : (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) =
 ofSnowflaking ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_ofSnowflaking_closedEBall`：preimage_ofSnowfl
aking_closedEBall (x : X) (r : Real>=0∞) : ofSnowflaking ⁻¹' Metric.closedEBall 
x r = Metric.closedEBall (toSnowflaking x :…
-/
theorem image_toSnowflaking_closedEBall (x : X) (r : ℝ≥0∞) :
    toSnowflaking '' Metric.closedEBall x r =
      Metric.closedEBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_toSnowflaking_emetricClosedBall := image_toSnowflaking_closedEBall

@[simp]
/-
**Metric.Snowflaking.preimage_toSnowflaking_closedEBall** 是 Mathlib 中的一个定理，位于命名空
间 `Metric.Snowflaking`。
形式化陈述：preimage_toSnowflaking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : Real
>=0∞) : toSnowflaking ⁻¹' Metric.closedEBall x d = Metric.closedEBall x.ofSnowfl
aking (d ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；d : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_closedEBall`：image_toSnowflaking_
closedEBall (x : X) (r : Real>=0∞) : toSnowflaking '' Metric.closedEBall x r = M
etric.closedEBall (toSnowflaking x : Sno…
· 使用定理 `Metric.Snowflaking.toSnowflaking_ofSnowflaking`：toSnowflaking_ofSnowflak
ing (x : Snowflaking X α hα₀ hα₁) : toSnowflaking x.ofSnowflaking = x
· 使用定理 `ENNReal.rpow_inv_rpow`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y⁻¹) ^ y
 = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem preimage_toSnowflaking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    toSnowflaking ⁻¹' Metric.closedEBall x d = Metric.closedEBall x.ofSnowflaking (d ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_closedEBall,
    toSnowflaking_ofSnowflaking, ENNReal.rpow_inv_rpow hα₀.ne']

@[deprecated (since := "2026-01-24")]
alias preimage_toSnowflaking_emetricClosedBall := preimage_toSnowflaking_closedEBall

@[simp]
/-
**Metric.Snowflaking.image_ofSnowflaking_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.Snowflaking`。
形式化陈述：image_ofSnowflaking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : Real>=0
∞) : ofSnowflaking '' Metric.closedEBall x d = Metric.closedEBall x.ofSnowflakin
g (d ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；d : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_eq_preimage`：image_ofSnowflaking_
eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSnowflaking '' s = toSnowfla
king ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_toSnowflaking_closedEBall`：preimage_toSnowfl
aking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : Real>=0∞) : toSnowflaking ⁻
¹' Metric.closedEBall x d = Metric.closedEB…
-/
theorem image_ofSnowflaking_closedEBall (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    ofSnowflaking '' Metric.closedEBall x d =
      Metric.closedEBall x.ofSnowflaking (d ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_closedEBall]

@[deprecated (since := "2026-01-24")]
alias image_ofSnowflaking_emetricClosedBall := image_ofSnowflaking_closedEBall

@[simp]
/-
**Metric.Snowflaking.ediam_image_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric
.Snowflaking`。
形式化陈述：ediam_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) : ediam (ofS
nowflaking '' s) = ediam s ^ α⁻¹
参数：s : Set (Snowflaking X α hα₀ hα₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.Snowflaking.edist_ofSnowflaking_ofSnowflaking`：edist_ofSnowflakin
g_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) : edist x.ofSnowflaking y.ofSnow
flaking = edist x y ^ α⁻¹
· 使用定理 `ENNReal.rpow_inv_le_iff`：rpow_inv_le_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ediam_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    ediam (ofSnowflaking '' s) = ediam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [ENNReal.rpow_inv_le_iff hα₀, ediam_le_iff, Set.forall_mem_image,
    edist_ofSnowflaking_ofSnowflaking]

@[simp]
/-
**Metric.Snowflaking.ediam_preimage_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric.Snowflaking`。
形式化陈述：ediam_preimage_toSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) : ediam (
toSnowflaking ⁻¹' s) = ediam s ^ α⁻¹
参数：s : Set (Snowflaking X α hα₀ hα₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_eq_preimage`：image_ofSnowflaking_
eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSnowflaking '' s = toSnowfla
king ⁻¹' s
· 使用定理 `Metric.Snowflaking.ediam_image_ofSnowflaking`：ediam_image_ofSnowflaking 
(s : Set (Snowflaking X α hα₀ hα₁)) : ediam (ofSnowflaking '' s) = ediam s ^ α⁻¹
-/
theorem ediam_preimage_toSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    ediam (toSnowflaking ⁻¹' s) = ediam s ^ α⁻¹ := by
  rw [← image_ofSnowflaking_eq_preimage, ediam_image_ofSnowflaking]

@[simp]
/-
**Metric.Snowflaking.ediam_preimage_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric.Snowflaking`。
形式化陈述：ediam_preimage_ofSnowflaking (s : Set X) : ediam (ofSnowflaking ⁻¹' s : Se
t (Snowflaking X α hα₀ hα₁)) = ediam s ^ α
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_inv_rpow`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y⁻¹) ^ y
 = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Metric.Snowflaking.ediam_preimage_toSnowflaking`：ediam_preimage_toSnowfl
aking (s : Set (Snowflaking X α hα₀ hα₁)) : ediam (toSnowflaking ⁻¹' s) = ediam 
s ^ α⁻¹
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Metric.Snowflaking.ofSnowflaking_comp_toSnowflaking`：ofSnowflaking_comp_
toSnowflaking : (ofSnowflaking : Snowflaking X α hα₀ hα₁ -> X) ∘ toSnowflaking =
 id
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
theorem ediam_preimage_ofSnowflaking (s : Set X) :
    ediam (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) = ediam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _), ← ediam_preimage_toSnowflaking,
    ← Set.preimage_comp, ofSnowflaking_comp_toSnowflaking, Set.preimage_id]

@[simp]
/-
**Metric.Snowflaking.ediam_image_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 `Metric
.Snowflaking`。
形式化陈述：ediam_image_toSnowflaking (s : Set X) : ediam (toSnowflaking '' s : Set (S
nowflaking X α hα₀ hα₁)) = ediam s ^ α
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eq_preimage`：image_toSnowflaking_
eq_preimage (s : Set X) : (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) =
 ofSnowflaking ⁻¹' s
· 使用定理 `Metric.Snowflaking.ediam_preimage_ofSnowflaking`：ediam_preimage_ofSnowfl
aking (s : Set X) : ediam (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) 
= ediam s ^ α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ediam_image_toSnowflaking (s : Set X) :
    ediam (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = ediam s ^ α := by
  simp [image_toSnowflaking_eq_preimage]

end PseudoEMetricSpace

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EMetricSpace X] : EMetricSpace (Snowflaking X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _

/-!
### Distance and a (pseudo) metric space structure

Th extended distance on `Snowflaking X α hα₀ hα₁`
is given by `dist x y = (dist x.ofSnowflaking y.ofSnowflaking) ^ α`.

If the original space is a (pseudo) metric space, then so is `Snowflaking X α hα₀ hα₁`.
-/

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Distance and a (pseudo) metric space structure

Th extended distance on `Snowflaking X α hα₀ hα₁`
is given by `dist x y = (dist x.ofSnowflaking y.ofSnowflaking) ^ α`.

If the original space is a (pseudo) metric space, then so is `Snowflaking X α hα
₀ hα₁`.
-/
instance [Dist X] : Dist (Snowflaking X α hα₀ hα₁) where
  dist x y := dist x.ofSnowflaking y.ofSnowflaking ^ α

@[simp]
/-
**Metric.Snowflaking.dist_toSnowflaking_toSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 
`Metric.Snowflaking`。
形式化陈述：dist_toSnowflaking_toSnowflaking [Dist X] (x y : X) : dist (toSnowflaking 
x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = dist x y ^ α
参数：x y : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_toSnowflaking_toSnowflaking [Dist X] (x y : X) :
    dist (toSnowflaking x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = dist x y ^ α :=
  rfl

section PseudoMetricSpace

variable [PseudoMetricSpace X]

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by intro x y; cases x; cases y; rw [dist_toSnowflaking_toSnowflaking]; positivity)
      (by
        intro x y; cases x; cases y
        rw [edist_toSnowflaking_toSnowflaking, dist_toSnowflaking_toSnowflaking,
          ← ENNReal.ofReal_rpow_of_nonneg, ← edist_dist] <;> positivity)
  aux.replaceBornology fun s ↦ by
    rw [← isBounded_preimage_toSnowflaking_iff, Metric.isBounded_iff, Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [mk_eq_toSnowflaking, dist_toSnowflaking_toSnowflaking, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_toSnowflaking_toSnowflaking, Real.rpow_rpow_inv (by positivity) hα₀.ne']

open Metric

@[simp]
/-
**Metric.Snowflaking.dist_ofSnowflaking_ofSnowflaking** 是 Mathlib 中的一个定理，位于命名空间 
`Metric.Snowflaking`。
形式化陈述：dist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) : dist x.
ofSnowflaking y.ofSnowflaking = dist x y ^ α⁻¹
参数：x y : Snowflaking X α hα₀ hα₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_rpow_inv`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y) ^ y⁻¹ = x
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) :
    dist x.ofSnowflaking y.ofSnowflaking = dist x y ^ α⁻¹ := by
  cases x; cases y
  simp [Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]
/-
**Metric.Snowflaking.preimage_ofSnowflaking_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic.Snowflaking`。
形式化陈述：preimage_ofSnowflaking_ball (x : X) {r : Real} (hr : 0 <= r) : ofSnowflaki
ng ⁻¹' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α)
参数：x : X；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_ofSnowflaking_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking ⁻¹' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]
/-
**Metric.Snowflaking.image_toSnowflaking_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric.
Snowflaking`。
形式化陈述：image_toSnowflaking_ball (x : X) {r : Real} (hr : 0 <= r) : toSnowflaking 
'' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α)
参数：x : X；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eq_preimage`：image_toSnowflaking_
eq_preimage (s : Set X) : (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) =
 ofSnowflaking ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_ofSnowflaking_ball`：preimage_ofSnowflaking_b
all (x : X) {r : Real} (hr : 0 <= r) : ofSnowflaking ⁻¹' ball x r = ball (toSnow
flaking x : Snowflaking X α hα₀ hα₁)…
-/
theorem image_toSnowflaking_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking '' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_ball x hr]

@[simp]
/-
**Metric.Snowflaking.preimage_toSnowflaking_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic.Snowflaking`。
形式化陈述：preimage_toSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr :
 0 <= r) : toSnowflaking ⁻¹' ball x r = ball x.ofSnowflaking (r ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_ball`：image_toSnowflaking_ball (x
 : X) {r : Real} (hr : 0 <= r) : toSnowflaking '' ball x r = ball (toSnowflaking
 x : Snowflaking X α hα₀ hα₁) (r …
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Metric.Snowflaking.toSnowflaking_ofSnowflaking`：toSnowflaking_ofSnowflak
ing (x : Snowflaking X α hα₀ hα₁) : toSnowflaking x.ofSnowflaking = x
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem preimage_toSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking ⁻¹' ball x r = ball x.ofSnowflaking (r ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_ball _ (by positivity),
    toSnowflaking_ofSnowflaking, Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
/-
**Metric.Snowflaking.image_ofSnowflaking_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric.
Snowflaking`。
形式化陈述：image_ofSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 
<= r) : ofSnowflaking '' ball x r = ball x.ofSnowflaking (r ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_eq_preimage`：image_ofSnowflaking_
eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSnowflaking '' s = toSnowfla
king ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_toSnowflaking_ball`：preimage_toSnowflaking_b
all (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r) : toSnowflaking ⁻¹' b
all x r = ball x.ofSnowflaking (r ^ …
-/
theorem image_ofSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking '' ball x r = ball x.ofSnowflaking (r ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_ball _ hr]

@[simp]
/-
**Metric.Snowflaking.preimage_ofSnowflaking_closedBall** 是 Mathlib 中的一个定理，位于命名空间
 `Metric.Snowflaking`。
形式化陈述：preimage_ofSnowflaking_closedBall (x : X) {r : Real} (hr : 0 <= r) : ofSno
wflaking ⁻¹' closedBall x r = closedBall (toSnowflaking x : Snowflaking X α hα₀ 
hα₁) (r ^ α)
参数：x : X；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_ofSnowflaking_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking ⁻¹' closedBall x r =
      closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]
/-
**Metric.Snowflaking.image_toSnowflaking_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `M
etric.Snowflaking`。
形式化陈述：image_toSnowflaking_closedBall (x : X) {r : Real} (hr : 0 <= r) : toSnowfl
aking '' closedBall x r = closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁)
 (r ^ α)
参数：x : X；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_eq_preimage`：image_toSnowflaking_
eq_preimage (s : Set X) : (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) =
 ofSnowflaking ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_ofSnowflaking_closedBall`：preimage_ofSnowfla
king_closedBall (x : X) {r : Real} (hr : 0 <= r) : ofSnowflaking ⁻¹' closedBall 
x r = closedBall (toSnowflaking x : Snowfl…
-/
theorem image_toSnowflaking_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking '' closedBall x r =
      closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_closedBall x hr]

@[simp]
/-
**Metric.Snowflaking.preimage_toSnowflaking_closedBall** 是 Mathlib 中的一个定理，位于命名空间
 `Metric.Snowflaking`。
形式化陈述：preimage_toSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : Real}
 (hr : 0 <= r) : toSnowflaking ⁻¹' closedBall x r = closedBall x.ofSnowflaking (
r ^ α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用定理 `Metric.Snowflaking.image_toSnowflaking_closedBall`：image_toSnowflaking_c
losedBall (x : X) {r : Real} (hr : 0 <= r) : toSnowflaking '' closedBall x r = c
losedBall (toSnowflaking x : Snowflakin…
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Metric.Snowflaking.toSnowflaking_ofSnowflaking`：toSnowflaking_ofSnowflak
ing (x : Snowflaking X α hα₀ hα₁) : toSnowflaking x.ofSnowflaking = x
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem preimage_toSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking ⁻¹' closedBall x r = closedBall x.ofSnowflaking (r ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_closedBall _ (by positivity),
    toSnowflaking_ofSnowflaking, Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
/-
**Metric.Snowflaking.image_ofSnowflaking_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `M
etric.Snowflaking`。
形式化陈述：image_ofSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : Real} (h
r : 0 <= r) : ofSnowflaking '' closedBall x r = closedBall x.ofSnowflaking (r ^ 
α⁻¹)
参数：x : Snowflaking X α hα₀ hα₁；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Snowflaking.image_ofSnowflaking_eq_preimage`：image_ofSnowflaking_
eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) : ofSnowflaking '' s = toSnowfla
king ⁻¹' s
· 使用定理 `Metric.Snowflaking.preimage_toSnowflaking_closedBall`：preimage_toSnowfla
king_closedBall (x : Snowflaking X α hα₀ hα₁) {r : Real} (hr : 0 <= r) : toSnowf
laking ⁻¹' closedBall x r = closedBall x.o…
-/
theorem image_ofSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking '' closedBall x r = closedBall x.ofSnowflaking (r ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_closedBall _ hr]

end PseudoMetricSpace

/-
**Metric.Snowflaking.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.Snowflaking`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MetricSpace X] : MetricSpace (Snowflaking X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _

end Snowflaking
end Metric

