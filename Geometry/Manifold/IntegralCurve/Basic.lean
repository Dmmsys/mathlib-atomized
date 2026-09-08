/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.Notation

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

This is the first of a series of files, organised as follows:
* `Mathlib/Geometry/Manifold/IntegralCurve/Basic.lean` (this file): Basic definitions and lemmas
  relating them to each other and to continuity and differentiability
* `Mathlib/Geometry/Manifold/IntegralCurve/Transform.lean`: Lemmas about translating or scaling the
  domain of an integral curve by a constant
* `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`: Local existence and uniqueness
  theorems for integral curves

## Main definitions

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
* `IsMIntegralCurve γ v`: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsMIntegralCurveOn γ v s`: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsMIntegralCurveAt γ v t₀`: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsMIntegralCurveOn γ v s` and `IsMIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## TODO

* Implement `IsMIntegralCurveWithinAt`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If `γ : ℝ → M` is $C^1$ on `s : Set ℝ` and `v` is a vector field on `M`,
`IsMIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` for all `t ∈ s`. The value of `γ`
outside of `s` is irrelevant and considered junk. -/
/-
**IsMIntegralCurveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn (γ : Real -> M) (v : (x : M) -> TangentSpace% x) (s : S
et Real) : Prop
参数：γ : Real -> M；v : (x : M) -> TangentSpace% x；s : Set Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `γ : ℝ → M` is $C^1$ on `s : Set ℝ` and `v` is a vector field on `M`,
`IsMIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` for all `t ∈ s`. 
The value of `γ`
outside of `s` is irrelevant and considered junk.
-/
def IsMIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt[s] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v` is a vector field on `M` and `t₀ : ℝ`, `IsMIntegralCurveAt γ v t₀` means `γ : ℝ → M` is a
local integral curve of `v` in a neighbourhood containing `t₀`. The value of `γ` outside of this
interval is irrelevant and considered junk. -/
/-
**IsMIntegralCurveAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt (γ : Real -> M) (v : (x : M) -> TangentSpace% x) (t₀ : 
Real) : Prop
参数：γ : Real -> M；v : (x : M) -> TangentSpace% x；t₀ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `v` is a vector field on `M` and `t₀ : ℝ`, `IsMIntegralCurveAt γ v t₀` means 
`γ : ℝ → M` is a
local integral curve of `v` in a neighbourhood containing `t₀`. The value of `γ`
 outside of this
interval is irrelevant and considered junk.
-/
def IsMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v : M → TM` is a vector field on `M`, `IsMIntegralCurve γ v` means `γ : ℝ → M` is a global
integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
/-
**IsMIntegralCurve** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMIntegralCurve (γ : Real -> M) (v : (x : M) -> TangentSpace% x) : Prop
参数：γ : Real -> M；v : (x : M) -> TangentSpace% x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `v : M → TM` is a vector field on `M`, `IsMIntegralCurve γ v` means `γ : ℝ → 
M` is a global
integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`.
-/
def IsMIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace% x) : Prop :=
  ∀ t : ℝ, HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

variable {γ γ' : ℝ → M} {v : (x : M) → TangentSpace% x} {s s' : Set ℝ} {t₀ : ℝ}
/-
**IsMIntegralCurve.isMIntegralCurveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.isMIntegralCurveOn (h : IsMIntegralCurve γ v) (s : Set Re
al) : IsMIntegralCurveOn γ v s
参数：h : IsMIntegralCurve γ v；s : Set Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
lemma IsMIntegralCurve.isMIntegralCurveOn (h : IsMIntegralCurve γ v) (s : Set ℝ) :
    IsMIntegralCurveOn γ v s := fun t _ ↦ (h t).hasMFDerivWithinAt
/-
**isMIntegralCurve_iff_isMIntegralCurveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_iff_isMIntegralCurveOn : IsMIntegralCurve γ v ↔ IsMIntegr
alCurveOn γ v univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMIntegralCurve.isMIntegralCurveOn`：IsMIntegralCurve.isMIntegralCurveOn
 (h : IsMIntegralCurve γ v) (s : Set Real) : IsMIntegralCurveOn γ v s
· 使用定理 `HasMFDerivWithinAt.hasMFDerivAt`：HasMFDerivWithinAt.hasMFDerivAt (h : Ha
sMFDerivAt[s] f x f') (hs : s in 𝓝 x) : HasMFDerivAt% f x f'
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
lemma isMIntegralCurve_iff_isMIntegralCurveOn :
    IsMIntegralCurve γ v ↔ IsMIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isMIntegralCurveOn _, fun h t ↦ (h t (mem_univ _)).hasMFDerivAt Filter.univ_mem⟩
/-
**isMIntegralCurveAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsM
IntegralCurveOn γ v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `IsMIntegralCurveAt.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {H : Type u_2} [inst_2 : TopologicalSpace H]   {I : M
odelWithCorne…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `HasMFDerivWithinAt.hasMFDerivAt`：HasMFDerivWithinAt.hasMFDerivAt (h : Ha
sMFDerivAt[s] f x f') (hs : s in 𝓝 x) : HasMFDerivAt% f x f'
-/
lemma isMIntegralCurveAt_iff :
    IsMIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsMIntegralCurveOn γ v s := by
  constructor
  · intro h
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    exact ⟨s, hs, fun t ht ↦ (h t ht).hasMFDerivWithinAt⟩
  · rintro ⟨s, hs, h⟩
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem]
    obtain ⟨s', h1, h2, h3⟩ := mem_nhds_iff.mp hs
    refine ⟨s', h2.mem_nhds h3, ?_⟩
    intro t ht
    apply (h t (h1 ht)).hasMFDerivAt
    rw [mem_nhds_iff]
    exact ⟨s', h1, h2, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
/-
**isMIntegralCurveAt_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_iff' : IsMIntegralCurveAt γ v t₀ ↔ exists ε > 0, IsMInt
egralCurveOn γ v (Metric.ball t₀ ε)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x

--- 原说明 ---
`γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some in
terval
containing `t₀`.
-/
lemma isMIntegralCurveAt_iff' :
    IsMIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsMIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [isMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, h⟩
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hε'⟩ := hs
    refine ⟨ε, hε, fun t ht ↦ (h t (hε' ht)).mono hε'⟩
  · intro ⟨ε, hε, h⟩
    exact ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩
/-
**IsMIntegralCurve.isMIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.isMIntegralCurveAt (h : IsMIntegralCurve γ v) (t : Real) 
: IsMIntegralCurveAt γ v t
参数：h : IsMIntegralCurve γ v；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
lemma IsMIntegralCurve.isMIntegralCurveAt (h : IsMIntegralCurve γ v) (t : ℝ) :
    IsMIntegralCurveAt γ v t :=
  isMIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasMFDerivWithinAt⟩
/-
**isMIntegralCurve_iff_isMIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_iff_isMIntegralCurveAt : IsMIntegralCurve γ v ↔ forall t 
: Real, IsMIntegralCurveAt γ v t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMIntegralCurve.isMIntegralCurveAt`：IsMIntegralCurve.isMIntegralCurveAt
 (h : IsMIntegralCurve γ v) (t : Real) : IsMIntegralCurveAt γ v t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
· 使用定理 `HasMFDerivWithinAt.hasMFDerivAt`：HasMFDerivWithinAt.hasMFDerivAt (h : Ha
sMFDerivAt[s] f x f') (hs : s in 𝓝 x) : HasMFDerivAt% f x f'
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma isMIntegralCurve_iff_isMIntegralCurveAt :
    IsMIntegralCurve γ v ↔ ∀ t : ℝ, IsMIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isMIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasMFDerivAt hs⟩
/-
**IsMIntegralCurveOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.mono (h : IsMIntegralCurveOn γ v s) (hs : s' subseteq s
) : IsMIntegralCurveOn γ v s'
参数：h : IsMIntegralCurveOn γ v s；hs : s' subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
-/
lemma IsMIntegralCurveOn.mono (h : IsMIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsMIntegralCurveOn γ v s' := fun t ht ↦ (h t (hs ht)).mono hs
/-
**IsMIntegralCurveAt.hasMFDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt.hasMFDerivAt (h : IsMIntegralCurveAt γ v t₀) : HasMFDer
ivAt% γ t₀ ((1 : Real ->L[Real] Real).smulRight (v (γ t₀)))
参数：h : IsMIntegralCurveAt γ v t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
· 使用定理 `HasMFDerivWithinAt.hasMFDerivAt`：HasMFDerivWithinAt.hasMFDerivAt (h : Ha
sMFDerivAt[s] f x f') (hs : s in 𝓝 x) : HasMFDerivAt% f x f'
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma IsMIntegralCurveAt.hasMFDerivAt (h : IsMIntegralCurveAt γ v t₀) :
    HasMFDerivAt% γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t₀))) :=
  have ⟨_, hs, h⟩ := isMIntegralCurveAt_iff.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasMFDerivAt hs
/-
**IsMIntegralCurveOn.isMIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.isMIntegralCurveAt (h : IsMIntegralCurveOn γ v s) (hs :
 s in 𝓝 t₀) : IsMIntegralCurveAt γ v t₀
参数：h : IsMIntegralCurveOn γ v s；hs : s in 𝓝 t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
-/
lemma IsMIntegralCurveOn.isMIntegralCurveAt (h : IsMIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsMIntegralCurveAt γ v t₀ := isMIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
/-
**IsMIntegralCurveAt.isMIntegralCurveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt.isMIntegralCurveOn (h : forall t in s, IsMIntegralCurve
At γ v t) : IsMIntegralCurveOn γ v s
参数：h : forall t in s, IsMIntegralCurveAt γ v t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`.
-/
lemma IsMIntegralCurveAt.isMIntegralCurveOn (h : ∀ t ∈ s, IsMIntegralCurveAt γ v t) :
    IsMIntegralCurveOn γ v s := by
  intro t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs')
/-
**isMIntegralCurveOn_iff_isMIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveOn_iff_isMIntegralCurveAt (hs : IsOpen s) : IsMIntegralCur
veOn γ v s ↔ forall t in s, IsMIntegralCurveAt γ v t
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsMIntegralCurveOn.isMIntegralCurveAt`：IsMIntegralCurveOn.isMIntegralCur
veAt (h : IsMIntegralCurveOn γ v s) (hs : s in 𝓝 t₀) : IsMIntegralCurveAt γ v t₀
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `IsMIntegralCurveAt.isMIntegralCurveOn`：IsMIntegralCurveAt.isMIntegralCur
veOn (h : forall t in s, IsMIntegralCurveAt γ v t) : IsMIntegralCurveOn γ v s
-/
lemma isMIntegralCurveOn_iff_isMIntegralCurveAt (hs : IsOpen s) :
    IsMIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsMIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isMIntegralCurveAt (hs.mem_nhds ht), IsMIntegralCurveAt.isMIntegralCurveOn⟩
/-
**IsMIntegralCurveOn.continuousWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.continuousWithinAt (hγ : IsMIntegralCurveOn γ v s) (ht 
: t₀ in s) : ContinuousWithinAt γ s t₀
参数：hγ : IsMIntegralCurveOn γ v s；ht : t₀ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsMIntegralCurveOn.continuousWithinAt (hγ : IsMIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).1
/-
**IsMIntegralCurveOn.continuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.continuousOn (hγ : IsMIntegralCurveOn γ v s) : Continuo
usOn γ s
参数：hγ : IsMIntegralCurveOn γ v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.continuousWithinAt`：HasMFDerivWithinAt.continuousWith
inAt (h : HasMFDerivAt[s] f x f') : ContinuousWithinAt f s x
-/
lemma IsMIntegralCurveOn.continuousOn (hγ : IsMIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht ↦ (hγ t ht).continuousWithinAt
/-
**IsMIntegralCurveAt.continuousAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt.continuousAt (hγ : IsMIntegralCurveAt γ v t₀) : Continu
ousAt γ t₀
参数：hγ : IsMIntegralCurveAt γ v t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用引理 `IsMIntegralCurveOn.continuousWithinAt`：IsMIntegralCurveOn.continuousWith
inAt (hγ : IsMIntegralCurveOn γ v s) (ht : t₀ in s) : ContinuousWithinAt γ s t₀
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma IsMIntegralCurveAt.continuousAt (hγ : IsMIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isMIntegralCurveAt_iff.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs
/-
**IsMIntegralCurve.continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.continuous (hγ : IsMIntegralCurve γ v) : Continuous γ
参数：hγ : IsMIntegralCurve γ v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `IsMIntegralCurveAt.continuousAt`：IsMIntegralCurveAt.continuousAt (hγ : I
sMIntegralCurveAt γ v t₀) : ContinuousAt γ t₀
· 使用引理 `IsMIntegralCurve.isMIntegralCurveAt`：IsMIntegralCurve.isMIntegralCurveAt
 (h : IsMIntegralCurve γ v) (t : Real) : IsMIntegralCurveAt γ v t
-/
lemma IsMIntegralCurve.continuous (hγ : IsMIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t ↦ (hγ.isMIntegralCurveAt t).continuousAt

variable [IsManifold I 1 M]

set_option backward.isDefEq.respectTransparency false in
/-- If `γ` is an integral curve of a vector field `v`, then `γ t` is tangent to `v (γ t)` when
expressed in the local chart around the initial point `γ t₀`. -/
/-
**IsMIntegralCurveOn.hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.hasDerivWithinAt (hγ : IsMIntegralCurveOn γ v s) {t : R
eal} (ht : t in s) (hsrc : γ t in (extChartAt I (γ t₀)).source) : HasDerivWithin
At ((extChartAt I (γ t₀)) ∘ γ) (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t)
)) s t
参数：hγ : IsMIntegralCurveOn γ v s；ht : t in s；hsrc : γ t in (extChartAt I (γ t₀))
.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivWithinAt_iff_hasFDerivWithinAt`：hasDerivWithinAt_iff_hasFDerivWi
thinAt {f' : F} : HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (toSpanSinglet
on 𝕜 f') s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_iff_hasFDerivWithinAt`：hasMFDerivWithinAt_iff_hasFDer
ivWithinAt : HasMFDerivAt[s] f x f' ↔ HasFDerivWithinAt f f' s x
· 使用定理 `HasMFDerivWithinAt.congr_mfderiv`：HasMFDerivWithinAt.congr_mfderiv (h : 
HasMFDerivAt[s] f x f') (h' : f' = f₁') : HasMFDerivAt[s] f x f₁'
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
· 使用定理 `hasMFDerivWithinAt_extChartAt`：hasMFDerivWithinAt_extChartAt (h : y in (
chartAt H x).source) : HasMFDerivAt[s] (extChartAt I x) y (mfderiv% (chartAt H x
) y :)
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `ContinuousLinearMap.smulRight_apply`：smulRight_apply {c : M₁ ->L[R] S} {
f : M₂} {x : M₁} : (smulRight c f : M₁ -> M₂) x = c x • f
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用引理 `mfderiv_chartAt_eq_tangentCoordChange`：mfderiv_chartAt_eq_tangentCoordCh
ange {x y : M} (hsrc : x in (chartAt H y).source) : mfderiv% (chartAt H y) x = t
angentCoordChange I x y x

--- 原说明 ---
If `γ` is an integral curve of a vector field `v`, then `γ t` is tangent to `v (
γ t)` when
expressed in the local chart around the initial point `γ t₀`.
-/
lemma IsMIntegralCurveOn.hasDerivWithinAt (hγ : IsMIntegralCurveOn γ v s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I (γ t₀)).source) :
    HasDerivWithinAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) s t := by
  -- turn `HasDerivWithinAt` into comp of `HasMFDerivWithinAt`
  replace hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**IsMIntegralCurveAt.eventually_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt.eventually_hasDerivAt (hγ : IsMIntegralCurveAt γ v t₀) 
: forallᶠ t in 𝓝 t₀, HasDerivAt ((extChartAt I (γ t₀)) ∘ γ) (tangentCoordChange 
I (γ t) (γ t₀) (γ t) (v (γ t))) t
参数：hγ : IsMIntegralCurveAt γ v t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_mem_nhds_iff`：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s
 in 𝓝 x') ↔ s in 𝓝 x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用引理 `IsMIntegralCurveAt.continuousAt`：IsMIntegralCurveAt.continuousAt (hγ : I
sMIntegralCurveAt γ v t₀) : ContinuousAt γ t₀
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_hasFDerivAt`：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDer
ivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivAt_iff_hasFDerivAt`：hasMFDerivAt_iff_hasFDerivAt : HasMFDerivA
t% f x f' ↔ HasFDerivAt f f' x
· 使用定理 `HasMFDerivAt.congr_mfderiv`：HasMFDerivAt.congr_mfderiv (h : HasMFDerivAt
% f x f') (h' : f' = f₁') : HasMFDerivAt% f x f₁'
· 使用定理 `HasMFDerivAt.comp`：HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf
 : HasMFDerivAt% f x f') : HasMFDerivAt% (g ∘ f) x (g'.comp f')
· 使用定理 `hasMFDerivAt_extChartAt`：hasMFDerivAt_extChartAt (h : y in (chartAt H x)
.source) : HasMFDerivAt% (extChartAt I x) y (mfderiv% (chartAt H x) y :)
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `ContinuousLinearMap.smulRight_apply`：smulRight_apply {c : M₁ ->L[R] S} {
f : M₂} {x : M₁} : (smulRight c f : M₁ -> M₂) x = c x • f
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用引理 `mfderiv_chartAt_eq_tangentCoordChange`：mfderiv_chartAt_eq_tangentCoordCh
ange {x y : M} (hsrc : x in (chartAt H y).source) : mfderiv% (chartAt H y) x = t
angentCoordChange I x y x
-/
lemma IsMIntegralCurveAt.eventually_hasDerivAt (hγ : IsMIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
  apply eventually_mem_nhds_iff.mpr
    (hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _)) |>.and hγ |>.mono
  rintro t ⟨ht1, ht2⟩
  have hsrc := mem_of_mem_nhds ht1
  rw [mem_preimage, extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) ht2).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl
