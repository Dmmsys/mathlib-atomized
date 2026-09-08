/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Integral curves of vector fields on a normed vector space

Let `E` be a normed vector space and `v : ℝ → E → E` be a time-dependent vector field on `E`.
An integral curve  of `v` is a function `γ : ℝ → E` such that the derivative of `γ` at `t` equals
`v t (γ t)`. The integral curve may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : ℝ → E → E` be a time-dependent vector field on `E`, and let `γ : ℝ → E`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v t (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v t (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v t (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

## TODO

* Implement `IsIntegralCurveWithinAt`.

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for all `t ∈ s`. -/
/-
**IsIntegralCurveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn (γ : Real -> E) (v : Real -> E -> E) (s : Set Real) : Pr
op
参数：γ : Real -> E；v : Real -> E -> E；s : Set Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for a
ll `t ∈ s`.
-/
def IsIntegralCurveOn (γ : ℝ → E) (v : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (v t (γ t)) s t

/-- `IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in a neighbourhood
containing `t₀`. -/
/-
**IsIntegralCurveAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt (γ : Real -> E) (v : Real -> E -> E) (t₀ : Real) : Prop
参数：γ : Real -> E；v : Real -> E -> E；t₀ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in
 a neighbourhood
containing `t₀`.
-/
def IsIntegralCurveAt (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

/-- `IsIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v`. That is, `γ t` is
tangent to `v t (γ t)` for all `t : ℝ`. -/
/-
**IsIntegralCurve** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIntegralCurve (γ : Real -> E) (v : Real -> E -> E) : Prop
参数：γ : Real -> E；v : Real -> E -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v`. That 
is, `γ t` is
tangent to `v t (γ t)` for all `t : ℝ`.
-/
def IsIntegralCurve (γ : ℝ → E) (v : ℝ → E → E) : Prop :=
  ∀ t : ℝ, HasDerivAt γ (v t (γ t)) t

variable {γ γ' : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}
/-
**IsIntegralCurve.isIntegralCurveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set Real)
 : IsIntegralCurveOn γ v s
参数：h : IsIntegralCurve γ v；s : Set Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
-/
lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ (h t).hasDerivWithinAt
/-
**isIntegralCurveOn_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveOn_univ : IsIntegralCurveOn γ v univ ↔ IsIntegralCurve γ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用引理 `IsIntegralCurve.isIntegralCurveOn`：IsIntegralCurve.isIntegralCurveOn (h 
: IsIntegralCurve γ v) (s : Set Real) : IsIntegralCurveOn γ v s
-/
lemma isIntegralCurveOn_univ :
    IsIntegralCurveOn γ v univ ↔ IsIntegralCurve γ v :=
  ⟨fun h t ↦ (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h ↦ h.isIntegralCurveOn _⟩
/-
**isIntegralCurveAt_iff_exists_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveAt_iff_exists_mem_nhds : IsIntegralCurveAt γ v t₀ ↔ exists 
s in 𝓝 t₀, IsIntegralCurveOn γ v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralCurveAt.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℝ E] (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ),   IsIntegralCurv
eAt γ v t₀ =…
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
-/
lemma isIntegralCurveAt_iff_exists_mem_nhds :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  rw [IsIntegralCurveAt, Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun t ht ↦ (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
/-
**isIntegralCurveAt_iff_exists_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveAt_iff_exists_pos : IsIntegralCurveAt γ v t₀ ↔ exists ε > 0
, IsIntegralCurveOn γ v (Metric.ball t₀ ε)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralCurveAt.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℝ E] (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ),   IsIntegralCurv
eAt γ v t₀ =…
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)

--- 原说明 ---
`γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some in
terval
containing `t₀`.
-/
lemma isIntegralCurveAt_iff_exists_pos :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [IsIntegralCurveAt, Metric.eventually_nhds_iff_ball]
  congrm ∃ ε > 0, ∀ (y : ℝ) (hy : y ∈ Metric.ball t₀ ε), ?_
  exact ⟨HasDerivAt.hasDerivWithinAt, fun h ↦ h.hasDerivAt (Metric.isOpen_ball.mem_nhds hy)⟩
/-
**IsIntegralCurve.isIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : Real) : I
sIntegralCurveAt γ v t
参数：h : IsIntegralCurve γ v；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isIntegralCurveAt_iff_exists_mem_nhds`：isIntegralCurveAt_iff_exists_mem_
nhds : IsIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsIntegralCurveOn γ v s
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
-/
lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t :=
  isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasDerivWithinAt⟩
/-
**isIntegralCurve_iff_isIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurve_iff_isIntegralCurveAt : IsIntegralCurve γ v ↔ forall t : R
eal, IsIntegralCurveAt γ v t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIntegralCurve.isIntegralCurveAt`：IsIntegralCurve.isIntegralCurveAt (h 
: IsIntegralCurve γ v) (t : Real) : IsIntegralCurveAt γ v t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isIntegralCurveAt_iff_exists_mem_nhds`：isIntegralCurveAt_iff_exists_mem_
nhds : IsIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsIntegralCurveOn γ v s
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasDerivAt hs⟩
/-
**IsIntegralCurveOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' subseteq s) 
: .mono hs IsIntegralCurveOn γ v s'
参数：h : IsIntegralCurveOn γ v s；hs : s' subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.mono`：HasDerivWithinAt.mono (h : HasDerivWithinAt f f' 
t x) (hst : s subseteq t) : HasDerivWithinAt f f' s x
-/
lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (hs ht) |>.mono hs
/-
**IsIntegralCurveAt.hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) : HasDerivAt γ
 (v t₀ (γ t₀)) t₀
参数：h : IsIntegralCurveAt γ v t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isIntegralCurveAt_iff_exists_mem_nhds`：isIntegralCurveAt_iff_exists_mem_
nhds : IsIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsIntegralCurveOn γ v s
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasDerivAt γ (v t₀ (γ t₀)) t₀ :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasDerivAt hs
/-
**IsIntegralCurveOn.isIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s 
in 𝓝 t₀) : IsIntegralCurveAt γ v t₀
参数：h : IsIntegralCurveOn γ v s；hs : s in 𝓝 t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isIntegralCurveAt_iff_exists_mem_nhds`：isIntegralCurveAt_iff_exists_mem_
nhds : IsIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsIntegralCurveOn γ v s
-/
lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
/-
**IsIntegralCurveAt.isIntegralCurveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt.isIntegralCurveOn (h : forall t in s, IsIntegralCurveAt 
γ v t) : IsIntegralCurveOn γ v s
参数：h : forall t in s, IsIntegralCurveAt γ v t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`.
-/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs') |>.hasDerivWithinAt
/-
**isIntegralCurveOn_iff_isIntegralCurveAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) : IsIntegralCurveO
n γ v s ↔ forall t in s, IsIntegralCurveAt γ v t
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIntegralCurveOn.isIntegralCurveAt`：IsIntegralCurveOn.isIntegralCurveAt
 (h : IsIntegralCurveOn γ v s) (hs : s in 𝓝 t₀) : IsIntegralCurveAt γ v t₀
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `IsIntegralCurveAt.isIntegralCurveOn`：IsIntegralCurveAt.isIntegralCurveOn
 (h : forall t in s, IsIntegralCurveAt γ v t) : IsIntegralCurveOn γ v s
-/
lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩
/-
**IsIntegralCurveOn.continuousWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : 
t₀ in s) : ContinuousWithinAt γ s t₀
参数：hγ : IsIntegralCurveOn γ v s；ht : t₀ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
-/
lemma IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).continuousWithinAt
/-
**IsIntegralCurveOn.continuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) : Continuous
On γ s
参数：hγ : IsIntegralCurveOn γ v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
-/
lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := (hγ · · |>.continuousWithinAt)
/-
**IsIntegralCurveAt.continuousAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) : Continuou
sAt γ t₀
参数：hγ : IsIntegralCurveAt γ v t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isIntegralCurveAt_iff_exists_mem_nhds`：isIntegralCurveAt_iff_exists_mem_
nhds : IsIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsIntegralCurveOn γ v s
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用引理 `IsIntegralCurveOn.continuousWithinAt`：IsIntegralCurveOn.continuousWithin
At (hγ : IsIntegralCurveOn γ v s) (ht : t₀ in s) : ContinuousWithinAt γ s t₀
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs
/-
**IsIntegralCurve.continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ
参数：hγ : IsIntegralCurve γ v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `IsIntegralCurveAt.continuousAt`：IsIntegralCurveAt.continuousAt (hγ : IsI
ntegralCurveAt γ v t₀) : ContinuousAt γ t₀
· 使用引理 `IsIntegralCurve.isIntegralCurveAt`：IsIntegralCurve.isIntegralCurveAt (h 
: IsIntegralCurve γ v) (t : Real) : IsIntegralCurveAt γ v t
-/
lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)
