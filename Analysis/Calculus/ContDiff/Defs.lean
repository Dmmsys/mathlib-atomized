/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
It is `C^∞` if it is `C^n` for all n.
Finally, it is `C^ω` if it is analytic (as well as all its derivative, which is automatic if the
space is complete).

We formalize these notions with predicates `ContDiffWithinAt`, `ContDiffAt`, `ContDiffOn` and
`ContDiff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `ContDiffOn` is not defined directly in terms of the
regularity of the specific choice `iteratedFDerivWithin 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`HasFTaylorSeriesUpToOn` defined in the file `FTaylorSeries`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `ContDiff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `ContDiffOn 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `ContDiffAt 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `ContDiffWithinAt 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.

In sets of unique differentiability, `ContDiffOn 𝕜 n f s` can be expressed in terms of the
properties of `iteratedFDerivWithin 𝕜 m f s` for `m ≤ n`. In the whole space,
`ContDiff 𝕜 n f` can be expressed in terms of the properties of `iteratedFDeriv 𝕜 m f`
for `m ≤ n`.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iteratedFDerivWithin`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
cannot happen over the real numbers, thanks to partitions of unity, but the behavior over a general
field is not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `ContDiffWithinAt` and `ContDiffOn`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `ContDiffWithinAt 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.
To avoid ambiguities with the two tops, the theorem names use either `infty` or `omega`.
These notations are scoped in `ContDiff`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

@[expose] public section

noncomputable section

open Set Fin Filter Function
open scoped NNReal Topology ContDiff

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {s s₁ t u : Set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F} {m n : ℕ∞ω}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Smooth functions within a set around a point -/

variable (𝕜) in
/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at `x`. The precise definition we
give (all the derivatives should be analytic) is more involved to work around issues when the space
is not complete, but it is equivalent when the space is complete.

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
@[fun_prop]
/-
**ContDiffWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContDiffWithinAt (n : Nat∞ω) (f : E -> F) (s : Set E) (x : E) : Prop
参数：n : Nat∞ω；f : E -> F；s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is continuously differentiable up to order `n` within a set `s` at a 
point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s 
∪ {x}`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`.
For `n = ∞`, we only require that this holds up to any finite order (where the n
eighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at `x`. The preci
se definition we
give (all the derivatives should be analytic) is more involved to work around is
sues when the space
is not complete, but it is equivalent when the space is complete.

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `
m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def ContDiffWithinAt (n : ℕ∞ω) (f : E → F) (s : Set E) (x : E) : Prop :=
  match n with
  | ω => ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn ω f p u ∧ ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) u
  | (n : ℕ∞) => ∀ m : ℕ, m ≤ n → ∃ u ∈ 𝓝[insert x s] x,
      ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u
/-
**HasFTaylorSeriesUpToOn.analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.analyticOn (hf : HasFTaylorSeriesUpToOn ω f p s) (h
 : AnalyticOn 𝕜 (fun x => p x 0) s) : AnalyticOn 𝕜 f s
参数：hf : HasFTaylorSeriesUpToOn ω f p s；h : AnalyticOn 𝕜 (fun x => p x 0) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `LinearIsometryEquiv.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
· 使用引理 `AnalyticOn.congr`：AnalyticOn.congr {f g : E -> F} {s : Set E} (hf : Anal
yticOn 𝕜 f s) (hs : EqOn g f s) : AnalyticOn 𝕜 g s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
-/
lemma HasFTaylorSeriesUpToOn.analyticOn
    (hf : HasFTaylorSeriesUpToOn ω f p s) (h : AnalyticOn 𝕜 (fun x ↦ p x 0) s) :
    AnalyticOn 𝕜 f s := by
  have : AnalyticOn 𝕜 (fun x ↦ (continuousMultilinearCurryFin0 𝕜 E F) (p x 0)) s :=
    (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
      h (Set.mapsTo_univ _ _)
  exact this.congr (fun y hy ↦ (hf.zero_eq _ hy).symm)
/-
**ContDiffWithinAt.analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.analyticOn (h : ContDiffWithinAt 𝕜 ω f s x) : exists u in
 𝓝[insert x s] x, AnalyticOn 𝕜 f u
参数：h : ContDiffWithinAt 𝕜 ω f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasFTaylorSeriesUpToOn.analyticOn`：HasFTaylorSeriesUpToOn.analyticOn (hf
 : HasFTaylorSeriesUpToOn ω f p s) (h : AnalyticOn 𝕜 (fun x => p x 0) s) : Analy
ticOn 𝕜 f s
-/
lemma ContDiffWithinAt.analyticOn (h : ContDiffWithinAt 𝕜 ω f s x) :
    ∃ u ∈ 𝓝[insert x s] x, AnalyticOn 𝕜 f u := by
  obtain ⟨u, hu, p, hp, h'p⟩ := h
  exact ⟨u, hu, hp.analyticOn (h'p 0)⟩
/-
**ContDiffWithinAt.analyticWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.analyticWithinAt (h : ContDiffWithinAt 𝕜 ω f s x) : Analy
ticWithinAt 𝕜 f s x
参数：h : ContDiffWithinAt 𝕜 ω f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticOn`：ContDiffWithinAt.analyticOn (h : ContDiffWi
thinAt 𝕜 ω f s x) : exists u in 𝓝[insert x s] x, AnalyticOn 𝕜 f u
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `AnalyticWithinAt.mono_of_mem_nhdsWithin`：AnalyticWithinAt.mono_of_mem_nh
dsWithin (h : AnalyticWithinAt 𝕜 f s x) (hst : s in 𝓝[t] x) : AnalyticWithinAt 𝕜
 f t x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
lemma ContDiffWithinAt.analyticWithinAt (h : ContDiffWithinAt 𝕜 ω f s x) :
    AnalyticWithinAt 𝕜 f s x := by
  obtain ⟨u, hu, hf⟩ := h.analyticOn
  have xu : x ∈ u := mem_of_mem_nhdsWithin (by simp) hu
  exact (hf x xu).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)
/-
**contDiffWithinAt_omega_iff_analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_omega_iff_analyticWithinAt [CompleteSpace F] : ContDiffWi
thinAt 𝕜 ω f s x ↔ AnalyticWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticWithinAt.exists_hasFTaylorSeriesUpToOn`：AnalyticWithinAt.exists_
hasFTaylorSeriesUpToOn [CompleteSpace F] (n : WithTop Nat∞) (h : AnalyticWithinA
t 𝕜 f s x) : exists u in 𝓝[insert x …
· 使用定理 `HasFTaylorSeriesUpToOn.of_le`：HasFTaylorSeriesUpToOn.of_le (h : HasFTayl
orSeriesUpToOn n f p s) (hmn : m <= n) : HasFTaylorSeriesUpToOn m f p s
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem contDiffWithinAt_omega_iff_analyticWithinAt [CompleteSpace F] :
    ContDiffWithinAt 𝕜 ω f s x ↔ AnalyticWithinAt 𝕜 f s x := by
  refine ⟨fun h ↦ h.analyticWithinAt, fun h ↦ ?_⟩
  obtain ⟨u, hu, p, hp, h'p⟩ := h.exists_hasFTaylorSeriesUpToOn ω
  exact ⟨u, hu, p, hp.of_le le_top, fun i ↦ h'p i⟩
/-
**contDiffWithinAt_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_nat {n : Nat} : ContDiffWithinAt 𝕜 n f s x ↔ exists u in 
𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeries
UpToOn n f p u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `HasFTaylorSeriesUpToOn.of_le`：HasFTaylorSeriesUpToOn.of_le (h : HasFTayl
orSeriesUpToOn n f p s) (hmn : m <= n) : HasFTaylorSeriesUpToOn m f p s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem contDiffWithinAt_nat {n : ℕ} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∃ u ∈ 𝓝[insert x s] x,
      ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le (mod_cast hm)⟩⟩

/-- When `n` is either a natural number or `ω`, one can characterize the property of being `C^n`
as the existence of a neighborhood on which there is a Taylor series up to order `n`,
requiring in addition that its terms are analytic in the `ω` case. -/
/-
**contDiffWithinAt_iff_of_ne_infty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_iff_of_ne_infty (hn : n != ∞) : ContDiffWithinAt 𝕜 n f s 
x ↔ exists u in 𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries 𝕜 E F, 
HasFTaylorSeriesUpToOn n f p u ∧ (n = ω -> forall i, AnalyticOn 𝕜 (fun x => p x 
i) u)
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
When `n` is either a natural number or `ω`, one can characterize the property of
 being `C^n`
as the existence of a neighborhood on which there is a Taylor series up to order
 `n`,
requiring in addition that its terms are analytic in the `ω` case.
-/
lemma contDiffWithinAt_iff_of_ne_infty (hn : n ≠ ∞) :
    ContDiffWithinAt 𝕜 n f s x ↔ ∃ u ∈ 𝓝[insert x s] x,
      ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn n f p u ∧
        (n = ω → ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) u) := by
  match n with
  | ω => simp [ContDiffWithinAt]
  | ∞ => simp at hn
  | (n : ℕ) => simp [contDiffWithinAt_nat]

@[fun_prop]
/-
**ContDiffWithinAt.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m <= n) : C
ontDiffWithinAt 𝕜 m f s x
参数：h : ContDiffWithinAt 𝕜 n f s x；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpToOn.of_le`：HasFTaylorSeriesUpToOn.of_le (h : HasFTayl
orSeriesUpToOn n f p s) (hmn : m <= n) : HasFTaylorSeriesUpToOn m f p s
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m ≤ n) :
    ContDiffWithinAt 𝕜 m f s x := by
  match n with
  | ω => match m with
    | ω => exact h
    | (m : ℕ∞) =>
      intro k _
      obtain ⟨u, hu, p, hp, -⟩ := h
      exact ⟨u, hu, p, hp.of_le le_top⟩
  | (n : ℕ∞) => match m with
    | ω => simp at hmn
    | (m : ℕ∞) => exact fun k hk ↦ h k (le_trans hk (mod_cast hmn))

/-- In a complete space, a function which is analytic within a set at a point is also `C^ω` there.
Note that the same statement for `AnalyticOn` does not require completeness, see
`AnalyticOn.contDiffOn`. -/
/-
**AnalyticWithinAt.contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] (h : AnalyticWithinAt 
𝕜 f s x) : ContDiffWithinAt 𝕜 n f s x
参数：h : AnalyticWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffWithinAt_omega_iff_analyticWithinAt`：contDiffWithinAt_omega_iff_
analyticWithinAt [CompleteSpace F] : ContDiffWithinAt 𝕜 ω f s x ↔ AnalyticWithin
At 𝕜 f s x
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
In a complete space, a function which is analytic within a set at a point is als
o `C^ω` there.
Note that the same statement for `AnalyticOn` does not require completeness, see
`AnalyticOn.contDiffOn`.
-/
theorem AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] (h : AnalyticWithinAt 𝕜 f s x) :
    ContDiffWithinAt 𝕜 n f s x :=
  (contDiffWithinAt_omega_iff_analyticWithinAt.2 h).of_le le_top
/-
**contDiffWithinAt_iff_forall_nat_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_iff_forall_nat_le {n : Nat∞} : ContDiffWithinAt 𝕜 n f s x
 ↔ forall m : Nat, ↑m <= n -> ContDiffWithinAt 𝕜 m f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contDiffWithinAt_iff_forall_nat_le {n : ℕ∞} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H m hm => H m hm _ le_rfl⟩
/-
**contDiffWithinAt_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_infty : ContDiffWithinAt 𝕜 ∞ f s x ↔ forall n : Nat, Cont
DiffWithinAt 𝕜 n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `contDiffWithinAt_iff_forall_nat_le`：contDiffWithinAt_iff_forall_nat_le {
n : Nat∞} : ContDiffWithinAt 𝕜 n f s x ↔ forall m : Nat, ↑m <= n -> ContDiffWith
inAt 𝕜 m f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffWithinAt_infty :
    ContDiffWithinAt 𝕜 ∞ f s x ↔ ∀ n : ℕ, ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_iff_forall_nat_le.trans <| by simp only [forall_prop_of_true, le_top]
/-
**ContDiffWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.continuousWithinAt (h : ContDiffWithinAt 𝕜 n f s x) : Con
tinuousWithinAt f s x
参数：h : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ContinuousWithinAt.mono_of_mem_nhdsWithin`：ContinuousWithinAt.mono_of_me
m_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x) : ContinuousWithi
nAt f s x
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `HasFTaylorSeriesUpToOn.continuousOn`：HasFTaylorSeriesUpToOn.continuousOn
 (h : HasFTaylorSeriesUpToOn n f p s) : ContinuousOn f s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mem_nhdsWithin_insert`：mem_nhdsWithin_insert {a : α} {s t : Set α} : t i
n 𝓝[insert a s] a ↔ a in t ∧ t in 𝓝[s] a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ContDiffWithinAt.continuousWithinAt (h : ContDiffWithinAt 𝕜 n f s x) :
    ContinuousWithinAt f s x := by
  have := h.of_le zero_le
  simp only [ContDiffWithinAt, nonpos_iff_eq_zero, Nat.cast_eq_zero, forall_eq, CharP.cast_eq_zero]
    at this
  rcases this with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuousOn.continuousWithinAt hu.1).mono_of_mem_nhdsWithin hu.2
/-
**ContDiffWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_of_eventuallyEq (h : ContDiffWithinAt 𝕜 n f s x) (h
₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin_insert`：mem_nhdsWithin_insert {a : α} {s t : Set α} : t i
n 𝓝[insert a s] a ↔ a in t ∧ t in 𝓝[s] a
· 使用定理 `HasFTaylorSeriesUpToOn.congr`：HasFTaylorSeriesUpToOn.congr (h : HasFTayl
orSeriesUpToOn n f p s) (h₁ : forall x in s, f₁ x = f x) : HasFTaylorSeriesUpToO
n n f₁ p s
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
-/
theorem ContDiffWithinAt.congr_of_eventuallyEq (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨{x ∈ u | f₁ x = f x}, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ ↦ And.right,
      fun i ↦ (H' i).mono (sep_subset _ _)⟩
  | (n : ℕ∞) =>
    intro m hm
    let ⟨u, hu, p, H⟩ := h m hm
    exact ⟨{ x ∈ u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ ↦ And.right⟩
/-
**Filter.EventuallyEq.congr_contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.congr_contDiffWithinAt (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁
 x = f x) : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.congr_contDiffWithinAt (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H ↦ H.congr_of_eventuallyEq h₁.symm hx.symm, fun H ↦ H.congr_of_eventuallyEq h₁ hx⟩
/-
**ContDiffWithinAt.congr_of_eventuallyEq_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_of_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f 
s x) (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : f₁ =ᶠ[𝓝[insert x s] x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem ContDiffWithinAt.congr_of_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ :)
/-
**Filter.EventuallyEq.congr_contDiffWithinAt_of_insert** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Filter.EventuallyEq.congr_contDiffWithinAt_of_insert (h₁ : f₁ =ᶠ[𝓝[insert 
x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h₁ : f₁ =ᶠ[𝓝[insert x s] x] f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq_insert`：ContDiffWithinAt.congr_of
_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[insert x s] 
x] f) : ContDiffWithinAt 𝕜 n f₁ s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_insert (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H ↦ H.congr_of_eventuallyEq_insert h₁.symm, fun H ↦ H.congr_of_eventuallyEq_insert h₁⟩
/-
**ContDiffWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f 
s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : ContDiffWithinAt 𝕜 n f₁ s x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
-/
theorem ContDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq h₁ <| h₁.self_of_nhdsWithin hx
/-
**Filter.EventuallyEq.congr_contDiffWithinAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : x in s) : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq_of_mem`：ContDiffWithinAt.congr_of
_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx
 : x in s) : ContDiffWithinAt 𝕜 n f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H ↦ H.congr_of_eventuallyEq_of_mem h₁.symm hx, fun H ↦ H.congr_of_eventuallyEq_of_mem h₁ hx⟩
/-
**ContDiffWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in 
s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : forall y in s, f₁ y = f y；hx : f₁ x = f x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx

/-- Version of `ContDiffWithinAt.congr` where `x` need not be contained in `s`,
but `f` and `f₁` are equal on a set containing both. -/
/-
**ContDiffWithinAt.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in
 t, f₁ y = f y) (hst : s subseteq t) (hxt : x in t) : ContDiffWithinAt 𝕜 n f₁ s 
x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : forall y in t, f₁ y = f y；hst : s subsete
q t；hxt : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x

--- 原说明 ---
Version of `ContDiffWithinAt.congr` where `x` need not be contained in `s`,
but `f` and `f₁` are equal on a set containing both.
-/
theorem ContDiffWithinAt.congr' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ t, f₁ y = f y)
    (hst : s ⊆ t) (hxt : x ∈ t) :
    ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr (fun _y hy ↦ h₁ _ (hst hy)) (h₁ x hxt)
/-
**contDiffWithinAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_congr (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) 
: ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h₁ : forall y in s, f₁ y = f y；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem contDiffWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun h' ↦ h'.congr (fun x hx ↦ (h₁ x hx).symm) hx.symm, fun h' ↦  h'.congr h₁ hx⟩
/-
**ContDiffWithinAt.congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : foral
l y in s, f₁ y = f y) (hx : x in s) : ContDiffWithinAt 𝕜 n f₁ s x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : forall y in s, f₁ y = f y；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
-/
theorem ContDiffWithinAt.congr_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)
/-
**contDiffWithinAt_congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_congr_of_mem (h₁ : forall y in s, f₁ y = f y) (hx : x in 
s) : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h₁ : forall y in s, f₁ y = f y；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_congr`：contDiffWithinAt_congr (h₁ : forall y in s, f₁ y
 = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f
 s x
-/
theorem contDiffWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr h₁ (h₁ x hx)
/-
**ContDiffWithinAt.congr_of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_of_insert (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : fo
rall y in insert x s, f₁ y = f y) : ContDiffWithinAt 𝕜 n f₁ s x
参数：h : ContDiffWithinAt 𝕜 n f s x；h₁ : forall y in insert x s, f₁ y = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem ContDiffWithinAt.congr_of_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : ∀ y ∈ insert x s, f₁ y = f y) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))
/-
**contDiffWithinAt_congr_of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_congr_of_insert (h₁ : forall y in insert x s, f₁ y = f y)
 : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h₁ : forall y in insert x s, f₁ y = f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_congr`：contDiffWithinAt_congr (h₁ : forall y in s, f₁ y
 = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f
 s x
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem contDiffWithinAt_congr_of_insert (h₁ : ∀ y ∈ insert x s, f₁ y = f y) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))
/-
**ContDiffWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.mono_of_mem_nhdsWithin (h : ContDiffWithinAt 𝕜 n f s x) {
t : Set E} (hst : s in 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x
参数：h : ContDiffWithinAt 𝕜 n f s x；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
· 使用定理 `insert_mem_nhdsWithin_insert`：insert_mem_nhdsWithin_insert {a : α} {s t 
: Set α} (h : t in 𝓝[s] a) : insert a t in 𝓝[insert a s] a
-/
theorem ContDiffWithinAt.mono_of_mem_nhdsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s ∈ 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H, H'⟩
  | (n : ℕ∞) =>
    intro m hm
    rcases h m hm with ⟨u, hu, p, H⟩
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩
/-
**ContDiffWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : 
t subseteq s) : ContDiffWithinAt 𝕜 n f t x
参数：h : ContDiffWithinAt 𝕜 n f s x；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) :
    ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem_nhdsWithin <| Filter.mem_of_superset self_mem_nhdsWithin hst
/-
**ContDiffWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_mono (h : ContDiffWithinAt 𝕜 n f s x) (h' : EqOn f₁
 f s₁) (h₁ : s₁ subseteq s) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s₁ x
参数：h : ContDiffWithinAt 𝕜 n f s x；h' : EqOn f₁ f s₁；h₁ : s₁ subseteq s；hx : f₁ x
 = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
-/
theorem ContDiffWithinAt.congr_mono
    (h : ContDiffWithinAt 𝕜 n f s x) (h' : EqOn f₁ f s₁) (h₁ : s₁ ⊆ s) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s₁ x :=
  (h.mono h₁).congr h' hx
/-
**ContDiffWithinAt.congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.congr_set (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (h
st : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x
参数：h : ContDiffWithinAt 𝕜 n f s x；hst : s =ᶠ[𝓝 x] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
-/
theorem ContDiffWithinAt.congr_set (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x := by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  apply h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin
/-
**contDiffWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_congr_set {t : Set E} (hst : s =ᶠ[𝓝 x] t) : ContDiffWithi
nAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x
参数：hst : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_set`：ContDiffWithinAt.congr_set (h : ContDiffWith
inAt 𝕜 n f s x) {t : Set E} (hst : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem contDiffWithinAt_congr_set {t : Set E} (hst : s =ᶠ[𝓝 x] t) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩
/-
**contDiffWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_inter' (h : t in 𝓝[s] x) : ContDiffWithinAt 𝕜 n f (s inte
r t) x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_congr_set`：contDiffWithinAt_congr_set {t : Set E} (hst 
: s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_eventuallyEq`：mem_nhdsWithin_iff_eventuallyEq {s t : 
Set α} {x : α} : t in 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s inter t : Set α)
-/
theorem contDiffWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr_set (mem_nhdsWithin_iff_eventuallyEq.1 h).symm
/-
**contDiffWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_inter (h : t in 𝓝 x) : ContDiffWithinAt 𝕜 n f (s inter t)
 x ↔ ContDiffWithinAt 𝕜 n f s x
参数：h : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_inter'`：contDiffWithinAt_inter' (h : t in 𝓝[s] x) : Con
tDiffWithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
-/
theorem contDiffWithinAt_inter (h : t ∈ 𝓝 x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)
/-
**contDiffWithinAt_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_insert_self : ContDiffWithinAt 𝕜 n f (insert x s) x ↔ Con
tDiffWithinAt 𝕜 n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.insert_idem`：insert_idem (a : α) (s : Set α) : insert a (insert a s)
 = insert a s
-/
theorem contDiffWithinAt_insert_self :
    ContDiffWithinAt 𝕜 n f (insert x s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω => simp [ContDiffWithinAt]
  | (n : ℕ∞) => simp_rw [ContDiffWithinAt, insert_idem]
/-
**contDiffWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_insert {y : E} : ContDiffWithinAt 𝕜 n f (insert y s) x ↔ 
ContDiffWithinAt 𝕜 n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `contDiffWithinAt_insert_self`：contDiffWithinAt_insert_self : ContDiffWit
hinAt 𝕜 n f (insert x s) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem contDiffWithinAt_insert {y : E} :
    ContDiffWithinAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rcases eq_or_ne x y with (rfl | hx)
  · exact contDiffWithinAt_insert_self
  refine ⟨fun h ↦ h.mono (subset_insert _ _), fun h ↦ ?_⟩
  apply h.mono_of_mem_nhdsWithin
  simp [nhdsWithin_insert_of_ne hx, self_mem_nhdsWithin]

alias ⟨ContDiffWithinAt.of_insert, ContDiffWithinAt.insert'⟩ := contDiffWithinAt_insert
/-
**ContDiffWithinAt.insert** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 : 
NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   {f : E → F} {x : E} {n
 : WithTop ℕ∞}, ContDiffWithinAt 𝕜 n f s x → ContDiffWithinAt 𝕜 n f (insert x s)
 x
参数：insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.insert'`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type uF} […
-/
protected theorem ContDiffWithinAt.insert (h : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n f (insert x s) x :=
  h.insert'
/-
**contDiffWithinAt_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_sdiff_singleton {y : E} : ContDiffWithinAt 𝕜 n f (s \ {y}
) x ↔ ContDiffWithinAt 𝕜 n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_insert`：contDiffWithinAt_insert {y : E} : ContDiffWithi
nAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffWithinAt_sdiff_singleton {y : E} :
    ContDiffWithinAt 𝕜 n f (s \ {y}) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rw [← contDiffWithinAt_insert, insert_sdiff_singleton, contDiffWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias contDiffWithinAt_diff_singleton := contDiffWithinAt_sdiff_singleton

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
/-
**ContDiffWithinAt.differentiableWithinAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.differentiableWithinAt' (h : ContDiffWithinAt 𝕜 n f s x) 
(hn : n != 0) : DifferentiableWithinAt 𝕜 f (insert x s) x
参数：h : ContDiffWithinAt 𝕜 n f s x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_nat`：contDiffWithinAt_nat {n : Nat} : ContDiffWithinAt 
𝕜 n f s x ↔ exists u in 𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries
 𝕜 E F, Ha…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.one_le_iff_ne_zero_withTop`：one_le_iff_ne_zero_withTop {n : WithTop
 Nat∞} : 1 <= n ↔ n != 0
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `differentiableWithinAt_inter`：differentiableWithinAt_inter (ht : t in 𝓝 
x) : DifferentiableWithinAt 𝕜 f (s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `HasFTaylorSeriesUpToOn.differentiableOn`：HasFTaylorSeriesUpToOn.differen
tiableOn (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0) : DifferentiableOn 𝕜
 f s
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differe
ntiable
within this set at this point.
-/
theorem ContDiffWithinAt.differentiableWithinAt' (h : ContDiffWithinAt 𝕜 n f s x) (hn : n ≠ 0) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  rcases contDiffWithinAt_nat.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)
    with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 <|
    ((H.mono tu).differentiableOn one_ne_zero) x ⟨mem_insert x s, xt⟩
/-
**ContDiffWithinAt.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.differentiableWithinAt (h : ContDiffWithinAt 𝕜 n f s x) (
hn : n != 0) : DifferentiableWithinAt 𝕜 f s x
参数：h : ContDiffWithinAt 𝕜 n f s x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ContDiffWithinAt.differentiableWithinAt'`：ContDiffWithinAt.differentiabl
eWithinAt' (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithin
At 𝕜 f (insert x s) x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem ContDiffWithinAt.differentiableWithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n ≠ 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiableWithinAt' hn).mono (subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`
(and moreover the function is analytic when `n = ω`). -/
/-
**contDiffWithinAt_succ_iff_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_succ_iff_hasFDerivWithinAt (hn : n != ∞) : ContDiffWithin
At 𝕜 (n + 1) f s x ↔ exists u in 𝓝[insert x s] x, (n = ω -> AnalyticOn 𝕜 f u) ∧ 
exists f' : E -> E ->L[𝕜] F, (forall x in u, HasFDerivWithinAt f (f' x) u x) ∧ C
ontDiffWithinAt 𝕜 n f' u x
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `contDiffWithinAt_iff_of_ne_infty`：contDiffWithinAt_iff_of_ne_infty (hn :
 n != ∞) : ContDiffWithinAt 𝕜 n f s x ↔ exists u in 𝓝[insert x s] x, exists p : 
E -> FormalMultilinear…
· 使用引理 `HasFTaylorSeriesUpToOn.analyticOn`：HasFTaylorSeriesUpToOn.analyticOn (hf
 : HasFTaylorSeriesUpToOn ω f p s) (h : AnalyticOn 𝕜 (fun x => p x 0) s) : Analy
ticOn 𝕜 f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.hasFDerivWithinAt`：HasFTaylorSeriesUpToOn.hasFDer
ivWithinAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0) (hx : x in s) : Ha
sFDerivWithinAt f (continuousM…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `hasFTaylorSeriesUpToOn_succ_iff_right`：hasFTaylorSeriesUpToOn_succ_iff_r
ight : HasFTaylorSeriesUpToOn (n + 1) f p s ↔ (forall x in s, (p x 0).curry0 = f
 x) ∧ (forall x in s, HasFD…
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `LinearIsometryEquiv.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is 
`C^n`
(and moreover the function is analytic when `n = ω`).
-/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt (hn : n ≠ ∞) :
    ContDiffWithinAt 𝕜 (n + 1) f s x ↔ ∃ u ∈ 𝓝[insert x s] x, (n = ω → AnalyticOn 𝕜 f u) ∧
      ∃ f' : E → E →L[𝕜] F,
      (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 n f' u x := by
  have h'n : n + 1 ≠ ∞ := by simpa using hn
  constructor
  · intro h
    rcases (contDiffWithinAt_iff_of_ne_infty h'n).1 h with ⟨u, hu, p, Hp, H'p⟩
    refine ⟨u, hu, ?_, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1),
        fun y hy => Hp.hasFDerivWithinAt (by simp) hy, ?_⟩
    · rintro rfl
      exact Hp.analyticOn (H'p rfl 0)
    apply (contDiffWithinAt_iff_of_ne_infty hn).2
    refine ⟨u, ?_, fun y : E => (p y).shift, ?_⟩
    · convert! @self_mem_nhdsWithin _ _ x u
      have : x ∈ insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right] at Hp
      refine ⟨Hp.2.2, ?_⟩
      rintro rfl i
      change AnalyticOn 𝕜
        (fun x ↦ (continuousMultilinearCurryRightEquiv' 𝕜 i E F) (p x (i + 1))) u
      apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
        ?_ (Set.mapsTo_univ _ _)
      exact H'p rfl _
  · rintro ⟨u, hu, hf, f', f'_eq_deriv, Hf'⟩
    rw [contDiffWithinAt_iff_of_ne_infty h'n]
    rcases (contDiffWithinAt_iff_of_ne_infty hn).1 Hf' with ⟨v, hv, p', Hp', p'_an⟩
    refine ⟨v ∩ u, ?_, fun x => (p' x).unshift (f x), ?_, ?_⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right]
      refine ⟨fun y _ => rfl, fun y hy => ?_, ?_⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v ∩ u) y
        rw [← Function.comp_def _ f, LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert! (f'_eq_deriv y hy.2).mono inter_subset_right
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert! (Hp'.mono inter_subset_left).congr fun x hx => Hp'.zero_eq x hx.1 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last, init_snoc]
    · intro h i
      simp only [WithTop.add_eq_top, WithTop.one_ne_top, or_false] at h
      match i with
      | 0 =>
        simp only [FormalMultilinearSeries.unshift]
        apply AnalyticOnNhd.comp_analyticOn _ ((hf h).mono inter_subset_right)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _
      | i + 1 =>
        simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one]
        apply AnalyticOnNhd.comp_analyticOn _ ((p'_an h i).mono inter_subset_left)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _

/-- A version of `contDiffWithinAt_succ_iff_hasFDerivWithinAt` where all derivatives
  are taken within the same set. -/
/-
**contDiffWithinAt_succ_iff_hasFDerivWithinAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_succ_iff_hasFDerivWithinAt' (hn : n != ∞) : ContDiffWithi
nAt 𝕜 (n + 1) f s x ↔ exists u in 𝓝[insert x s] x, u subseteq insert x s ∧ (n = 
ω -> AnalyticOn 𝕜 f u) ∧ exists f' : E -> E ->L[𝕜] F, (forall x in u, HasFDerivW
ithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt`：contDiffWithinAt_succ_iff_h
asFDerivWithinAt (hn : n != ∞) : ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u in 
𝓝[insert x s] x, (n = ω -> Analyt…
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `HasFDerivWithinAt.mono_of_mem_nhdsWithin`：HasFDerivWithinAt.mono_of_mem_
nhdsWithin (h : HasFDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasFDerivWithi
nAt f f' s x
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_insert`：contDiffWithinAt_insert {y : E} : ContDiffWithi
nAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `HasFDerivWithinAt.insert'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [
inst_3 : Topolo…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.insert`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F
 : Type uF} […

--- 原说明 ---
A version of `contDiffWithinAt_succ_iff_hasFDerivWithinAt` where all derivatives
  are taken within the same set.
-/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt' (hn : n ≠ ∞) :
    ContDiffWithinAt 𝕜 (n + 1) f s x ↔
      ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ (n = ω → AnalyticOn 𝕜 f u) ∧
      ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x := by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨u, hu, f_an, f', huf', hf'⟩ := (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhdsWithin.mp hu
    rw [inter_comm] at hwu
    refine ⟨insert x s ∩ w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left, ?_, f',
      fun y hy => ?_, ?_⟩
    · intro h
      apply (f_an h).mono hwu
    · refine ((huf' y <| hwu hy).mono hwu).mono_of_mem_nhdsWithin ?_
      grw [← subset_insert]
      exact inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt hn,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f_an, f', huf', hf'⟩
    exact ⟨u, hu, f_an, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩


/-! ### Smooth functions within a set -/

variable (𝕜) in
/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at every point of `s`. The precise
definition we give (all the derivatives should be analytic) is more involved to work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
@[fun_prop]
/-
**ContDiffOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContDiffOn (n : Nat∞ω) (f : E -> F) (s : Set E) : Prop
参数：n : Nat∞ω；f : E -> F；s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is continuously differentiable up to `n` on `s` if, for any point `x`
 in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`.

For `n = ∞`, we only require that this holds up to any finite order (where the n
eighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at every point of
 `s`. The precise
definition we give (all the derivatives should be analytic) is more involved to 
work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
def ContDiffOn (n : ℕ∞ω) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ContDiffWithinAt 𝕜 n f s x
/-
**HasFTaylorSeriesUpToOn.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.contDiffOn {n : Nat∞} {f' : E -> FormalMultilinearS
eries 𝕜 E F} (hf : HasFTaylorSeriesUpToOn n f f' s) : ContDiffOn 𝕜 n f s
参数：hf : HasFTaylorSeriesUpToOn n f f' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `HasFTaylorSeriesUpToOn.of_le`：HasFTaylorSeriesUpToOn.of_le (h : HasFTayl
orSeriesUpToOn n f p s) (hmn : m <= n) : HasFTaylorSeriesUpToOn m f p s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasFTaylorSeriesUpToOn.contDiffOn {n : ℕ∞} {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpToOn n f f' s) : ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and]
  exact ⟨f', hf.of_le (mod_cast hm)⟩
/-
**ContDiffOn.contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.contDiffWithinAt (h : ContDiffOn 𝕜 n f s) (hx : x in s) : ContD
iffWithinAt 𝕜 n f s x
参数：h : ContDiffOn 𝕜 n f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContDiffOn.contDiffWithinAt (h : ContDiffOn 𝕜 n f s) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f s x :=
  h x hx

@[fun_prop]
/-
**ContDiffOn.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= n) : ContDiffOn 𝕜 m 
f s
参数：h : ContDiffOn 𝕜 n f s；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
-/
theorem ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m ≤ n) : ContDiffOn 𝕜 m f s := fun x hx =>
  (h x hx).of_le hmn
/-
**ContDiffWithinAt.contDiffOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.contDiffOn' (hm : m <= n) (h' : m = ∞ -> n = ω) (h : Cont
DiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x in u ∧ ContDiffOn 𝕜 m f (insert
 x s inter u)
参数：hm : m <= n；h' : m = ∞ -> n = ω；h : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `contDiffWithinAt_nat`：contDiffWithinAt_nat {n : Nat} : ContDiffWithinAt 
𝕜 n f s x ↔ exists u in 𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries
 𝕜 E F, Ha…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `HasFTaylorSeriesUpToOn.contDiffOn`：HasFTaylorSeriesUpToOn.contDiffOn {n 
: Nat∞} {f' : E -> FormalMultilinearSeries 𝕜 E F} (hf : HasFTaylorSeriesUpToOn n
 f f' s) : ContDiffOn 𝕜…
-/
theorem ContDiffWithinAt.contDiffOn' (hm : m ≤ n) (h' : m = ∞ → n = ω)
    (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 m f (insert x s ∩ u) := by
  rcases eq_or_ne n ω with rfl | hn
  · obtain ⟨t, ht, p, hp, h'p⟩ := h
    rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
    rw [inter_comm] at hut
    refine ⟨u, huo, hxu, ?_⟩
    suffices ContDiffOn 𝕜 ω f (insert x s ∩ u) from this.of_le le_top
    intro y hy
    refine ⟨insert x s ∩ u, ?_, p, hp.mono hut, fun i ↦ (h'p i).mono hut⟩
    simp only [insert_eq_of_mem, hy, self_mem_nhdsWithin]
  · match m with
    | ω => simp [hn] at hm
    | ∞ => exact (hn (h' rfl)).elim
    | (m : ℕ) =>
      rcases contDiffWithinAt_nat.1 (h.of_le hm) with ⟨t, ht, p, hp⟩
      rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
      rw [inter_comm] at hut
      exact ⟨u, huo, hxu, (hp.mono hut).contDiffOn⟩
/-
**ContDiffWithinAt.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.contDiffOn (hm : m <= n) (h' : m = ∞ -> n = ω) (h : ContD
iffWithinAt 𝕜 n f s x) : exists u in 𝓝[insert x s] x, u subseteq insert x s ∧ Co
ntDiffOn 𝕜 m f u
参数：hm : m <= n；h' : m = ∞ -> n = ω；h : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem ContDiffWithinAt.contDiffOn (hm : m ≤ n) (h' : m = ∞ → n = ω)
    (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContDiffOn 𝕜 m f u := by
  obtain ⟨_u, uo, xu, h⟩ := h.contDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩
/-
**ContDiffOn.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : AnalyticOn 𝕜 f s
参数：h : ContDiffOn 𝕜 ω f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
-/
theorem ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : AnalyticOn 𝕜 f s :=
  fun x hx ↦ (h x hx).analyticWithinAt

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
/-
**contDiffWithinAt_iff_contDiffOn_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_iff_contDiffOn_nhds (hn : n != ∞) : ContDiffWithinAt 𝕜 n 
f s x ↔ exists u in 𝓝[insert x s] x, ContDiffOn 𝕜 n f u
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffOn`：ContDiffWithinAt.contDiffOn (hm : m <= n) (
h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u in 𝓝[insert x s
] x, u subseteq i…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s

--- 原说明 ---
A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `
C^n` on
a neighborhood of this point.
-/
theorem contDiffWithinAt_iff_contDiffOn_nhds (hn : n ≠ ∞) :
    ContDiffWithinAt 𝕜 n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContDiffOn 𝕜 n f u := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, h'u⟩
    exact ⟨u, hu, h'u.2⟩
  · rcases h with ⟨u, u_mem, hu⟩
    have : x ∈ u := mem_of_mem_nhdsWithin (mem_insert x s) u_mem
    exact (hu x this).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert x s) u_mem)
/-
**ContDiffWithinAt.eventually** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 : 
NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   {f : E → F} {x : E} {n
 : WithTop ℕ∞},   ContDiffWithinAt 𝕜 n f s x → n ≠ ↑⊤ → ∀ᶠ (y : E) in nhdsWithin
 x (insert x s), ContDiffWithinAt 𝕜 n f s y
参数：y : E；insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffOn`：ContDiffWithinAt.contDiffOn (hm : m <= n) (
h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u in 𝓝[insert x s
] x, u subseteq i…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem ContDiffWithinAt.eventually (h : ContDiffWithinAt 𝕜 n f s x) (hn : n ≠ ∞) :
    ∀ᶠ y in 𝓝[insert x s] x, ContDiffWithinAt 𝕜 n f s y := by
  rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, _, hd⟩
  have : ∀ᶠ y : E in 𝓝[insert x s] x, u ∈ 𝓝[insert x s] y ∧ y ∈ u :=
    (eventually_eventually_nhdsWithin.2 hu).and hu
  refine this.mono fun y hy => (hd y hy.2).mono_of_mem_nhdsWithin ?_
  exact nhdsWithin_mono y (subset_insert _ _) hy.1
/-
**ContDiffOn.of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 n f s
参数：h : ContDiffOn 𝕜 (n + 1) f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem ContDiffOn.of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 n f s :=
  h.of_le le_self_add
/-
**ContDiffOn.one_of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.one_of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 1 f s
参数：h : ContDiffOn 𝕜 (n + 1) f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem ContDiffOn.one_of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 1 f s :=
  h.of_le le_add_self
/-
**contDiffOn_iff_forall_nat_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_iff_forall_nat_le {n : Nat∞} : ContDiffOn 𝕜 n f s ↔ forall m : 
Nat, ↑m <= n -> ContDiffOn 𝕜 m f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contDiffOn_iff_forall_nat_le {n : ℕ∞} :
    ContDiffOn 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffOn 𝕜 m f s :=
  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H x hx m hm => H m hm x hx m le_rfl⟩
/-
**contDiffOn_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ forall n : Nat, ContDiffOn 𝕜 n f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `contDiffOn_iff_forall_nat_le`：contDiffOn_iff_forall_nat_le {n : Nat∞} : 
ContDiffOn 𝕜 n f s ↔ forall m : Nat, ↑m <= n -> ContDiffOn 𝕜 m f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s :=
  contDiffOn_iff_forall_nat_le.trans <| by simp only [le_top, forall_prop_of_true]
/-
**contDiffOn_all_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_all_iff_nat : (forall (n : Nat∞), ContDiffOn 𝕜 n f s) ↔ forall 
n : Nat, ContDiffOn 𝕜 n f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_infty`：contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ forall n : Nat
, ContDiffOn 𝕜 n f s
-/
theorem contDiffOn_all_iff_nat :
    (∀ (n : ℕ∞), ContDiffOn 𝕜 n f s) ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s := by
  refine ⟨fun H n => H n, ?_⟩
  rintro H (_ | n)
  exacts [contDiffOn_infty.2 H, H n]
/-
**ContDiffOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s
参数：h : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
-/
theorem ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]
/-
**ContDiffOn.continuousOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_zero (h : ContDiffOn 𝕜 0 f s) : ContinuousOn f s
参数：h : ContDiffOn 𝕜 0 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
-/
theorem ContDiffOn.continuousOn_zero (h : ContDiffOn 𝕜 0 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt
/-
**ContDiffOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall x in s, f₁ x = f x)
 : ContDiffOn 𝕜 n f₁ s
参数：h : ContDiffOn 𝕜 n f s；h₁ : forall x in s, f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
-/
theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
    ContDiffOn 𝕜 n f₁ s := fun x hx => (h x hx).congr h₁ (h₁ x hx)
/-
**contDiffOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_congr (h₁ : forall x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ 
ContDiffOn 𝕜 n f s
参数：h₁ : forall x in s, f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem contDiffOn_congr (h₁ : ∀ x ∈ s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩
/-
**ContDiffOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t subseteq s) 
: ContDiffOn 𝕜 n f t
参数：h : ContDiffOn 𝕜 n f s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
-/
theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) : ContDiffOn 𝕜 n f t :=
  fun x hx => (h x (hst hx)).mono hst
/-
**ContDiffOn.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : forall x in s₁, f₁ x
 = f x) (hs : s₁ subseteq s) : ContDiffOn 𝕜 n f₁ s₁
参数：hf : ContDiffOn 𝕜 n f s；h₁ : forall x in s₁, f₁ x = f x；hs : s₁ subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
-/
theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
    ContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
/-
**ContDiffOn.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : n != 0) : Diffe
rentiableOn 𝕜 f s
参数：h : ContDiffOn 𝕜 n f s；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x

--- 原说明 ---
If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there.
-/
theorem ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : n ≠ 0) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).differentiableWithinAt hn

@[fun_prop]
/-
**ContDiffOn.differentiableOn_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.differentiableOn_one (h : ContDiffOn 𝕜 1 f s) : DifferentiableO
n 𝕜 f s
参数：h : ContDiffOn 𝕜 1 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem ContDiffOn.differentiableOn_one (h : ContDiffOn 𝕜 1 f s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).differentiableWithinAt one_ne_zero

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
/-
**contDiffOn_of_locally_contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_locally_contDiffOn (h : forall x in s, exists u, IsOpen u ∧ 
x in u ∧ ContDiffOn 𝕜 n f (s inter u)) : ContDiffOn 𝕜 n f s
参数：h : forall x in s, exists u, IsOpen u ∧ x in u ∧ ContDiffOn 𝕜 n f (s inter u)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_inter`：contDiffWithinAt_inter (h : t in 𝓝 x) : ContDiff
WithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is `C^n` around each point in a set, then it is `C^n` on the set.
-/
theorem contDiffOn_of_locally_contDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 n f (s ∩ u)) : ContDiffOn 𝕜 n f s := by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
/-
**contDiffOn_succ_iff_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_iff_hasFDerivWithinAt (hn : n != ∞) : ContDiffOn 𝕜 (n + 1)
 f s ↔ forall x in s, exists u in 𝓝[insert x s] x, (n = ω -> AnalyticOn 𝕜 f u) ∧
 exists f' : E -> E ->L[𝕜] F, (forall x in u, HasFDerivWithinAt f (f' x) u x) ∧ 
ContDiffOn 𝕜 n f' u
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt`：contDiffWithinAt_succ_iff_h
asFDerivWithinAt (hn : n != ∞) : ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u in 
𝓝[insert x s] x, (n = ω -> Analyt…
· 使用定理 `ContDiffWithinAt.contDiffOn`：ContDiffWithinAt.contDiffOn (hm : m <= n) (
h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u in 𝓝[insert x s
] x, u subseteq i…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is 
`C^n`.
-/
theorem contDiffOn_succ_iff_hasFDerivWithinAt (hn : n ≠ ∞) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, (n = ω → AnalyticOn 𝕜 f u) ∧ ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffOn 𝕜 n f' u := by
  constructor
  · intro h x hx
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).1 (h x hx) with
      ⟨u, hu, f_an, f', hf', Hf'⟩
    rcases Hf'.contDiffOn le_rfl (by simp [hn]) with ⟨v, vu, v'u, hv⟩
    rw [insert_eq_of_mem hx] at hu ⊢
    have xu : x ∈ u := mem_of_mem_nhdsWithin hx hu
    rw [insert_eq_of_mem xu] at vu v'u
    exact ⟨v, nhdsWithin_le_of_mem hu vu, fun h ↦ (f_an h).mono v'u, f',
      fun y hy ↦ (hf' y (v'u hy)).mono v'u, hv⟩
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]
    rcases h x hx with ⟨u, u_nhbd, f_an, f', hu, hf'⟩
    have : x ∈ u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f_an, f', hu, hf' x this⟩


/-! ### Iterated derivative within a set -/

@[simp]
/-
**contDiffOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `hasFTaylorSeriesUpToOn_zero_iff`：hasFTaylorSeriesUpToOn_zero_iff : HasFT
aylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ forall x in s, (p x 0).curry0 = f
 x
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Iterated derivative within a set
-/
theorem contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s := by
  refine ⟨fun H => H.continuousOn, fun H => fun x hx m hm ↦ ?_⟩
  have : (m : ℕ∞ω) = 0 := le_antisymm (mod_cast hm) bot_le
  rw [this]
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  rw [hasFTaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x _ => by simp [ftaylorSeriesWithin]⟩
/-
**contDiffWithinAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_zero (hx : x in s) : ContDiffWithinAt 𝕜 0 f s x ↔ exists 
u in 𝓝[s] x, ContinuousOn f (s inter u)
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_inter'`：contDiffWithinAt_inter' (h : t in 𝓝[s] x) : Con
tDiffWithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `ContDiffOn.contDiffWithinAt`：ContDiffOn.contDiffWithinAt (h : ContDiffOn
 𝕜 n f s) (hx : x in s) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_zero`：contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
-/
theorem contDiffWithinAt_zero (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, ContinuousOn f (s ∩ u) := by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
    refine ⟨u, ?_, ?_⟩
    · simpa [hx] using H
    · simp only [Nat.cast_zero, hasFTaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono inter_subset_right
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (contDiffOn_zero.mpr hu).contDiffWithinAt h'

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylorSeriesWithin 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
/-
**ContDiffOn.ftaylorSeriesWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffOn`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 : 
NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   {f : E → F} {n : WithT
op ℕ∞},   ContDiffOn 𝕜 n f s → UniqueDiffOn 𝕜 s → HasFTaylorSeriesUpToOn n f (ft
aylorSeriesWithin 𝕜 f s) s
参数：ftaylorSeriesWithin 𝕜 f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ENat.add_one_natCast_le_withTop_of_lt`：add_one_natCast_le_withTop_of_lt 
{m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `HasFDerivWithinAt.congr`：HasFDerivWithinAt.congr (h : HasFDerivWithinAt 
f f' s x) (hs : EqOn f₁ f s) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylorSeriesWithin 𝕜 f s` as a Taylor series up to order `n` in `s`.
-/
protected theorem ContDiffOn.ftaylorSeriesWithin
    (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  constructor
  · intro x _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro m hm x hx
    have : (m + 1 : ℕ) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hm
    rcases (h x hx).of_le this _ le_rfl with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFDerivWithin 𝕜 m.succ f s x
      rw [← iteratedFDerivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this, ← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast Nat.le_succ m)
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (mod_cast lt_add_one m) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases (h x hx).of_le hm _ le_rfl with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine ⟨o, o_open, xo, ?_⟩
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm
/-
**iteratedFDerivWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_subset {n : Nat} (st : s subseteq t) (hs : UniqueDiff
On 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (h : ContDiffOn 𝕜 n f t) (hx : x in s) : iterate
dFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x
参数：st : s subseteq t；hs : UniqueDiffOn 𝕜 s；ht : UniqueDiffOn 𝕜 t；h : ContDiffOn 
𝕜 n f t；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iteratedFDerivWithin_subset {n : ℕ} (st : s ⊆ t) (hs : UniqueDiffOn 𝕜 s)
    (ht : UniqueDiffOn 𝕜 t) (h : ContDiffOn 𝕜 n f t) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (((h.ftaylorSeriesWithin ht).mono st).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx).symm
/-
**ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn {f : E -> F} {s : Set E
} {a : E} (h : ContDiffWithinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s) (ha : a in s)
 {m : Nat} (hm : m <= n) : forallᶠ t in (𝓝[s] a).smallSets, HasFTaylorSeriesUpTo
On m f (ftaylorSeriesWithin 𝕜 f s) t
参数：h : ContDiffWithinAt 𝕜 n f s a；hs : UniqueDiffOn 𝕜 s；ha : a in s；hm : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_smallSets_subset`：eventually_smallSets_subset {s : Set
 α} : (forallᶠ t in l.smallSets, t subseteq s) ↔ s in l
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `HasFTaylorSeriesUpToOn.congr_series`：HasFTaylorSeriesUpToOn.congr_series
 {q} (hp : HasFTaylorSeriesUpToOn n f p s) (hpq : forall m : Nat, m <= n -> EqOn
 (p · m) (q · m) s) : Has…
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn {f : E → F} {s : Set E} {a : E}
    (h : ContDiffWithinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) {m : ℕ} (hm : m ≤ n) :
    ∀ᶠ t in (𝓝[s] a).smallSets, HasFTaylorSeriesUpToOn m f (ftaylorSeriesWithin 𝕜 f s) t := by
  rcases h.contDiffOn' hm (by simp) with ⟨U, hUo, haU, hfU⟩
  have : ∀ᶠ t in (𝓝[s] a).smallSets, t ⊆ s ∩ U := by
    rw [eventually_smallSets_subset]
    exact inter_mem_nhdsWithin _ <| hUo.mem_nhds haU
  refine this.mono fun t ht ↦ .mono ?_ ht
  rw [insert_eq_of_mem ha] at hfU
  refine (hfU.ftaylorSeriesWithin (hs.inter hUo)).congr_series fun k hk x hx ↦ ?_
  exact iteratedFDerivWithin_inter_open hUo hx.2

/-- On a set with unique differentiability, an analytic function is automatically `C^ω`, as its
successive derivatives are also analytic. This does not require completeness of the space. See
also `AnalyticOn.contDiffOn_of_completeSpace`. -/
/-
**AnalyticOn.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.contDiffOn (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) : Con
tDiffOn 𝕜 n f s
参数：h : AnalyticOn 𝕜 f s；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticOn.exists_hasFTaylorSeriesUpToOn`：AnalyticOn.exists_hasFTaylorSe
riesUpToOn (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) : exists p : E -> Form
alMultilinearSeries 𝕜 E F, Has…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
On a set with unique differentiability, an analytic function is automatically `C
^ω`, as its
successive derivatives are also analytic. This does not require completeness of 
the space. See
also `AnalyticOn.contDiffOn_of_completeSpace`.
-/
theorem AnalyticOn.contDiffOn (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  rcases h.exists_hasFTaylorSeriesUpToOn hs with ⟨p, hp⟩
  intro x hx
  refine ⟨s, ?_, p, hp⟩
  rw [insert_eq_of_mem hx]
  exact self_mem_nhdsWithin

/-- On a set with unique differentiability, an analytic function is automatically `C^ω`, as its
successive derivatives are also analytic. This does not require completeness of the space. See
also `AnalyticOnNhd.contDiffOn_of_completeSpace`. -/
/-
**AnalyticOnNhd.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.contDiffOn (h : AnalyticOnNhd 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
 : ContDiffOn 𝕜 n f s
参数：h : AnalyticOnNhd 𝕜 f s；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOn.contDiffOn`：AnalyticOn.contDiffOn (h : AnalyticOn 𝕜 f s) (hs 
: UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s

--- 原说明 ---
On a set with unique differentiability, an analytic function is automatically `C
^ω`, as its
successive derivatives are also analytic. This does not require completeness of 
the space. See
also `AnalyticOnNhd.contDiffOn_of_completeSpace`.
-/
theorem AnalyticOnNhd.contDiffOn (h : AnalyticOnNhd 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s := h.analyticOn.contDiffOn hs

/-- An analytic function is automatically `C^ω` in a complete space -/
/-
**AnalyticOn.contDiffOn_of_completeSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.contDiffOn_of_completeSpace [CompleteSpace F] (h : AnalyticOn 𝕜
 f s) : ContDiffOn 𝕜 n f s
参数：h : AnalyticOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.contDiffWithinAt`：AnalyticWithinAt.contDiffWithinAt [Co
mpleteSpace F] (h : AnalyticWithinAt 𝕜 f s x) : ContDiffWithinAt 𝕜 n f s x

--- 原说明 ---
An analytic function is automatically `C^ω` in a complete space
-/
theorem AnalyticOn.contDiffOn_of_completeSpace [CompleteSpace F] (h : AnalyticOn 𝕜 f s) :
    ContDiffOn 𝕜 n f s :=
  fun x hx ↦ (h x hx).contDiffWithinAt

/-- An analytic function is automatically `C^ω` in a complete space -/
/-
**AnalyticOnNhd.contDiffOn_of_completeSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.contDiffOn_of_completeSpace [CompleteSpace F] (h : AnalyticO
nNhd 𝕜 f s) : ContDiffOn 𝕜 n f s
参数：h : AnalyticOnNhd 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOn.contDiffOn_of_completeSpace`：AnalyticOn.contDiffOn_of_complet
eSpace [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : ContDiffOn 𝕜 n f s
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s

--- 原说明 ---
An analytic function is automatically `C^ω` in a complete space
-/
theorem AnalyticOnNhd.contDiffOn_of_completeSpace [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    ContDiffOn 𝕜 n f s :=
  h.analyticOn.contDiffOn_of_completeSpace
/-
**contDiffOn_of_continuousOn_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_continuousOn_differentiableOn {n : Nat∞} (Hcont : forall m :
 Nat, m <= n -> ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) (Hdiff
 : forall m : Nat, m < n -> DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 
m f s x) s) : ContDiffOn 𝕜 n f s
参数：Hcont : forall m : Nat, m <= n -> ContinuousOn (fun x => iteratedFDerivWithin
 𝕜 m f s x) s；Hdiff : forall m : Nat, m < n -> DifferentiableOn 𝕜 (fun x => iter
atedFDerivWithin 𝕜 m f s x) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem contDiffOn_of_continuousOn_differentiableOn {n : ℕ∞}
    (Hcont : ∀ m : ℕ, m ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s)
    (Hdiff : ∀ m : ℕ, m < n →
      DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  constructor
  · intro y _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro k hk y hy
    convert! (Hdiff k (lt_of_lt_of_le (mod_cast hk) (mod_cast hm)) y hy).hasFDerivWithinAt
  · intro k hk
    exact Hcont k (le_trans (mod_cast hk) (mod_cast hm))
/-
**contDiffOn_of_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_differentiableOn {n : Nat∞} (h : forall m : Nat, m <= n -> D
ifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) : ContDiffOn 𝕜 n f s
参数：h : forall m : Nat, m <= n -> DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f 
s) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `contDiffOn_of_continuousOn_differentiableOn`：contDiffOn_of_continuousOn_
differentiableOn {n : Nat∞} (Hcont : forall m : Nat, m <= n -> ContinuousOn (fun
 x => iteratedFDerivWithin 𝕜 m f …
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem contDiffOn_of_differentiableOn {n : ℕ∞}
    (h : ∀ m : ℕ, m ≤ n → DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s :=
  contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).continuousOn) fun m hm =>
    h m (le_of_lt hm)
/-
**contDiffOn_of_analyticOn_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_analyticOn_iteratedFDerivWithin (h : forall m, AnalyticOn 𝕜 
(iteratedFDerivWithin 𝕜 m f s) s) : ContDiffOn 𝕜 n f s
参数：h : forall m, AnalyticOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `AnalyticOn.differentiableOn`：AnalyticOn.differentiableOn (h : AnalyticOn
 𝕜 f s) : DifferentiableOn 𝕜 f s
· 使用定理 `AnalyticOn.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem contDiffOn_of_analyticOn_iteratedFDerivWithin
    (h : ∀ m, AnalyticOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  intro x hx
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
  · rw [insert_eq_of_mem hx]
    constructor
    · intro y _
      simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
        iteratedFDerivWithin_zero_apply]
    · intro k _ y hy
      exact ((h k).differentiableOn y hy).hasFDerivWithinAt
    · intro k _
      exact (h k).continuousOn
  · intro i
    rw [insert_eq_of_mem hx]
    exact h i
/-
**contDiffOn_omega_iff_analyticOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_omega_iff_analyticOn (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 ω f
 s ↔ AnalyticOn 𝕜 f s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `AnalyticOn.contDiffOn`：AnalyticOn.contDiffOn (h : AnalyticOn 𝕜 f s) (hs 
: UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s
-/
theorem contDiffOn_omega_iff_analyticOn (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ω f s ↔ AnalyticOn 𝕜 f s :=
  ⟨fun h m ↦ h.analyticOn m, fun h ↦ h.contDiffOn hs⟩
/-
**ContDiffOn.continuousOn_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_iteratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n
 f s) (hmn : m <= n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFDerivWithi
n 𝕜 m f s) s
参数：h : ContDiffOn 𝕜 n f s；hmn : m <= n；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ContDiffOn.continuousOn_iteratedFDerivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFDerivWithin 𝕜 m f s) s :=
  ((h.of_le hmn).ftaylorSeriesWithin hs).cont m le_rfl
/-
**ContDiffOn.differentiableOn_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.differentiableOn_iteratedFDerivWithin {m : Nat} (h : ContDiffOn
 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) : DifferentiableOn 𝕜 (iteratedFD
erivWithin 𝕜 m f s) s
参数：h : ContDiffOn 𝕜 n f s；hmn : m < n；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.add_one_natCast_le_withTop_of_lt`：add_one_natCast_le_withTop_of_lt 
{m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem ContDiffOn.differentiableOn_iteratedFDerivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s := by
  intro x hx
  have : (m + 1 : ℕ) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hmn
  apply (((h.of_le this).ftaylorSeriesWithin hs).fderivWithin m ?_ x hx).differentiableWithinAt
  exact_mod_cast lt_add_one m
/-
**ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin {m : Nat} (h 
: ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
 DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f s) s x
参数：h : ContDiffWithinAt 𝕜 n f s x；hmn : m < n；hs : UniqueDiffOn 𝕜 (insert x s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_beq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b : α}, 
(a == b) = false → a ≠ b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Std.LawfulBCmp.toTransCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : LT α
} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   Std.T
ransCmp cmp
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用引理 `ENat.add_one_natCast_le_withTop_of_lt`：add_one_natCast_le_withTop_of_lt 
{m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `nhdsWithin_inter_of_mem'`：nhdsWithin_inter_of_mem' {a : α} {s t : Set α}
 (h : t in 𝓝[s] a) : 𝓝[s inter t] a = 𝓝[s] a
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `iteratedFDerivWithin_eventually_congr_set'`：iteratedFDerivWithin_eventua
lly_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : Nat) : iteratedFDerivWithin 
𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWi…
（共 50 条，此处仅展示前 30 条）
-/
theorem ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f s) s x := by
  have : (m + 1 : ℕ∞ω) ≠ ∞ := Ne.symm (ne_of_beq_false rfl)
  rcases h.contDiffOn' (ENat.add_one_natCast_le_withTop_of_lt hmn) (by simp [this])
    with ⟨u, uo, xu, hu⟩
  set t := insert x s ∩ u
  have A : t =ᶠ[𝓝[≠] x] s := by
    simp only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc, nhdsWithin_inter_of_mem', ← sdiff_eq_compl_inter, insert_sdiff_of_mem,
      sdiff_eq_compl_inter]
    exacts [rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFDerivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 m f t :=
    iteratedFDerivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f t) t x :=
    hu.differentiableOn_iteratedFDerivWithin (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventuallyEq (B.filter_mono inf_le_left) B.self_of_nhds
/-
**contDiffOn_iff_continuousOn_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_iff_continuousOn_differentiableOn {n : Nat∞} (hs : UniqueDiffOn
 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (forall m : Nat, m <= n -> ContinuousOn (fun x => i
teratedFDerivWithin 𝕜 m f s x) s) ∧ forall m : Nat, m < n -> DifferentiableOn 𝕜 
(fun x => iteratedFDerivWithin 𝕜 m f s x) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffOn.continuousOn_iteratedFDerivWithin`：ContDiffOn.continuousOn_it
eratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m <= n) (hs : Uniqu
eDiffOn 𝕜 s) : ContinuousOn (itera…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContDiffOn.differentiableOn_iteratedFDerivWithin`：ContDiffOn.differentia
bleOn_iteratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs 
: UniqueDiffOn 𝕜 s) : DifferentiableOn…
· 使用定理 `contDiffOn_of_continuousOn_differentiableOn`：contDiffOn_of_continuousOn_
differentiableOn {n : Nat∞} (Hcont : forall m : Nat, m <= n -> ContinuousOn (fun
 x => iteratedFDerivWithin 𝕜 m f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contDiffOn_iff_continuousOn_differentiableOn {n : ℕ∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (∀ m : ℕ, m ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) ∧
        ∀ m : ℕ, m < n → DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s :=
  ⟨fun h => ⟨fun _m hm => h.continuousOn_iteratedFDerivWithin (mod_cast hm) hs,
      fun _m hm => h.differentiableOn_iteratedFDerivWithin (mod_cast hm) hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩
/-
**contDiffOn_nat_iff_continuousOn_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_nat_iff_continuousOn_differentiableOn {n : Nat} (hs : UniqueDif
fOn 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (forall m : Nat, m <= n -> ContinuousOn (fun x =
> iteratedFDerivWithin 𝕜 m f s x) s) ∧ forall m : Nat, m < n -> DifferentiableOn
 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `contDiffOn_iff_continuousOn_differentiableOn`：contDiffOn_iff_continuousO
n_differentiableOn {n : Nat∞} (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (fo
rall m : Nat, m <= n -> Continuous…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_nat_iff_continuousOn_differentiableOn {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (∀ m : ℕ, m ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) ∧
        ∀ m : ℕ, m < n → DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s := by
  rw [← WithTop.coe_natCast, contDiffOn_iff_continuousOn_differentiableOn hs]
  simp
/-
**contDiffOn_succ_of_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_of_fderivWithin (hf : DifferentiableOn 𝕜 f s) (h' : n = ω 
-> AnalyticOn 𝕜 f s) (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : Co
ntDiffOn 𝕜 (n + 1) f s
参数：hf : DifferentiableOn 𝕜 f s；h' : n = ω -> AnalyticOn 𝕜 f s；h : ContDiffOn 𝕜 n
 (fun y => fderivWithin 𝕜 f s y) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.coe_top_add_one`：↑⊤ + 1 = ↑⊤
· 使用定理 `contDiffOn_infty`：contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ forall n : Nat
, ContDiffOn 𝕜 n f s
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt`：contDiffWithinAt_succ_iff_h
asFDerivWithinAt (hn : n != ∞) : ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u in 
𝓝[insert x s] x, (n = ω -> Analyt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem contDiffOn_succ_of_fderivWithin (hf : DifferentiableOn 𝕜 f s)
    (h' : n = ω → AnalyticOn 𝕜 f s)
    (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 (n + 1) f s := by
  rcases eq_or_ne n ∞ with rfl | hn
  · rw [ENat.coe_top_add_one, contDiffOn_infty]
    intro m x hx
    apply ContDiffWithinAt.of_le _ (show (m : ℕ∞ω) ≤ m + 1 from le_self_add)
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp),
      insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, (by simp), fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, (h x hx).of_le (mod_cast le_top)⟩
  · intro x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn,
      insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, h', fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, h x hx⟩
/-
**contDiffOn_of_analyticOn_of_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_analyticOn_of_fderivWithin (hf : AnalyticOn 𝕜 f s) (h : Cont
DiffOn 𝕜 ω (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 n f s
参数：hf : AnalyticOn 𝕜 f s；h : ContDiffOn 𝕜 ω (fun y => fderivWithin 𝕜 f s y) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffOn_succ_of_fderivWithin`：contDiffOn_succ_of_fderivWithin (hf : D
ifferentiableOn 𝕜 f s) (h' : n = ω -> AnalyticOn 𝕜 f s) (h : ContDiffOn 𝕜 n (fun
 y => fderivWithin 𝕜 …
· 使用定理 `AnalyticOn.differentiableOn`：AnalyticOn.differentiableOn (h : AnalyticOn
 𝕜 f s) : DifferentiableOn 𝕜 f s
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem contDiffOn_of_analyticOn_of_fderivWithin (hf : AnalyticOn 𝕜 f s)
    (h : ContDiffOn 𝕜 ω (fun y ↦ fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 (ω + 1) f s from this.of_le le_top
  exact contDiffOn_succ_of_fderivWithin hf.differentiableOn (fun _ ↦ hf) h

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderivWithin`) is `C^n`. -/
/-
**contDiffOn_succ_iff_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n
 + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 
n (fderivWithin 𝕜 f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.differentiableOn`：ContDiffOn.differentiableOn (h : ContDiffOn
 𝕜 n f s) (hn : n != 0) : DifferentiableOn 𝕜 f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt`：contDiffWithinAt_succ_iff_h
asFDerivWithinAt (hn : n != ∞) : ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u in 
𝓝[insert x s] x, (n = ω -> Analyt…
· 使用定理 `ne_of_beq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b : α}, 
(a == b) = false → a ≠ b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Std.LawfulBCmp.toTransCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : LT α
} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   Std.T
ransCmp cmp
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
A function is `C^(n + 1)` on a domain with unique derivatives if and only if it 
is
differentiable there, and its derivative (expressed with `fderivWithin`) is `C^n
`.
-/
theorem contDiffOn_succ_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧
      ContDiffOn 𝕜 n (fderivWithin 𝕜 f s) s := by
  refine ⟨fun H => ?_, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2.1 h.2.2⟩
  refine ⟨H.differentiableOn (by simp), ?_, fun x hx => ?_⟩
  · rintro rfl
    exact H.analyticOn
  have A (m : ℕ) (hm : m ≤ n) : ContDiffWithinAt 𝕜 m (fun y => fderivWithin 𝕜 f s y) s x := by
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := m) (ne_of_beq_false rfl)).1
      (H.of_le (by gcongr) x hx) with ⟨u, hu, -, f', hff', hf'⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm, insert_eq_of_mem hx] at ho
    have := hf'.mono ho
    rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
    apply this.congr_of_eventuallyEq_of_mem _ hx
    have : o ∩ s ∈ 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, Subset.refl _⟩
    rw [inter_comm] at this
    refine Filter.eventuallyEq_of_mem this fun y hy => ?_
    have A : fderivWithin 𝕜 f (s ∩ o) y = f' y :=
      ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
    rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A
  match n with
  | ω => exact (H.analyticOn.fderivWithin hs).contDiffOn hs (n := ω) x hx
  | ∞ => exact contDiffWithinAt_infty.2 (fun m ↦ A m (mod_cast le_top))
  | (n : ℕ) => exact A n le_rfl
/-
**contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hs : UniqueDiffOn 𝕜
 s) : ContDiffOn 𝕜 (n + 1) f s ↔ (n = ω -> AnalyticOn 𝕜 f s) ∧ exists f' : E -> 
E ->L[𝕜] F, ContDiffOn 𝕜 n f' s ∧ forall x, x in s -> HasFDerivWithinAt f (f' x)
 s x
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ContDiffWithinAt.congr_of_mem`：ContDiffWithinAt.congr_of_mem (h : ContDi
ffWithinAt 𝕜 n f s x) (h₁ : forall y in s, f₁ y = f y) (hx : x in s) : ContDiffW
ithinAt 𝕜 n f₁ s x
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔ (n = ω → AnalyticOn 𝕜 f s) ∧
      ∃ f' : E → E →L[𝕜] F, ContDiffOn 𝕜 n f' s ∧ ∀ x, x ∈ s → HasFDerivWithinAt f (f' x) s x := by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun h => ⟨h.2.1, fderivWithin 𝕜 f s, h.2.2,
    fun x hx => (h.1 x hx).hasFDerivWithinAt⟩, fun ⟨f_an, h⟩ => ?_⟩
  rcases h with ⟨f', h1, h2⟩
  refine ⟨fun x hx => (h2 x hx).differentiableWithinAt, f_an, fun x hx => ?_⟩
  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx
/-
**contDiffOn_infty_iff_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_infty_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 ∞
 f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.coe_top_add_one`：↑⊤ + 1 = ↑⊤
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_infty_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 f s) s := by
  rw [← ENat.coe_top_add_one, contDiffOn_succ_iff_fderivWithin hs]
  simp

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
/-
**contDiffOn_succ_iff_fderiv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_iff_fderiv_of_isOpen (hs : IsOpen s) : ContDiffOn 𝕜 (n + 1
) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (f
deriv 𝕜 f) s
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `contDiffOn_congr`：contDiffOn_congr (h₁ : forall x in s, f₁ x = f x) : Co
ntDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `fderivWithin_of_isOpen`：fderivWithin_of_isOpen (hs : IsOpen s) (hx : x i
n s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`.
-/
theorem contDiffOn_succ_iff_fderiv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧
      ContDiffOn 𝕜 n (fderiv 𝕜 f) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn,
    contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx]
/-
**contDiffOn_infty_iff_fderiv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_infty_iff_fderiv_of_isOpen (hs : IsOpen s) : ContDiffOn 𝕜 ∞ f s
 ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fderiv 𝕜 f) s
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.coe_top_add_one`：↑⊤ + 1 = ↑⊤
· 使用定理 `contDiffOn_succ_iff_fderiv_of_isOpen`：contDiffOn_succ_iff_fderiv_of_isOp
en (hs : IsOpen s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧ Con…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_infty_iff_fderiv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fderiv 𝕜 f) s := by
  rw [← ENat.coe_top_add_one, contDiffOn_succ_iff_fderiv_of_isOpen hs]
  simp
/-
**ContDiffOn.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffOn`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 : 
NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   {f : E → F} {m n : Wit
hTop ℕ∞},   ContDiffOn 𝕜 n f s → UniqueDiffOn 𝕜 s → m + 1 ≤ n → ContDiffOn 𝕜 m (
fderivWithin 𝕜 f s) s
参数：fderivWithin 𝕜 f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
-/
protected theorem ContDiffOn.fderivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (fderivWithin 𝕜 f s) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2.2
/-
**ContDiffOn.fderiv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn
 : m + 1 <= n) : ContDiffOn 𝕜 m (fderiv 𝕜 f) s
参数：hf : ContDiffOn 𝕜 n f s；hs : IsOpen s；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `ContDiffOn.fderivWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F
 : Type uF} […
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_of_isOpen`：fderivWithin_of_isOpen (hs : IsOpen s) (hx : x i
n s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x
-/
theorem ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fderiv 𝕜 f) s :=
  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm
/-
**ContDiffOn.continuousOn_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_fderivWithin (h : ContDiffOn 𝕜 n f s) (hs : Unique
DiffOn 𝕜 s) (hn : 1 <= n) : ContinuousOn (fderivWithin 𝕜 f s) s
参数：h : ContDiffOn 𝕜 n f s；hs : UniqueDiffOn 𝕜 s；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
-/
theorem ContDiffOn.continuousOn_fderivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (fderivWithin 𝕜 f s) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1
    (h.of_le (show 0 + (1 : ℕ∞ω) ≤ n from hn))).2.2.continuousOn
/-
**ContDiffOn.continuousOn_fderiv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_fderiv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : Is
Open s) (hn : 1 <= n) : ContinuousOn (fderiv 𝕜 f) s
参数：h : ContDiffOn 𝕜 n f s；hs : IsOpen s；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_succ_iff_fderiv_of_isOpen`：contDiffOn_succ_iff_fderiv_of_isOp
en (hs : IsOpen s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧ Con…
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
-/
theorem ContDiffOn.continuousOn_fderiv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (fderiv 𝕜 f) s :=
  ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1
    (h.of_le (show 0 + (1 : ℕ∞ω) ≤ n from hn))).2.2.continuousOn

/-! ### Smooth functions at a point -/

variable (𝕜) in
/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic at `x`. The precise
definition we give (all the derivatives should be analytic) is more involved to work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
@[fun_prop]
/-
**ContDiffAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContDiffAt (n : Nat∞ω) (f : E -> F) (x : E) : Prop
参数：n : Nat∞ω；f : E -> F；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is continuously differentiable up to `n` at a point `x` if, for any i
nteger `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, whi
ch are continuous.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`.

For `n = ∞`, we only require that this holds up to any finite order (where the n
eighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic at `x`. The precise
definition we give (all the derivatives should be analytic) is more involved to 
work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
def ContDiffAt (n : ℕ∞ω) (f : E → F) (x : E) : Prop :=
  ContDiffWithinAt 𝕜 n f univ x
/-
**contDiffWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x :=
  Iff.rfl
/-
**contDiffAt_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_infty : ContDiffAt 𝕜 ∞ f x ↔ forall n : Nat, ContDiffAt 𝕜 n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffAt_infty : ContDiffAt 𝕜 ∞ f x ↔ ∀ n : ℕ, ContDiffAt 𝕜 n f x := by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_infty]

@[fun_prop]
/-
**ContDiffAt.contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.contDiffWithinAt (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 
n f s x
参数：h : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiffAt.contDiffWithinAt (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)

@[fun_prop]
/-
**ContDiffWithinAt.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s in 𝓝 
x) : ContDiffAt 𝕜 n f x
参数：h : ContDiffWithinAt 𝕜 n f s x；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffAt.eq_1`：∀ (𝕜 : Type u) [inst : NontriviallyNormedField 𝕜] {E : 
Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type 
uF} […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_inter`：contDiffWithinAt_inter (h : t in 𝓝 x) : ContDiff
WithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x := by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]
/-
**contDiffWithinAt_iff_contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_iff_contDiffAt (h : s in 𝓝 x) : ContDiffWithinAt 𝕜 n f s 
x ↔ ContDiffAt 𝕜 n f x
参数：h : s in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `contDiffWithinAt_inter`：contDiffWithinAt_inter (h : t in 𝓝 x) : ContDiff
WithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffWithinAt_iff_contDiffAt (h : s ∈ 𝓝 x) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffAt 𝕜 n f x := by
  rw [← univ_inter s, contDiffWithinAt_inter h, contDiffWithinAt_univ]
/-
**IsOpen.contDiffOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.contDiffOn_iff (hs : IsOpen s) : ContDiffOn 𝕜 n f s ↔ forall ⦃a⦄, a
 in s -> ContDiffAt 𝕜 n f a
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `contDiffWithinAt_iff_contDiffAt`：contDiffWithinAt_iff_contDiffAt (h : s 
in 𝓝 x) : ContDiffWithinAt 𝕜 n f s x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsOpen.contDiffOn_iff (hs : IsOpen s) :
    ContDiffOn 𝕜 n f s ↔ ∀ ⦃a⦄, a ∈ s → ContDiffAt 𝕜 n f a :=
  forall₂_congr fun _ => contDiffWithinAt_iff_contDiffAt ∘ hs.mem_nhds

@[fun_prop]
/-
**ContDiffOn.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (hx : s in 𝓝 x) : ContDiffA
t 𝕜 n f x
参数：h : ContDiffOn 𝕜 n f s；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x :=
  (h _ (mem_of_mem_nhds hx)).contDiffAt hx
/-
**ContDiffAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x]
 f) : ContDiffAt 𝕜 n f₁ x
参数：h : ContDiffAt 𝕜 n f x；hg : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq_of_mem`：ContDiffWithinAt.congr_of
_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx
 : x in s) : ContDiffWithinAt 𝕜 n f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
    ContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventuallyEq_of_mem (by rwa [nhdsWithin_univ]) (mem_univ x)
/-
**ContDiffAt.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= n) : ContDiffAt 𝕜 m 
f x
参数：h : ContDiffAt 𝕜 n f x；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
-/
theorem ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m ≤ n) : ContDiffAt 𝕜 m f x :=
  ContDiffWithinAt.of_le h hmn

@[fun_prop]
/-
**ContDiffAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x
参数：h : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
-/
theorem ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x := by
  simpa [continuousWithinAt_univ] using h.continuousWithinAt
/-
**ContDiffAt.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : AnalyticAt 𝕜 f x
参数：h : ContDiffAt 𝕜 ω f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
-/
theorem ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : AnalyticAt 𝕜 f x := by
  rw [← contDiffWithinAt_univ] at h
  rw [← analyticWithinAt_univ]
  exact h.analyticWithinAt

/-- In a complete space, a function which is analytic at a point is also `C^ω` there.
Note that the same statement for `AnalyticOn` does not require completeness, see
`AnalyticOn.contDiffOn`. -/
/-
**AnalyticAt.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) : ContDiffA
t 𝕜 n f x
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `AnalyticWithinAt.contDiffWithinAt`：AnalyticWithinAt.contDiffWithinAt [Co
mpleteSpace F] (h : AnalyticWithinAt 𝕜 f s x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …

--- 原说明 ---
In a complete space, a function which is analytic at a point is also `C^ω` there
.
Note that the same statement for `AnalyticOn` does not require completeness, see
`AnalyticOn.contDiffOn`.
-/
theorem AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ]
  rw [← analyticWithinAt_univ] at h
  exact h.contDiffWithinAt

@[simp]
/-
**contDiffWithinAt_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_compl_self : ContDiffWithinAt 𝕜 n f {x}ᶜ x ↔ ContDiffAt 𝕜
 n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `contDiffWithinAt_sdiff_singleton`：contDiffWithinAt_sdiff_singleton {y : 
E} : ContDiffWithinAt 𝕜 n f (s \ {y}) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffWithinAt_compl_self :
    ContDiffWithinAt 𝕜 n f {x}ᶜ x ↔ ContDiffAt 𝕜 n f x := by
  rw [compl_eq_univ_sdiff, contDiffWithinAt_sdiff_singleton, contDiffWithinAt_univ]

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
/-
**ContDiffAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.differentiableAt (h : ContDiffAt 𝕜 n f x) (hn : n != 0) : Diffe
rentiableAt 𝕜 f x
参数：h : ContDiffAt 𝕜 n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x

--- 原说明 ---
If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there.
-/
theorem ContDiffAt.differentiableAt (h : ContDiffAt 𝕜 n f x) (hn : n ≠ 0) :
    DifferentiableAt 𝕜 f x := by
  simpa [hn, differentiableWithinAt_univ] using h.differentiableWithinAt
/-
**ContDiffAt.differentiableAt_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.differentiableAt_iteratedFDeriv {f : E -> F} {n : Nat∞ω} {m : N
at} {x : E} (h : ContDiffAt 𝕜 n f x) (hmn : ↑m < n) : DifferentiableAt 𝕜 (iterat
edFDeriv 𝕜 m f) x
参数：h : ContDiffAt 𝕜 n f x；hmn : ↑m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin`：ContDiffWi
thinAt.differentiableWithinAt_iteratedFDerivWithin {m : Nat} (h : ContDiffWithin
At 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem ContDiffAt.differentiableAt_iteratedFDeriv
    {f : E → F} {n : ℕ∞ω} {m : ℕ} {x : E} (h : ContDiffAt 𝕜 n f x) (hmn : ↑m < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 m f) x := by
  rw [← differentiableWithinAt_univ]
  convert! (h.differentiableWithinAt_iteratedFDerivWithin hmn (by simp [uniqueDiffOn_univ]))
  exact iteratedFDerivWithin_univ.symm

@[fun_prop]
/-
**ContDiffAt.differentiableAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.differentiableAt_one (h : ContDiffAt 𝕜 1 f x) : DifferentiableA
t 𝕜 f x
参数：h : ContDiffAt 𝕜 1 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
-/
theorem ContDiffAt.differentiableAt_one (h : ContDiffAt 𝕜 1 f x) :
    DifferentiableAt 𝕜 f x := by
  simpa [(le_refl 1), differentiableWithinAt_univ] using h.differentiableWithinAt

nonrec lemma ContDiffAt.contDiffOn (h : ContDiffAt 𝕜 n f x) (hm : m ≤ n) (h' : m = ∞ → n = ω) :
    ∃ u ∈ 𝓝 x, ContDiffOn 𝕜 m f u := by
  simpa [nhdsWithin_univ] using h.contDiffOn hm h'

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
/-
**contDiffAt_succ_iff_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_succ_iff_hasFDerivAt {n : Nat} : ContDiffAt 𝕜 (n + 1) f x ↔ exi
sts f' : E -> E ->L[𝕜] F, (exists u in 𝓝 x, forall x in u, HasFDerivAt f (f' x) 
x) ∧ ContDiffAt 𝕜 n f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt`：contDiffWithinAt_succ_iff_h
asFDerivWithinAt (hn : n != ∞) : ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u in 
𝓝[insert x s] x, (n = ω -> Analyt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `HasFDerivWithinAt.hasFDerivAt`：HasFDerivWithinAt.hasFDerivAt (h : HasFDe
rivWithinAt f f' s x) (hs : s in 𝓝 x) : HasFDerivAt f f' x
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x

--- 原说明 ---
A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `
C^n`.
-/
theorem contDiffAt_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiffAt 𝕜 (n + 1) f x ↔ ∃ f' : E → E →L[𝕜] F,
      (∃ u ∈ 𝓝 x, ∀ x ∈ u, HasFDerivAt f (f' x) x) ∧ ContDiffAt 𝕜 n f' x := by
  rw [← contDiffWithinAt_univ, contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, -, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine ⟨f', ⟨t, ?_⟩, h_cont_diff.contDiffAt H⟩
    refine ⟨mem_nhds_iff.mpr ⟨t, Subset.rfl, ht, hxt⟩, ?_⟩
    intro y hyt
    refine (h_fderiv y (htu hyt)).hasFDerivAt ?_
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine ⟨u, H, by simp, f', fun x hxu ↦ ?_, h_cont_diff.contDiffWithinAt⟩
    exact (h_fderiv x hxu).hasFDerivWithinAt
/-
**ContDiffAt.eventually** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 : 
NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {x : E} {n : WithTop ℕ
∞}, ContDiffAt 𝕜 n f x → n ≠ ↑⊤ → ∀ᶠ (y : E) in nhds x, ContDiffAt 𝕜 n f y
参数：y : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `ContDiffWithinAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
-/
protected theorem ContDiffAt.eventually (h : ContDiffAt 𝕜 n f x) (h' : n ≠ ∞) :
    ∀ᶠ y in 𝓝 x, ContDiffAt 𝕜 n f y := by
  simpa [nhdsWithin_univ] using! ContDiffWithinAt.eventually h h'
/-
**iteratedFDerivWithin_eq_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_eq_iteratedFDeriv {n : Nat} (hs : UniqueDiffOn 𝕜 s) (
h : ContDiffAt 𝕜 n f x) (hx : x in s) : iteratedFDerivWithin 𝕜 n f s x = iterate
dFDeriv 𝕜 n f x
参数：hs : UniqueDiffOn 𝕜 s；h : ContDiffAt 𝕜 n f x；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `iteratedFDerivWithin_subset`：iteratedFDerivWithin_subset {n : Nat} (st :
 s subseteq t) (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (h : ContDiffOn 𝕜
 n f t) (hx : x i…
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
-/
theorem iteratedFDerivWithin_eq_iteratedFDeriv {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [← iteratedFDerivWithin_inter_open u_open xu,
    ← iteratedFDerivWithin_inter_open u_open xu (s := univ)]
  apply iteratedFDerivWithin_subset
  · exact inter_subset_inter_left _ (subset_univ _)
  · exact hs.inter u_open
  · apply uniqueDiffOn_univ.inter u_open
  · simpa using hu
  · exact ⟨hx, xu⟩

/-! ### Smooth functions -/

variable (𝕜) in
/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.

For `n = ω`, we require the function to be analytic. The precise
definition we give (all the derivatives should be analytic) is more involved to work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
@[fun_prop]
/-
**ContDiff** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContDiff (n : Nat∞ω) (f : E -> F) : Prop
参数：n : Nat∞ω；f : E -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is continuously differentiable up to `n` if it admits derivatives up 
to
order `n`, which are continuous. Contrary to the case of definitions in domains 
(where derivatives
might not be unique) we do not need to localize the definition in space or time.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`.

For `n = ω`, we require the function to be analytic. The precise
definition we give (all the derivatives should be analytic) is more involved to 
work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
def ContDiff (n : ℕ∞ω) (f : E → F) : Prop :=
  match n with
  | ω => ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo ⊤ f p
      ∧ ∀ i, AnalyticOnNhd 𝕜 (fun x ↦ p x i) univ
  | (n : ℕ∞) => ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p

/-- If `f` has a Taylor series up to `n`, then it is `C^n`. -/
/-
**HasFTaylorSeriesUpTo.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpTo.contDiff {n : Nat∞} {f' : E -> FormalMultilinearSerie
s 𝕜 E F} (hf : HasFTaylorSeriesUpTo n f f') : ContDiff 𝕜 n f
参数：hf : HasFTaylorSeriesUpTo n f f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
If `f` has a Taylor series up to `n`, then it is `C^n`.
-/
theorem HasFTaylorSeriesUpTo.contDiff {n : ℕ∞} {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpTo n f f') : ContDiff 𝕜 n f :=
  ⟨f', hf⟩
/-
**contDiffOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 : 
NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {n : WithTop ℕ∞}, Cont
DiffOn 𝕜 n f ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, fun_prop] theorem contDiffOn_empty : ContDiffOn 𝕜 n f ∅ := fun _x hx ↦ hx.elim
/-
**contDiffOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFTaylorSeriesUpToOn_univ_iff`：hasFTaylorSeriesUpToOn_univ_iff : HasFT
aylorSeriesUpToOn n f p univ ↔ HasFTaylorSeriesUpTo n f p
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `analyticOn_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 …
· 使用定理 `AnalyticOn.iteratedFDerivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type v} […
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `Filter.univ_sets`：∀ {α : Type u_1} (self : Filter α), Set.univ ∈ self.se
ts
· 使用定理 `HasFTaylorSeriesUpToOn.of_le`：HasFTaylorSeriesUpToOn.of_le (h : HasFTayl
orSeriesUpToOn n f p s) (hmn : m <= n) : HasFTaylorSeriesUpToOn m f p s
· 使用定理 `HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn`：HasFTaylorSeriesUpTo.hasFTa
ylorSeriesUpToOn (h : HasFTaylorSeriesUpTo n f p) (s : Set E) : HasFTaylorSeries
UpToOn n f p s
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
-/
theorem contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f := by
  match n with
  | ω =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      refine ⟨H.ftaylorSeriesWithin uniqueDiffOn_univ, fun i ↦ ?_⟩
      rw [← analyticOn_univ]
      exact H.analyticOn.iteratedFDerivWithin uniqueDiffOn_univ _
    · rintro ⟨p, hp, h'p⟩ x _
      exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le le_top,
        fun i ↦ (h'p i).analyticOn⟩
  | (n : ℕ∞) =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      exact H.ftaylorSeriesWithin uniqueDiffOn_univ
    · rintro ⟨p, hp⟩ x _ m hm
      exact ⟨univ, Filter.univ_sets _, p,
        (hp.hasFTaylorSeriesUpToOn univ).of_le (mod_cast hm)⟩
/-
**contDiff_iff_contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ forall x, ContDiffAt 𝕜 n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ ∀ x, ContDiffAt 𝕜 n f x := by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]

@[fun_prop]
/-
**ContDiff.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x
参数：h : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
-/
theorem ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x :=
  contDiff_iff_contDiffAt.1 h x

@[fun_prop]
/-
**ContDiff.contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s 
x
参数：h : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s x :=
  h.contDiffAt.contDiffWithinAt
/-
**contDiff_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_infty : ContDiff 𝕜 ∞ f ↔ forall n : Nat, ContDiff 𝕜 n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_infty : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp [contDiffOn_univ.symm, contDiffOn_infty]
/-
**contDiff_all_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_all_iff_nat : (forall n : Nat∞, ContDiff 𝕜 n f) ↔ forall n : Nat,
 ContDiff 𝕜 n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_all_iff_nat : (∀ n : ℕ∞, ContDiff 𝕜 n f) ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

@[fun_prop]
/-
**ContDiff.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s
参数：h : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s :=
  (contDiffOn_univ.2 h).mono (subset_univ _)

@[simp]
/-
**contDiff_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `contDiffOn_zero`：contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
-/
theorem contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f := by
  rw [← contDiffOn_univ, ← continuousOn_univ]
  exact contDiffOn_zero
/-
**contDiffAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ exists u in 𝓝 x, ContinuousOn f u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, ContinuousOn f u := by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]
/-
**contDiffAt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_one_iff : ContDiffAt 𝕜 1 f x ↔ exists f' : E -> E ->L[𝕜] F, exi
sts u in 𝓝 x, ContinuousOn f' u ∧ forall x in u, HasFDerivAt f (f' x) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.exists_mem_and_iff`：exists_mem_and_iff {P : Set α -> Prop} {Q : S
et α -> Prop} (hP : Antitone P) (hQ : Antitone Q) : ((exists u in f, P u) ∧ exis
ts u in f, Q u)…
· 使用定理 `Set.antitone_bforall`：antitone_bforall {P : α -> Prop} : Antitone fun s 
: Set α => forall x in s, P x
· 使用定理 `antitone_continuousOn`：antitone_continuousOn {f : α -> β} : Antitone (Co
ntinuousOn f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffAt_one_iff :
    ContDiffAt 𝕜 1 f x ↔
      ∃ f' : E → E →L[𝕜] F, ∃ u ∈ 𝓝 x, ContinuousOn f' u ∧ ∀ x ∈ u, HasFDerivAt f (f' x) x := by
  rw [show (1 : ℕ∞ω) = (0 : ℕ) + 1 from rfl]
  simp_rw [contDiffAt_succ_iff_hasFDerivAt, show ((0 : ℕ) : ℕ∞ω) = 0 from rfl,
    contDiffAt_zero, exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm]

@[fun_prop]
/-
**ContDiff.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : ContDiff 𝕜 m f
参数：h : ContDiff 𝕜 n f；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m ≤ n) : ContDiff 𝕜 m f :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 h).of_le hmn
/-
**ContDiff.of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.of_succ (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f
参数：h : ContDiff 𝕜 (n + 1) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem ContDiff.of_succ (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f :=
  h.of_le le_self_add
/-
**ContDiff.one_of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.one_of_succ (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f
参数：h : ContDiff 𝕜 (n + 1) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem ContDiff.one_of_succ (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f := by
  apply h.of_le le_add_self

@[fun_prop]
/-
**ContDiff.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f
参数：h : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

@[fun_prop]
/-
**ContDiff.continuous_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_zero (h : ContDiff 𝕜 0 f) : Continuous f
参数：h : ContDiff 𝕜 0 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ContDiff.continuous_zero (h : ContDiff 𝕜 0 f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
@[fun_prop]
/-
**ContDiff.differentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : n != 0) : Differentiabl
e 𝕜 f
参数：h : ContDiff 𝕜 n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用定理 `ContDiffOn.differentiableOn`：ContDiffOn.differentiableOn (h : ContDiffOn
 𝕜 n f s) (hn : n != 0) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f

--- 原说明 ---
If a function is `C^n` with `n ≥ 1`, then it is differentiable.
-/
theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : n ≠ 0) : Differentiable 𝕜 f :=
  differentiableOn_univ.1 <| (contDiffOn_univ.2 h).differentiableOn hn

@[fun_prop]
/-
**ContDiff.differentiable_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.differentiable_one (h : ContDiff 𝕜 1 f) : Differentiable 𝕜 f
参数：h : ContDiff 𝕜 1 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用定理 `ContDiffOn.differentiableOn`：ContDiffOn.differentiableOn (h : ContDiffOn
 𝕜 n f s) (hn : n != 0) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem ContDiff.differentiable_one (h : ContDiff 𝕜 1 f) : Differentiable 𝕜 f :=
  differentiableOn_univ.1 <| (contDiffOn_univ.2 h).differentiableOn one_ne_zero
/-
**contDiff_iff_forall_nat_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_iff_forall_nat_le {n : Nat∞} : ContDiff 𝕜 n f ↔ forall m : Nat, ↑
m <= n -> ContDiff 𝕜 m f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `contDiffOn_iff_forall_nat_le`：contDiffOn_iff_forall_nat_le {n : Nat∞} : 
ContDiffOn 𝕜 n f s ↔ forall m : Nat, ↑m <= n -> ContDiffOn 𝕜 m f s
-/
theorem contDiff_iff_forall_nat_le {n : ℕ∞} :
    ContDiff 𝕜 n f ↔ ∀ m : ℕ, ↑m ≤ n → ContDiff 𝕜 m f := by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le

/-- A function is `C^(n+1)` iff it has a `C^n` derivative. -/
/-
**contDiff_succ_iff_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_succ_iff_hasFDerivAt {n : Nat} : ContDiff 𝕜 (n + 1) f ↔ exists f'
 : E -> E ->L[𝕜] F, ContDiff 𝕜 n f' ∧ forall x, HasFDerivAt f (f' x) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`：contDiffOn_succ_i
ff_hasFDerivWithinAt_of_uniqueDiffOn (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n +
 1) f s ↔ (n = ω -> AnalyticOn 𝕜 f s) ∧ exi…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is `C^(n+1)` iff it has a `C^n` derivative.
-/
theorem contDiff_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiff 𝕜 (n + 1) f ↔
      ∃ f' : E → E →L[𝕜] F, ContDiff 𝕜 n f' ∧ ∀ x, HasFDerivAt f (f' x) x := by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ, Set.mem_univ, forall_true_left,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn uniqueDiffOn_univ,
    WithTop.natCast_ne_top, analyticOn_univ, false_implies, true_and]
/-
**contDiff_one_iff_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_one_iff_hasFDerivAt : ContDiff 𝕜 1 f ↔ exists f' : E -> E ->L[𝕜] 
F, Continuous f' ∧ forall x, HasFDerivAt f (f' x) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `contDiff_succ_iff_hasFDerivAt`：contDiff_succ_iff_hasFDerivAt {n : Nat} :
 ContDiff 𝕜 (n + 1) f ↔ exists f' : E -> E ->L[𝕜] F, ContDiff 𝕜 n f' ∧ forall x,
 HasFDerivAt f (f' …
-/
theorem contDiff_one_iff_hasFDerivAt : ContDiff 𝕜 1 f ↔
    ∃ f' : E → E →L[𝕜] F, Continuous f' ∧ ∀ x, HasFDerivAt f (f' x) x := by
  convert! contDiff_succ_iff_hasFDerivAt using 4; simp
/-
**AnalyticOn.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.contDiff (hf : AnalyticOn 𝕜 f univ) : ContDiff 𝕜 n f
参数：hf : AnalyticOn 𝕜 f univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `AnalyticOn.contDiffOn`：AnalyticOn.contDiffOn (h : AnalyticOn 𝕜 f s) (hs 
: UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem AnalyticOn.contDiff (hf : AnalyticOn 𝕜 f univ) : ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]
  exact hf.contDiffOn (n := n) uniqueDiffOn_univ
/-
**AnalyticOnNhd.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f univ) : ContDiff 𝕜 n f
参数：hf : AnalyticOnNhd 𝕜 f univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOn.contDiff`：AnalyticOn.contDiff (hf : AnalyticOn 𝕜 f univ) : Co
ntDiff 𝕜 n f
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
-/
theorem AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f univ) : ContDiff 𝕜 n f :=
  hf.analyticOn.contDiff
/-
**ContDiff.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.analyticOnNhd (h : ContDiff 𝕜 ω f) : AnalyticOnNhd 𝕜 f s
参数：h : ContDiff 𝕜 ω f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `AnalyticOnNhd.mono`：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd
 𝕜 f t) (hst : s subseteq t) : AnalyticOnNhd 𝕜 f s
· 使用定理 `analyticOn_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 …
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.analyticOnNhd (h : ContDiff 𝕜 ω f) : AnalyticOnNhd 𝕜 f s := by
  rw [← contDiffOn_univ] at h
  have := h.analyticOn
  rw [analyticOn_univ] at this
  exact this.mono (subset_univ _)
/-
**contDiff_omega_iff_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_omega_iff_analyticOnNhd : ContDiff 𝕜 ω f ↔ AnalyticOnNhd 𝕜 f univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.analyticOnNhd`：ContDiff.analyticOnNhd (h : ContDiff 𝕜 ω f) : An
alyticOnNhd 𝕜 f s
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
-/
theorem contDiff_omega_iff_analyticOnNhd :
    ContDiff 𝕜 ω f ↔ AnalyticOnNhd 𝕜 f univ :=
  ⟨fun h ↦ h.analyticOnNhd, fun h ↦ h.contDiff⟩

/-! ### Iterated derivative -/

/-- When a function is `C^n`, it admits `ftaylorSeries 𝕜 f` as a Taylor series up
to order `n` in `s`. -/
/-
**ContDiff.ftaylorSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.ftaylorSeries (hf : ContDiff 𝕜 n f) : HasFTaylorSeriesUpTo n f (f
taylorSeries 𝕜 f)
参数：hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
When a function is `C^n`, it admits `ftaylorSeries 𝕜 f` as a Taylor series up
to order `n` in `s`.
-/
theorem ContDiff.ftaylorSeries (hf : ContDiff 𝕜 n f) :
    HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  simp only [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    at hf ⊢
  exact ContDiffOn.ftaylorSeriesWithin hf uniqueDiffOn_univ

/-- For `n : ℕ∞`, a function is `C^n` iff it admits `ftaylorSeries 𝕜 f`
as a Taylor series up to order `n`. -/
/-
**contDiff_iff_ftaylorSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_iff_ftaylorSeries {n : Nat∞} : ContDiff 𝕜 n f ↔ HasFTaylorSeriesU
pTo n f (ftaylorSeries 𝕜 f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `hasFTaylorSeriesUpToOn_univ_iff`：hasFTaylorSeriesUpToOn_univ_iff : HasFT
aylorSeriesUpToOn n f p univ ↔ HasFTaylorSeriesUpTo n f p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ftaylorSeriesWithin_univ`：ftaylorSeriesWithin_univ : ftaylorSeriesWithin
 𝕜 f univ = ftaylorSeries 𝕜 f
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
For `n : ℕ∞`, a function is `C^n` iff it admits `ftaylorSeries 𝕜 f`
as a Taylor series up to order `n`.
-/
theorem contDiff_iff_ftaylorSeries {n : ℕ∞} :
    ContDiff 𝕜 n f ↔ HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  constructor
  · rw [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h ↦ ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · exact fun h ↦ ⟨ftaylorSeries 𝕜 f, h⟩
/-
**contDiff_iff_continuous_differentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_iff_continuous_differentiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (fora
ll m : Nat, m <= n -> Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧ forall m : N
at, m < n -> Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `contDiffOn_iff_continuousOn_differentiableOn`：contDiffOn_iff_continuousO
n_differentiableOn {n : Nat∞} (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (fo
rall m : Nat, m <= n -> Continuous…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_iff_continuous_differentiable {n : ℕ∞} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, m ≤ n → Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, m < n → Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x := by
  simp [contDiffOn_univ.symm, continuousOn_univ, differentiableOn_univ.symm,
    iteratedFDerivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]
/-
**contDiff_nat_iff_continuous_differentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_nat_iff_continuous_differentiable {n : Nat} : ContDiff 𝕜 n f ↔ (f
orall m : Nat, m <= n -> Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧ forall m 
: Nat, m < n -> Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `contDiff_iff_continuous_differentiable`：contDiff_iff_continuous_differen
tiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, m <= n -> Continuous fun x
 => iteratedFDeriv 𝕜 m f x) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_nat_iff_continuous_differentiable {n : ℕ} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, m ≤ n → Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, m < n → Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x := by
  rw [← WithTop.coe_natCast, contDiff_iff_continuous_differentiable]
  simp

/-- If `f` is `C^n` then its `m`-times iterated derivative is continuous for `m ≤ n`. -/
/-
**ContDiff.continuous_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_iteratedFDeriv {m : Nat} (hm : m <= n) (hf : ContDiff 
𝕜 n f) : Continuous fun x => iteratedFDeriv 𝕜 m f x
参数：hm : m <= n；hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_iff_continuous_differentiable`：contDiff_iff_continuous_differen
tiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, m <= n -> Continuous fun x
 => iteratedFDeriv 𝕜 m f x) …
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If `f` is `C^n` then its `m`-times iterated derivative is continuous for `m ≤ n`
.
-/
theorem ContDiff.continuous_iteratedFDeriv {m : ℕ} (hm : m ≤ n) (hf : ContDiff 𝕜 n f) :
    Continuous fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp (hf.of_le hm)).1 m le_rfl

@[fun_prop]
/-
**ContDiff.continuous_iteratedFDeriv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_iteratedFDeriv' {m : Nat} (hf : ContDiff 𝕜 m f) : Cont
inuous fun x => iteratedFDeriv 𝕜 m f x
参数：hf : ContDiff 𝕜 m f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_iff_continuous_differentiable`：contDiff_iff_continuous_differen
tiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, m <= n -> Continuous fun x
 => iteratedFDeriv 𝕜 m f x) …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ContDiff.continuous_iteratedFDeriv' {m : ℕ} (hf : ContDiff 𝕜 m f) :
    Continuous fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp hf).1 m le_rfl

/-- If `f` is `C^n` then its `m`-times iterated derivative is differentiable for `m < n`. -/
/-
**ContDiff.differentiable_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.differentiable_iteratedFDeriv {m : Nat} (hm : m < n) (hf : ContDi
ff 𝕜 n f) : Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x
参数：hm : m < n；hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_iff_continuous_differentiable`：contDiff_iff_continuous_differen
tiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, m <= n -> Continuous fun x
 => iteratedFDeriv 𝕜 m f x) …
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用引理 `ENat.add_one_natCast_le_withTop_of_lt`：add_one_natCast_le_withTop_of_lt 
{m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α

--- 原说明 ---
If `f` is `C^n` then its `m`-times iterated derivative is differentiable for `m 
< n`.
-/
theorem ContDiff.differentiable_iteratedFDeriv {m : ℕ} (hm : m < n) (hf : ContDiff 𝕜 n f) :
    Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp
    (hf.of_le (ENat.add_one_natCast_le_withTop_of_lt hm))).2 m (mod_cast lt_add_one m)
/-
**contDiff_of_differentiable_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_of_differentiable_iteratedFDeriv {n : Nat∞} (h : forall m : Nat, 
m <= n -> Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)) : ContDiff 𝕜 n f
参数：h : forall m : Nat, m <= n -> Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_continuous_differentiable`：contDiff_iff_continuous_differen
tiable {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, m <= n -> Continuous fun x
 => iteratedFDeriv 𝕜 m f x) …
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem contDiff_of_differentiable_iteratedFDeriv {n : ℕ∞}
    (h : ∀ m : ℕ, m ≤ n → Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

/-- A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`. -/
/-
**contDiff_succ_iff_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_succ_iff_fderiv : ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n 
= ω -> AnalyticOnNhd 𝕜 f univ) ∧ ContDiff 𝕜 n (fderiv 𝕜 f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`.
-/
theorem contDiff_succ_iff_fderiv :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω → AnalyticOnNhd 𝕜 f univ) ∧
      ContDiff 𝕜 n (fderiv 𝕜 f) := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ, analyticOn_univ]
/-
**contDiff_one_iff_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_one_iff_fderiv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous
 (fderiv 𝕜 f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `contDiff_succ_iff_fderiv`：contDiff_succ_iff_fderiv : ContDiff 𝕜 (n + 1) 
f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOnNhd 𝕜 f univ) ∧ ContDiff 𝕜 n (fderi
v 𝕜 f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_one_iff_fderiv :
    ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f) := by
  rw [← zero_add 1, contDiff_succ_iff_fderiv]
  simp
/-
**contDiff_infty_iff_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_infty_iff_fderiv : ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff
 𝕜 ∞ (fderiv 𝕜 f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.coe_top_add_one`：↑⊤ + 1 = ↑⊤
· 使用定理 `contDiff_succ_iff_fderiv`：contDiff_succ_iff_fderiv : ContDiff 𝕜 (n + 1) 
f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOnNhd 𝕜 f univ) ∧ ContDiff 𝕜 n (fderi
v 𝕜 f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_infty_iff_fderiv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (fderiv 𝕜 f) := by
  rw [← ENat.coe_top_add_one, contDiff_succ_iff_fderiv]
  simp
/-
**ContDiff.continuous_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : n != 0) : Continuous
 (fderiv 𝕜 f)
参数：h : ContDiff 𝕜 n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_one_iff_fderiv`：contDiff_one_iff_fderiv : ContDiff 𝕜 1 f ↔ Diff
erentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f)
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.one_le_iff_ne_zero_withTop`：one_le_iff_ne_zero_withTop {n : WithTop
 Nat∞} : 1 <= n ↔ n != 0
-/
theorem ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : n ≠ 0) :
    Continuous (fderiv 𝕜 f) :=
  (contDiff_one_iff_fderiv.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)).2

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
/-
**ContDiff.continuous_fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : n != 0) : Cont
inuous fun p : E × E => (fderiv 𝕜 f p.1 : E -> F) p.2
参数：h : ContDiff 𝕜 n f；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContDiff.continuous_fderiv`：ContDiff.continuous_fderiv (h : ContDiff 𝕜 n
 f) (hn : n != 0) : Continuous (fderiv 𝕜 f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df
(x) v`) is
continuous.
-/
theorem ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : n ≠ 0) :
    Continuous fun p : E × E => (fderiv 𝕜 f p.1 : E → F) p.2 :=
  have A : Continuous fun q : (E →L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMap_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prodMk continuous_snd
  A.comp B
