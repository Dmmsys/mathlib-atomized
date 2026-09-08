/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Symmetry of the second derivative

We show that, over the reals, the second derivative is symmetric.

The most precise result is `Convex.second_derivative_within_at_symmetric`. It asserts that,
if a function is differentiable inside a convex set `s` with nonempty interior, and has a second
derivative within `s` at a point `x`, then this second derivative at `x` is symmetric. Note that
this result does not require continuity of the first derivative.

The following particular cases of this statement are especially relevant:

`second_derivative_symmetric_of_eventually` asserts that, if a function is differentiable on a
neighborhood of `x`, and has a second derivative at `x`, then this second derivative is symmetric.

`second_derivative_symmetric` asserts that, if a function is differentiable, and has a second
derivative at `x`, then this second derivative is symmetric.

There statements are given over `ℝ` or `ℂ`, the general version being deduced from the real
version. We also give statements in terms of `fderiv` and `fderivWithin`, called respectively
`ContDiffAt.isSymmSndFDerivAt` and `ContDiffWithinAt.isSymmSndFDerivWithinAt` (the latter
requiring that the point under consideration is accumulated by points in the interior of the set).
These are written using ad hoc predicates `IsSymmSndFDerivAt` and `IsSymmSndFDerivWithinAt`, which
increase readability of statements in differential geometry where they show up a lot.

We also deduce statements over an arbitrary field, requiring that the function is `C^2` if the field
is `ℝ` or `ℂ`, and analytic otherwise. Formally, we assume that the function is `C^n`
with `minSmoothness 𝕜 2 ≤ n`, where `minSmoothness 𝕜 i` is `i` if `𝕜` is `ℝ` or `ℂ`,
and `ω` otherwise.

## Implementation note

For the proof, we obtain an asymptotic expansion to order two of `f (x + v + w) - f (x + v)`, by
using the mean value inequality applied to a suitable function along the
segment `[x + v, x + v + w]`. This expansion involves `f'' ⬝ w` as we move along a segment directed
by `w` (see `Convex.taylor_approx_two_segment`).

Consider the alternate sum `f (x + v + w) + f x - f (x + v) - f (x + w)`, corresponding to the
values of `f` along a rectangle based at `x` with sides `v` and `w`. One can write it using the two
sides directed by `w`, as `(f (x + v + w) - f (x + v)) - (f (x + w) - f x)`. Together with the
previous asymptotic expansion, one deduces that it equals `f'' v w + o(1)` when `v, w` tends to `0`.
Exchanging the roles of `v` and `w`, one instead gets an asymptotic expansion `f'' w v`, from which
the equality `f'' v w = f'' w v` follows.

In our most general statement, we only assume that `f` is differentiable inside a convex set `s`, so
a few modifications have to be made. Since we don't assume continuity of `f` at `x`, we consider
instead the rectangle based at `x + v + w` with sides `v` and `w`,
in `Convex.isLittleO_alternate_sum_square`, but the argument is essentially the same. It only works
when `v` and `w` both point towards the interior of `s`, to make sure that all the sides of the
rectangle are contained in `s` by convexity. The general case follows by linearity, though.
-/

@[expose] public section


open Asymptotics Set Filter

open scoped Topology ContDiff

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s t : Set E} {f : E → F} {x : E}

variable (𝕜) in
/-- Definition recording that a function has a symmetric second derivative within a set at
a point. This is automatic in most cases of interest (open sets over real or complex vector fields,
or general case for analytic functions), but we can express theorems of calculus using this
as a general assumption, and then specialize to these situations. -/
/-
**IsSymmSndFDerivWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSymmSndFDerivWithinAt (f : E -> F) (s : Set E) (x : E) : Prop
参数：f : E -> F；s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition recording that a function has a symmetric second derivative within a 
set at
a point. This is automatic in most cases of interest (open sets over real or com
plex vector fields,
or general case for analytic functions), but we can express theorems of calculus
 using this
as a general assumption, and then specialize to these situations.
-/
def IsSymmSndFDerivWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∀ v w, fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v

variable (𝕜) in
/-- Definition recording that a function has a symmetric second derivative at
a point. This is automatic in most cases of interest (open sets over real or complex vector fields,
or general case for analytic functions), but we can express theorems of calculus using this
as a general assumption, and then specialize to these situations. -/
/-
**IsSymmSndFDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSymmSndFDerivAt (f : E -> F) (x : E) : Prop
参数：f : E -> F；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition recording that a function has a symmetric second derivative at
a point. This is automatic in most cases of interest (open sets over real or com
plex vector fields,
or general case for analytic functions), but we can express theorems of calculus
 using this
as a general assumption, and then specialize to these situations.
-/
def IsSymmSndFDerivAt (f : E → F) (x : E) : Prop :=
  ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v
/-
**IsSymmSndFDerivWithinAt.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsSymmSndFDerivWithinAt`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {F : Ty
pe u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E} {f : E → F} {x : E},
   IsSymmSndFDerivWithinAt 𝕜 f s x →     ∀ (v w : E), ((fderivWithin 𝕜 (fderivWi
thin 𝕜 f s) s x) v) w = ((fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x) w) v
参数：v w : E；(fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x) v；(fderivWithin 𝕜 (fderivWi
thin 𝕜 f s) s x) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsSymmSndFDerivWithinAt.eq (h : IsSymmSndFDerivWithinAt 𝕜 f s x) (v w : E) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x w v :=
  h v w
/-
**IsSymmSndFDerivAt.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsSymmSndFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {F : Ty
pe u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   IsSymmSnd
FDerivAt 𝕜 f x → ∀ (v w : E), ((fderiv 𝕜 (fderiv 𝕜 f) x) v) w = ((fderiv 𝕜 (fder
iv 𝕜 f) x) w) v
参数：v w : E；(fderiv 𝕜 (fderiv 𝕜 f) x) v；(fderiv 𝕜 (fderiv 𝕜 f) x) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsSymmSndFDerivAt.eq
    (h : IsSymmSndFDerivAt 𝕜 f x) (v w : E) :
    fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v :=
  h v w
/-
**fderivWithin_fderivWithin_eq_of_mem_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_fderivWithin_eq_of_mem_nhdsWithin (h : t in 𝓝[s] x) (hf : Con
tDiffWithinAt 𝕜 2 f t x) (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x
 in s) : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 
𝕜 f t) t x
参数：h : t in 𝓝[s] x；hf : ContDiffWithinAt 𝕜 2 f t x；hs : UniqueDiffOn 𝕜 s；ht : Un
iqueDiffOn 𝕜 t；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `ContDiffWithinAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `fderivWithin_of_mem_nhdsWithin`：fderivWithin_of_mem_nhdsWithin [Continuo
usAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
 (st : t in 𝓝[s] x) …
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
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
（共 31 条，此处仅展示前 30 条）
-/
lemma fderivWithin_fderivWithin_eq_of_mem_nhdsWithin (h : t ∈ 𝓝[s] x)
    (hf : ContDiffWithinAt 𝕜 2 f t x) (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x ∈ s) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := by
  have A : ∀ᶠ y in 𝓝[s] x, fderivWithin 𝕜 f s y = fderivWithin 𝕜 f t y := by
    have : ∀ᶠ y in 𝓝[s] x, ContDiffWithinAt 𝕜 2 f t y :=
      nhdsWithin_le_iff.2 h (nhdsWithin_mono _ (subset_insert x t) (hf.eventually (by simp)))
    filter_upwards [self_mem_nhdsWithin, this, eventually_eventually_nhdsWithin.2 h]
      with y hy h'y h''y
    exact fderivWithin_of_mem_nhdsWithin h''y (hs y hy) (h'y.differentiableWithinAt two_ne_zero)
  have : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq A
    exact fderivWithin_of_mem_nhdsWithin h (hs x hx) (hf.differentiableWithinAt two_ne_zero)
  rw [this]
  apply fderivWithin_of_mem_nhdsWithin h (hs x hx)
  exact (hf.fderivWithin_right (m := 1) ht le_rfl
    (mem_of_mem_nhdsWithin hx h)).differentiableWithinAt one_ne_zero
/-
**fderivWithin_fderivWithin_eq_of_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_fderivWithin_eq_of_eventuallyEq (h : s =ᶠ[𝓝 x] t) : fderivWit
hin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq_of_nhds`：Filter.EventuallyEq.fderivW
ithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s
 x
· 使用定理 `fderivWithin_eventually_congr_set`：fderivWithin_eventually_congr_set (h 
: s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t
· 使用定理 `fderivWithin_congr_set`：fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderi
vWithin 𝕜 f s x = fderivWithin 𝕜 f t x
-/
lemma fderivWithin_fderivWithin_eq_of_eventuallyEq (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := calc
  fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x
    = fderivWithin 𝕜 (fderivWithin 𝕜 f t) s x :=
      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
  _ = fderivWithin 𝕜 (fderivWithin 𝕜 f t) t x := fderivWithin_congr_set h
/-
**fderivWithin_fderivWithin_eq_of_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_fderivWithin_eq_of_mem_nhds {f : E -> F} {x : E} {s : Set E} 
(h : s in 𝓝 x) : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderiv 𝕜 (fderiv 𝕜 f)
 x
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `fderivWithin_fderivWithin_eq_of_eventuallyEq`：fderivWithin_fderivWithin_
eq_of_eventuallyEq (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x =
 fderivWithin 𝕜 (fderivWithin 𝕜 f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma fderivWithin_fderivWithin_eq_of_mem_nhds {f : E → F} {x : E} {s : Set E}
    (h : s ∈ 𝓝 x) :
    fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x = fderiv 𝕜 (fderiv 𝕜 f) x := by
  simp only [← fderivWithin_univ]
  apply fderivWithin_fderivWithin_eq_of_eventuallyEq
  simp [h]
/-
**isSymmSndFDerivWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {F : Ty
pe u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {x : E},   IsSymmSnd
FDerivWithinAt 𝕜 f Set.univ x ↔ IsSymmSndFDerivAt 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isSymmSndFDerivWithinAt_univ :
    IsSymmSndFDerivWithinAt 𝕜 f univ x ↔ IsSymmSndFDerivAt 𝕜 f x := by
  simp [IsSymmSndFDerivWithinAt, IsSymmSndFDerivAt]
/-
**IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin (h : IsSymmSndFDerivWithinA
t 𝕜 f t x) (hst : t in 𝓝[s] x) (hf : ContDiffWithinAt 𝕜 2 f t x) (hs : UniqueDif
fOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x in s) : IsSymmSndFDerivWithinAt 𝕜 f s x
参数：h : IsSymmSndFDerivWithinAt 𝕜 f t x；hst : t in 𝓝[s] x；hf : ContDiffWithinAt 𝕜
 2 f t x；hs : UniqueDiffOn 𝕜 s；ht : UniqueDiffOn 𝕜 t；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用引理 `fderivWithin_fderivWithin_eq_of_mem_nhdsWithin`：fderivWithin_fderivWithi
n_eq_of_mem_nhdsWithin (h : t in 𝓝[s] x) (hf : ContDiffWithinAt 𝕜 2 f t x) (hs :
 UniqueDiffOn 𝕜 s) (ht : UniqueDiffO…
-/
theorem IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin (h : IsSymmSndFDerivWithinAt 𝕜 f t x)
    (hst : t ∈ 𝓝[s] x) (hf : ContDiffWithinAt 𝕜 2 f t x)
    (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) (hx : x ∈ s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hst hf hs ht hx]
  exact h v w
/-
**IsSymmSndFDerivWithinAt.congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSymmSndFDerivWithinAt.congr_set (h : IsSymmSndFDerivWithinAt 𝕜 f s x) (h
st : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWithinAt 𝕜 f t x
参数：h : IsSymmSndFDerivWithinAt 𝕜 f s x；hst : s =ᶠ[𝓝 x] t。
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
· 使用引理 `fderivWithin_fderivWithin_eq_of_eventuallyEq`：fderivWithin_fderivWithin_
eq_of_eventuallyEq (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x =
 fderivWithin 𝕜 (fderivWithin 𝕜 f …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem IsSymmSndFDerivWithinAt.congr_set (h : IsSymmSndFDerivWithinAt 𝕜 f s x)
    (hst : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWithinAt 𝕜 f t x := by
  intro v w
  rw [fderivWithin_fderivWithin_eq_of_eventuallyEq hst.symm]
  exact h v w
/-
**isSymmSndFDerivWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSymmSndFDerivWithinAt_congr_set (hst : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWit
hinAt 𝕜 f s x ↔ IsSymmSndFDerivWithinAt 𝕜 f t x
参数：hst : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSymmSndFDerivWithinAt.congr_set`：IsSymmSndFDerivWithinAt.congr_set (h 
: IsSymmSndFDerivWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWithinAt
 𝕜 f t x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem isSymmSndFDerivWithinAt_congr_set (hst : s =ᶠ[𝓝 x] t) :
    IsSymmSndFDerivWithinAt 𝕜 f s x ↔ IsSymmSndFDerivWithinAt 𝕜 f t x :=
  ⟨fun h ↦ h.congr_set hst, fun h ↦ h.congr_set hst.symm⟩
/-
**IsSymmSndFDerivAt.isSymmSndFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSymmSndFDerivAt.isSymmSndFDerivWithinAt (h : IsSymmSndFDerivAt 𝕜 f x) (h
f : ContDiffAt 𝕜 2 f x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : IsSymmSndFDerivW
ithinAt 𝕜 f s x
参数：h : IsSymmSndFDerivAt 𝕜 f x；hf : ContDiffAt 𝕜 2 f x；hs : UniqueDiffOn 𝕜 s；hx 
: x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin`：IsSymmSndFDerivWithinAt.
mono_of_mem_nhdsWithin (h : IsSymmSndFDerivWithinAt 𝕜 f t x) (hst : t in 𝓝[s] x)
 (hf : ContDiffWithinAt 𝕜 2 f t x) (…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem IsSymmSndFDerivAt.isSymmSndFDerivWithinAt (h : IsSymmSndFDerivAt 𝕜 f x)
    (hf : ContDiffAt 𝕜 2 f x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at h hf
  exact h.mono_of_mem_nhdsWithin univ_mem hf hs uniqueDiffOn_univ hx
/-
**isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) (
hx : x in s) : IsSymmSndFDerivWithinAt 𝕜 f s x ↔ (iteratedFDerivWithin 𝕜 2 f s x
).domDomCongr Fin.revPerm = iteratedFDerivWithin 𝕜 2 f s x
参数：hs : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.finZeroElim_eq_zero`：∀ {α : Type u_1} [inst : Zero α], finZeroEli
m = 0
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `Matrix.Fin.cons_vecEmpty`：∀ {α : Type u_1} (x : α), Fin.cons x ![] = ![x
]
· 使用定理 `Matrix.Fin.cons_vecCons`：∀ {n : ℕ} {α : Type u_1} (x y : α) (p : Fin n →
 α),   Fin.cons x (Matrix.vecCons y p) = Matrix.vecCons x (Matrix.vecCons y p)
· 使用定理 `ContinuousMultilinearMap.domDomCongr_apply`：∀ {R : Type u} {ι : Type v} 
{M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   
[inst_2 : AddCommMonoid M₃] [ins…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用引理 `iteratedFDerivWithin_two_apply`：iteratedFDerivWithin_two_apply (f : E ->
 F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s) (m : Fin 2 -> E) : iteratedFDe
rivWithin 𝕜 2 f s z …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.rev_zero`：∀ (n : ℕ), Fin.rev 0 = Fin.last n
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x ↔
      (iteratedFDerivWithin 𝕜 2 f s x).domDomCongr Fin.revPerm =
        iteratedFDerivWithin 𝕜 2 f s x := by
  simp_rw [IsSymmSndFDerivWithinAt, ContinuousMultilinearMap.ext_iff, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi]
  simp [iteratedFDerivWithin_two_apply f hs hx, eq_comm]
/-
**isSymmSndFDerivAt_iff_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSymmSndFDerivAt_iff_iteratedFDeriv : IsSymmSndFDerivAt 𝕜 f x ↔ (iterated
FDeriv 𝕜 2 f x).domDomCongr Fin.revPerm = iteratedFDeriv 𝕜 2 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin`：isSymmSndFDerivWithinA
t_iff_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : IsSymmSndFDer
ivWithinAt 𝕜 f s x ↔ (iteratedFDerivWi…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem isSymmSndFDerivAt_iff_iteratedFDeriv :
    IsSymmSndFDerivAt 𝕜 f x ↔
      (iteratedFDeriv 𝕜 2 f x).domDomCongr Fin.revPerm = iteratedFDeriv 𝕜 2 f x := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ _)
/-
**IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons {x v w : E} {hf : IsSymm
SndFDerivWithinAt 𝕜 f s x} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : iteratedFDeri
vWithin 𝕜 2 f s x ![v, w] = iteratedFDerivWithin 𝕜 2 f s x ![w, v]
参数：hs : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `Fin.rev_zero`：∀ (n : ℕ), Fin.rev 0 = Fin.last n
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMultilinearMap.domDomCongr_apply`：∀ {R : Type u} {ι : Type v} 
{M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   
[inst_2 : AddCommMonoid M₃] [ins…
· 使用定理 `isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin`：isSymmSndFDerivWithinA
t_iff_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : IsSymmSndFDer
ivWithinAt 𝕜 f s x ↔ (iteratedFDerivWi…
-/
theorem IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons {x v w : E}
    {hf : IsSymmSndFDerivWithinAt 𝕜 f s x} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 2 f s x ![v, w] = iteratedFDerivWithin 𝕜 2 f s x ![w, v] := by
  simp_rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx, ContinuousMultilinearMap.ext_iff,
    ContinuousMultilinearMap.domDomCongr_apply] at hf
  convert! hf ![w, v] using 2
  ext i
  fin_cases i <;> simp
/-
**IsSymmSndFDerivAt.iteratedFDeriv_cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSymmSndFDerivAt.iteratedFDeriv_cons {x v w : E} {hf : IsSymmSndFDerivAt 
𝕜 f x} : iteratedFDeriv 𝕜 2 f x ![v, w] = iteratedFDeriv 𝕜 2 f x ![w, v]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsSymmSndFDerivWithinAt.iteratedFDerivWithin_cons`：IsSymmSndFDerivWithin
At.iteratedFDerivWithin_cons {x v w : E} {hf : IsSymmSndFDerivWithinAt 𝕜 f s x} 
(hs : UniqueDiffOn 𝕜 s) (hx : x in s) :…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem IsSymmSndFDerivAt.iteratedFDeriv_cons {x v w : E} {hf : IsSymmSndFDerivAt 𝕜 f x} :
    iteratedFDeriv 𝕜 2 f x ![v, w] = iteratedFDeriv 𝕜 2 f x ![w, v] := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← iteratedFDerivWithin_univ] at *
  exact hf.iteratedFDerivWithin_cons uniqueDiffOn_univ (mem_univ _)

/-- If a function is analytic within a set at a point, then its second derivative is symmetric. -/
/-
**ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega (hf : ContDiffWithinAt 𝕜
 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : IsSymmSndFDerivWithinAt 𝕜 f s 
x
参数：hf : ContDiffWithinAt 𝕜 ω f s x；hs : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin`：isSymmSndFDerivWithinA
t_iff_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : IsSymmSndFDer
ivWithinAt 𝕜 f s x ↔ (iteratedFDerivWi…
· 使用定理 `ContDiffWithinAt.domDomCongr_iteratedFDerivWithin`：ContDiffWithinAt.domD
omCongr_iteratedFDerivWithin (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn
 𝕜 s) (hx : x in s) {n : Nat} (σ : Perm…

--- 原说明 ---
If a function is analytic within a set at a point, then its second derivative is
 symmetric.
-/
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega (hf : ContDiffWithinAt 𝕜 ω f s x)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  rw [isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hs hx]
  exact hf.domDomCongr_iteratedFDerivWithin hs hx _

/-- If a function is analytic at a point, then its second derivative is symmetric. -/
/-
**ContDiffAt.isSymmSndFDerivAt_of_omega** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.isSymmSndFDerivAt_of_omega (hf : ContDiffAt 𝕜 ω f x) : IsSymmSn
dFDerivAt 𝕜 f x
参数：hf : ContDiffAt 𝕜 ω f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt_of_omega`：ContDiffWithinAt.isSy
mmSndFDerivWithinAt_of_omega (hf : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffO
n 𝕜 s) (hx : x in s) : IsSymmSndFDerivW…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
If a function is analytic at a point, then its second derivative is symmetric.
-/
theorem ContDiffAt.isSymmSndFDerivAt_of_omega (hf : ContDiffAt 𝕜 ω f x) :
    IsSymmSndFDerivAt 𝕜 f x := by
  simp only [← isSymmSndFDerivWithinAt_univ, ← contDiffWithinAt_univ] at hf ⊢
  exact hf.isSymmSndFDerivWithinAt_of_omega uniqueDiffOn_univ (mem_univ _)

end General

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {s : Set E} (s_conv : Convex ℝ s) {f : E → F} {f' : E → E →L[ℝ] F}
  {f'' : E →L[ℝ] E →L[ℝ] F} (hf : ∀ x ∈ interior s, HasFDerivAt f (f' x) x) {x : E} (xs : x ∈ s)
  (hx : HasFDerivWithinAt f' f'' (interior s) x)

section
include s_conv hf xs hx

set_option backward.isDefEq.respectTransparency false in
/-- Assume that `f` is differentiable inside a convex set `s`, and that its derivative `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing inside `s`, one can
Taylor-expand to order two the function `f` on the segment `[x + h v, x + h (v + w)]`, giving a
bilinear estimate for `f (x + hv + hw) - f (x + hv)` in terms of `f' w` and of `f'' ⬝ w`, up to
`o(h^2)`.

This is a technical statement used to show that the second derivative is symmetric. -/
/-
**Convex.taylor_approx_two_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.taylor_approx_two_segment {v w : E} (hv : x + v in interior s) (hw 
: x + v + w in interior s) : (fun h : Real => f (x + h • v + h • w) - f (x + h •
 v) - h • f' x w - h ^ 2 • f'' v w - (h ^ 2 / 2) • f'' w w) =o[𝓝[>] 0] fun h => 
h ^ 2
参数：hv : x + v in interior s；hw : x + v + w in interior s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivWithinAt_iff_isLittleO`：hasFDerivWithinAt_iff_isLittleO : HasFD
erivWithinAt f f' s x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' 
=> x' - x)
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
（共 174 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that `f` is differentiable inside a convex set `s`, and that its derivati
ve `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing insi
de `s`, one can
Taylor-expand to order two the function `f` on the segment `[x + h v, x + h (v +
 w)]`, giving a
bilinear estimate for `f (x + hv + hw) - f (x + hv)` in terms of `f' w` and of `
f'' ⬝ w`, up to
`o(h^2)`.

This is a technical statement used to show that the second derivative is symmetr
ic.
-/
theorem Convex.taylor_approx_two_segment {v w : E} (hv : x + v ∈ interior s)
    (hw : x + v + w ∈ interior s) :
    (fun h : ℝ => f (x + h • v + h • w)
        - f (x + h • v) - h • f' x w - h ^ 2 • f'' v w - (h ^ 2 / 2) • f'' w w) =o[𝓝[>] 0]
      fun h => h ^ 2 := by
  -- it suffices to check that the expression is bounded by `ε * ((‖v‖ + ‖w‖) * ‖w‖) * h^2` for
  -- small enough `h`, for any positive `ε`.
  refine IsLittleO.trans_isBigO
    (isLittleO_iff.2 fun ε εpos => ?_) (isBigO_const_mul_self ((‖v‖ + ‖w‖) * ‖w‖) _ _)
  -- consider a ball of radius `δ` around `x` in which the Taylor approximation for `f''` is
  -- good up to `δ`.
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff] at hx
  rcases Metric.mem_nhdsWithin_iff.1 (hx εpos) with ⟨δ, δpos, sδ⟩
  have E1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h * (‖v‖ + ‖w‖) < δ := by
    have : Filter.Tendsto (fun h => h * (‖v‖ + ‖w‖)) (𝓝[>] (0 : ℝ)) (𝓝 (0 * (‖v‖ + ‖w‖))) :=
      (continuous_id.mul continuous_const).continuousWithinAt
    apply (tendsto_order.1 this).2 δ
    simpa only [zero_mul] using δpos
  have E2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), (h : ℝ) < 1 :=
    mem_nhdsWithin_of_mem_nhds <| Iio_mem_nhds zero_lt_one
  filter_upwards [E1, E2, self_mem_nhdsWithin] with h hδ h_lt_1 hpos
  -- we consider `h` small enough that all points under consideration belong to this ball,
  -- and also with `0 < h < 1`.
  replace hpos : 0 < h := hpos
  have xt_mem : ∀ t ∈ Icc (0 : ℝ) 1, x + h • v + (t * h) • w ∈ interior s := by
    intro t ht
    have : x + h • v ∈ interior s := s_conv.add_smul_mem_interior xs hv ⟨hpos, h_lt_1.le⟩
    rw [← smul_smul]
    apply s_conv.interior.add_smul_mem this _ ht
    rw [add_assoc] at hw
    convert! s_conv.add_smul_mem_interior xs hw ⟨hpos, h_lt_1.le⟩ using 1
    module
  -- define a function `g` on `[0,1]` (identified with `[v, v + w]`) such that `g 1 - g 0` is the
  -- quantity to be estimated. We will check that its derivative is given by an explicit
  -- expression `g'`, that we can bound. Then the desired bound for `g 1 - g 0` follows from the
  -- mean value inequality.
  let g t :=
    f (x + h • v + (t * h) • w) - (t * h) • f' x w - (t * h ^ 2) • f'' v w -
      ((t * h) ^ 2 / 2) • f'' w w
  set g' := fun t =>
    f' (x + h • v + (t * h) • w) (h • w) - h • f' x w - h ^ 2 • f'' v w - (t * h ^ 2) • f'' w w
    with hg'
  -- check that `g'` is the derivative of `g`, by a straightforward computation
  have g_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc 0 1) t := by
    intro t ht
    apply_rules [HasDerivWithinAt.sub, HasDerivWithinAt.add]
    · refine (hf _ ?_).comp_hasDerivWithinAt _ ?_
      · exact xt_mem t ht
      apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.const_add, HasDerivAt.smul_const,
        hasDerivAt_mul_const]
    · apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_mul_const]
    · apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_mul_const]
    · suffices H : HasDerivWithinAt (fun u => ((u * h) ^ 2 / 2) • f'' w w)
          ((((2 : ℕ) : ℝ) * (t * h) ^ (2 - 1) * (1 * h) / 2) • f'' w w) (Icc 0 1) t by
        convert H
        ring
      apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_id',
        HasDerivAt.pow, HasDerivAt.mul_const]
  -- check that `g'` is uniformly bounded, with a suitable bound `ε * ((‖v‖ + ‖w‖) * ‖w‖) * h^2`.
  have g'_bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖g' t‖ ≤ ε * ((‖v‖ + ‖w‖) * ‖w‖) * h ^ 2 := by
    intro t ht
    have I : ‖h • v + (t * h) • w‖ ≤ h * (‖v‖ + ‖w‖) :=
      calc
        ‖h • v + (t * h) • w‖ ≤ ‖h • v‖ + ‖(t * h) • w‖ := norm_add_le _ _
        _ = h * ‖v‖ + t * (h * ‖w‖) := by
          simp only [norm_smul, Real.norm_eq_abs, hpos.le, abs_of_nonneg, abs_mul, ht.left,
            mul_assoc]
        _ ≤ h * ‖v‖ + 1 * (h * ‖w‖) := by gcongr; exact ht.2.le
        _ = h * (‖v‖ + ‖w‖) := by ring
    calc
      ‖g' t‖ = ‖(f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)) (h • w)‖ := by
        rw [hg']
        congrm ‖?_‖
        simp only [sub_apply, add_apply, smul_apply, map_add, map_smul]
        module
      _ ≤ ‖f' (x + h • v + (t * h) • w) - f' x - f'' (h • v + (t * h) • w)‖ * ‖h • w‖ :=
        (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ε * ‖h • v + (t * h) • w‖ * ‖h • w‖ := by
        gcongr
        have H : x + h • v + (t * h) • w ∈ Metric.ball x δ ∩ interior s := by
          refine ⟨?_, xt_mem t ⟨ht.1, ht.2.le⟩⟩
          rw [add_assoc, add_mem_ball_iff_norm]
          exact I.trans_lt hδ
        simpa only [mem_ofPred_eq, add_assoc x, add_sub_cancel_left] using sδ H
      _ ≤ ε * (‖h • v‖ + ‖h • w‖) * ‖h • w‖ := by
        gcongr
        apply (norm_add_le _ _).trans
        gcongr
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg, ht.1, hpos.le, mul_assoc]
        exact mul_le_of_le_one_left (by positivity) ht.2.le
      _ = ε * ((‖v‖ + ‖w‖) * ‖w‖) * h ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg, hpos.le]; ring
  -- conclude using the mean value inequality
  have I : ‖g 1 - g 0‖ ≤ ε * ((‖v‖ + ‖w‖) * ‖w‖) * h ^ 2 := by
    simpa only [mul_one, sub_zero] using
      norm_image_sub_le_of_norm_deriv_le_segment' g_deriv g'_bound 1 (right_mem_Icc.2 zero_le_one)
  convert! I using 1
  · congr 1
    simp only [g, add_zero, one_mul, zero_div, zero_mul, sub_zero,
      zero_smul, Ne, not_false_iff, zero_pow, reduceCtorEq]
    abel
  · simp (discharger := positivity) only [Real.norm_eq_abs, abs_of_nonneg]
    ring

/-- One can get `f'' v w` as the limit of `h ^ (-2)` times the alternate sum of the values of `f`
along the vertices of a quadrilateral with sides `h v` and `h w` based at `x`.
In a setting where `f` is not guaranteed to be continuous at `f`, we can still
get this if we use a quadrilateral based at `h v + h w`. -/
/-
**Convex.isLittleO_alternate_sum_square** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.isLittleO_alternate_sum_square {v w : E} (h4v : x + (4 : Real) • v 
in interior s) (h4w : x + (4 : Real) • w in interior s) : (fun h : Real => f (x 
+ h • (2 • v + 2 • w)) + f (x + h • (v + w)) - f (x + h • (2 • v + w)) - f (x + 
h • (v + 2 • w)) - h ^ 2 • f'' v w) =o[𝓝[>] 0] fun h => h ^ 2
参数：h4v : x + (4 : Real) • v in interior s；h4w : x + (4 : Real) • w in interior s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
（共 100 条，此处仅展示前 30 条）

--- 原说明 ---
One can get `f'' v w` as the limit of `h ^ (-2)` times the alternate sum of the 
values of `f`
along the vertices of a quadrilateral with sides `h v` and `h w` based at `x`.
In a setting where `f` is not guaranteed to be continuous at `f`, we can still
get this if we use a quadrilateral based at `h v + h w`.
-/
theorem Convex.isLittleO_alternate_sum_square {v w : E} (h4v : x + (4 : ℝ) • v ∈ interior s)
    (h4w : x + (4 : ℝ) • w ∈ interior s) :
    (fun h : ℝ => f (x + h • (2 • v + 2 • w)) + f (x + h • (v + w))
        - f (x + h • (2 • v + w)) - f (x + h • (v + 2 • w)) - h ^ 2 • f'' v w) =o[𝓝[>] 0]
      fun h => h ^ 2 := by
  have A : (1 : ℝ) / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by simp, by norm_num⟩
  have B : (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by simp, by norm_num⟩
  have h2v2w : x + (2 : ℝ) • v + (2 : ℝ) • w ∈ interior s := by
    convert! s_conv.interior.add_smul_sub_mem h4v h4w B using 1
    module
  have h2vww : x + (2 • v + w) + w ∈ interior s := by
    convert! h2v2w using 1
    module
  have h2v : x + (2 : ℝ) • v ∈ interior s := by
    convert! s_conv.add_smul_sub_mem_interior xs h4v A using 1
    module
  have h2w : x + (2 : ℝ) • w ∈ interior s := by
    convert! s_conv.add_smul_sub_mem_interior xs h4w A using 1
    module
  have hvw : x + (v + w) ∈ interior s := by
    convert! s_conv.add_smul_sub_mem_interior xs h2v2w A using 1
    module
  have h2vw : x + (2 • v + w) ∈ interior s := by
    convert! s_conv.interior.add_smul_sub_mem h2v h2v2w B using 1
    module
  have hvww : x + (v + w) + w ∈ interior s := by
    convert! s_conv.interior.add_smul_sub_mem h2w h2v2w B using 1
    module
  have TA1 := s_conv.taylor_approx_two_segment hf xs hx h2vw h2vww
  have TA2 := s_conv.taylor_approx_two_segment hf xs hx hvw hvww
  convert! TA1.sub TA2 using 1
  ext h
  simp only [two_smul, smul_add, ← add_assoc, map_add,
    add_apply]
  abel

/-- Assume that `f` is differentiable inside a convex set `s`, and that its derivative `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing inside `s`, one
has `f'' v w = f'' w v`. Superseded by `Convex.second_derivative_within_at_symmetric`, which
removes the assumption that `v` and `w` point inside `s`. -/
/-
**Convex.second_derivative_within_at_symmetric_of_mem_interior** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：Convex.second_derivative_within_at_symmetric_of_mem_interior {v w : E} (h4
v : x + (4 : Real) • v in interior s) (h4w : x + (4 : Real) • w in interior s) :
 f'' w v = f'' v w
参数：h4v : x + (4 : Real) • v in interior s；h4w : x + (4 : Real) • w in interior s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.Symmetric.0.Convex.second_deri
vative_within_at_symmetric_of_mem_interior._abel_1_1`：∀ {E : Type u_2} {F : Type
 u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedA
ddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Convex.isLittleO_alternate_sum_square`：Convex.isLittleO_alternate_sum_sq
uare {v w : E} (h4v : x + (4 : Real) • v in interior s) (h4w : x + (4 : Real) • 
w in interior s) : (fun h :…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsBigO.smul_isLittleO`：∀ {α : Type u_1} {E' : Type u_6} {F' 
: Type u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E'] 
  [inst_1 : SeminormedA…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that `f` is differentiable inside a convex set `s`, and that its derivati
ve `f'` is
differentiable at a point `x`. Then, given two vectors `v` and `w` pointing insi
de `s`, one
has `f'' v w = f'' w v`. Superseded by `Convex.second_derivative_within_at_symme
tric`, which
removes the assumption that `v` and `w` point inside `s`.
-/
theorem Convex.second_derivative_within_at_symmetric_of_mem_interior {v w : E}
    (h4v : x + (4 : ℝ) • v ∈ interior s) (h4w : x + (4 : ℝ) • w ∈ interior s) :
    f'' w v = f'' v w := by
  have A : (fun h : ℝ => h ^ 2 • (f'' w v - f'' v w)) =o[𝓝[>] 0] fun h => h ^ 2 := by
    convert!
      (s_conv.isLittleO_alternate_sum_square hf xs hx h4v h4w).sub
        (s_conv.isLittleO_alternate_sum_square hf xs hx h4w h4v) using 1
    ext h
    simp only [add_comm, smul_add, smul_sub]
    abel
  have B : (fun _ : ℝ => f'' w v - f'' v w) =o[𝓝[>] 0] fun _ => (1 : ℝ) := by
    have : (fun h : ℝ => 1 / h ^ 2) =O[𝓝[>] 0] fun h => 1 / h ^ 2 := isBigO_refl _ _
    have C := this.smul_isLittleO A
    apply C.congr' _ _
    · filter_upwards [self_mem_nhdsWithin]
      intro h (hpos : 0 < h)
      match_scalars <;> field
    · filter_upwards [self_mem_nhdsWithin] with h (hpos : 0 < h)
      simp [field]
  simpa only [sub_eq_zero] using isLittleO_const_const_iff.1 B

end

set_option backward.isDefEq.respectTransparency false in
/-- If a function is differentiable inside a convex set with nonempty interior, and has a second
derivative at a point of this convex set, then this second derivative is symmetric. -/
/-
**Convex.second_derivative_within_at_symmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.second_derivative_within_at_symmetric {s : Set E} (s_conv : Convex 
Real s) (hne : (interior s).Nonempty) {f : E -> F} {f' : E -> E ->L[Real] F} {f'
' : E ->L[Real] E ->L[Real] F} (hf : forall x in interior s, HasFDerivAt f (f' x
) x) {x : E} (xs : x in s) (hx : HasFDerivWithinAt f' f'' (interior s) x) (v w :
 E) : f'' v w = f'' w v
参数：s_conv : Convex Real s；hne : (interior s).Nonempty；hf : forall x in interior 
s, HasFDerivAt f (f' x) x；xs : x in s；hx : HasFDerivWithinAt f' f'' (interior s)
 x；v w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousAt.smul`：ContinuousAt.smul (hf : ContinuousAt f b) (hg : Conti
nuousAt g b) : ContinuousAt (f • g) b
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_mem_nhds`：interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x
（共 112 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is differentiable inside a convex set with nonempty interior, and 
has a second
derivative at a point of this convex set, then this second derivative is symmetr
ic.
-/
theorem Convex.second_derivative_within_at_symmetric {s : Set E} (s_conv : Convex ℝ s)
    (hne : (interior s).Nonempty) {f : E → F} {f' : E → E →L[ℝ] F} {f'' : E →L[ℝ] E →L[ℝ] F}
    (hf : ∀ x ∈ interior s, HasFDerivAt f (f' x) x) {x : E} (xs : x ∈ s)
    (hx : HasFDerivWithinAt f' f'' (interior s) x) (v w : E) : f'' v w = f'' w v := by
  /- we work around a point `x + 4 z` in the interior of `s`. For any vector `m`,
    then `x + 4 (z + t m)` also belongs to the interior of `s` for small enough `t`. This means that
    we will be able to apply `second_derivative_within_at_symmetric_of_mem_interior` to show
    that `f''` is symmetric, after cancelling all the contributions due to `z`. -/
  rcases hne with ⟨y, hy⟩
  obtain ⟨z, hz⟩ : ∃ z, z = ((1 : ℝ) / 4) • (y - x) := ⟨((1 : ℝ) / 4) • (y - x), rfl⟩
  have A : ∀ m : E, Filter.Tendsto (fun t : ℝ => x + (4 : ℝ) • (z + t • m)) (𝓝 0) (𝓝 y) := by
    intro m
    have : x + (4 : ℝ) • (z + (0 : ℝ) • m) = y := by simp [hz]
    rw [← this]
    refine tendsto_const_nhds.add <| tendsto_const_nhds.smul <| tendsto_const_nhds.add ?_
    exact continuousAt_id.smul continuousAt_const
  have B : ∀ m : E, ∀ᶠ t in 𝓝[>] (0 : ℝ), x + (4 : ℝ) • (z + t • m) ∈ interior s := by
    intro m
    apply nhdsWithin_le_nhds
    apply A m
    rw [mem_interior_iff_mem_nhds] at hy
    exact interior_mem_nhds.2 hy
  -- we choose `t m > 0` such that `x + 4 (z + (t m) m)` belongs to the interior of `s`, for any
  -- vector `m`.
  choose t ts tpos using fun m => ((B m).and self_mem_nhdsWithin).exists
  -- applying `second_derivative_within_at_symmetric_of_mem_interior` to the vectors `z`
  -- and `z + (t m) m`, we deduce that `f'' m z = f'' z m` for all `m`.
  have C : ∀ m : E, f'' m z = f'' z m := by
    intro m
    have : f'' (z + t m • m) (z + t 0 • (0 : E)) = f'' (z + t 0 • (0 : E)) (z + t m • m) :=
      s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts 0) (ts m)
    simp only [map_add, map_smul, add_right_inj, add_apply, smul_apply, add_zero, smul_zero] at this
    exact smul_right_injective F (tpos m).ne' this
  -- applying `second_derivative_within_at_symmetric_of_mem_interior` to the vectors `z + (t v) v`
  -- and `z + (t w) w`, we deduce that `f'' v w = f'' w v`. Cross terms involving `z` can be
  -- eliminated thanks to the fact proved above that `f'' m z = f'' z m`.
  have : f'' (z + t v • v) (z + t w • w) = f'' (z + t w • w) (z + t v • v) :=
    s_conv.second_derivative_within_at_symmetric_of_mem_interior hf xs hx (ts w) (ts v)
  simp only [map_add, map_smul, add_apply, smul_apply, C] at this
  have : (t v * t w) • (f'' v) w = (t v * t w) • (f'' w) v := by
    linear_combination (norm := module) this
  apply smul_right_injective F _ this
  simp [(tpos v).ne', (tpos w).ne']

/-- If a function is differentiable around `x`, and has two derivatives at `x`, then the second
derivative is symmetric. Version over `ℝ`. See `second_derivative_symmetric_of_eventually` for a
version over `ℝ` or `ℂ`. -/
/-
**second_derivative_symmetric_of_eventually_of_real** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：second_derivative_symmetric_of_eventually_of_real {f : E -> F} {f' : E -> 
E ->L[Real] F} {f'' : E ->L[Real] E ->L[Real] F} (hf : forallᶠ y in 𝓝 x, HasFDer
ivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v
参数：hf : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y；hx : HasFDerivAt f' f'' x；v w :
 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `Convex.second_derivative_within_at_symmetric`：Convex.second_derivative_w
ithin_at_symmetric {s : Set E} (s_conv : Convex Real s) (hne : (interior s).None
mpty) {f : E -> F} {f' : E -> E ->…
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x

--- 原说明 ---
If a function is differentiable around `x`, and has two derivatives at `x`, then
 the second
derivative is symmetric. Version over `ℝ`. See `second_derivative_symmetric_of_e
ventually` for a
version over `ℝ` or `ℂ`.
-/
theorem second_derivative_symmetric_of_eventually_of_real {f : E → F} {f' : E → E →L[ℝ] F}
    {f'' : E →L[ℝ] E →L[ℝ] F} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x)
    (v w : E) : f'' v w = f'' w v := by
  rcases Metric.mem_nhds_iff.1 hf with ⟨ε, εpos, hε⟩
  have A : (interior (Metric.ball x ε)).Nonempty := by
    rwa [Metric.isOpen_ball.interior_eq, Metric.nonempty_ball]
  exact
    Convex.second_derivative_within_at_symmetric (convex_ball x ε) A
      (fun y hy => hε (interior_subset hy)) (Metric.mem_ball_self εpos) hx.hasFDerivWithinAt v w

end Real

section IsRCLikeNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {s : Set E} {f : E → F} {x : E}

set_option backward.isDefEq.respectTransparency false in
/-
**second_derivative_symmetric_of_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：second_derivative_symmetric_of_eventually [IsRCLikeNormedField 𝕜] {f' : E 
-> E ->L[𝕜] F} {x : E} {f'' : E ->L[𝕜] E ->L[𝕜] F} (hf : forallᶠ y in 𝓝 x, HasFD
erivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v
参数：hf : forallᶠ y in 𝓝 x, HasFDerivAt f (f' y) y；hx : HasFDerivAt f' f'' x；v w :
 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `second_derivative_symmetric_of_eventually_of_real`：second_derivative_sym
metric_of_eventually_of_real {f : E -> F} {f' : E -> E ->L[Real] F} {f'' : E ->L
[Real] E ->L[Real] F} (hf : forallᶠ y i…
-/
theorem second_derivative_symmetric_of_eventually [IsRCLikeNormedField 𝕜]
    {f' : E → E →L[𝕜] F} {x : E}
    {f'' : E →L[𝕜] E →L[𝕜] F} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v := by
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let _ : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  let f'R : E → E →L[ℝ] F := fun x ↦ (f' x).restrictScalars ℝ
  let f''R : E →L[ℝ] E →L[ℝ] F := f''.bilinearRestrictScalars ℝ
  have hfR : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f'R y) y := by
    filter_upwards [hf] with y hy using HasFDerivAt.restrictScalars ℝ hy
  have : HasFDerivAt f'R f''R x := by
    simp only [hasFDerivAt_iff_tendsto] at hx ⊢
    exact hx
  change f''R v w = f''R w v
  exact second_derivative_symmetric_of_eventually_of_real hfR this v w

/-- If a function is differentiable, and has two derivatives at `x`, then the second
derivative is symmetric. -/
/-
**second_derivative_symmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：second_derivative_symmetric [IsRCLikeNormedField 𝕜] {f' : E -> E ->L[𝕜] F}
 {f'' : E ->L[𝕜] E ->L[𝕜] F} {x : E} (hf : forall y, HasFDerivAt f (f' y) y) (hx
 : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v
参数：hf : forall y, HasFDerivAt f (f' y) y；hx : HasFDerivAt f' f'' x；v w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `second_derivative_symmetric_of_eventually`：second_derivative_symmetric_o
f_eventually [IsRCLikeNormedField 𝕜] {f' : E -> E ->L[𝕜] F} {x : E} {f'' : E ->L
[𝕜] E ->L[𝕜] F} (hf : forallᶠ y…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If a function is differentiable, and has two derivatives at `x`, then the second
derivative is symmetric.
-/
theorem second_derivative_symmetric [IsRCLikeNormedField 𝕜]
    {f' : E → E →L[𝕜] F} {f'' : E →L[𝕜] E →L[𝕜] F} {x : E}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hx : HasFDerivAt f' f'' x) (v w : E) : f'' v w = f'' w v :=
  second_derivative_symmetric_of_eventually (Filter.Eventually.of_forall hf) hx v w

open scoped Classical in
variable (𝕜) in
/-- `minSmoothness 𝕜 n` is the minimal smoothness exponent larger than or equal to `n` for which
one can do serious calculus in `𝕜`. If `𝕜` is `ℝ` or `ℂ`, this is just `n`. Otherwise,
this is `ω` as only analytic functions are well behaved on `ℚₚ`, say. -/
noncomputable irreducible_def minSmoothness (n : ℕ∞ω) :=
  if IsRCLikeNormedField 𝕜 then n else ω

/-
**minSmoothness_of_isRCLikeNormedField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [h : IsRCLikeNormedFie
ld 𝕜] {n : WithTop ℕ∞}, minSmoothness 𝕜 n = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minSmoothness_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] (
n : WithTop ℕ∞),   minSmoothness 𝕜 n = if IsRCLikeNormedField 𝕜 then n else ⊤
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma minSmoothness_of_isRCLikeNormedField [h : IsRCLikeNormedField 𝕜] {n : ℕ∞ω} :
    minSmoothness 𝕜 n = n := by
  simp [minSmoothness, h]
/-
**le_minSmoothness** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minSmoothness_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] (
n : WithTop ℕ∞),   minSmoothness 𝕜 n = if IsRCLikeNormedField 𝕜 then n else ⊤
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma le_minSmoothness {n : ℕ∞ω} : n ≤ minSmoothness 𝕜 n := by
  simp only [minSmoothness]
  split_ifs <;> simp
/-
**minSmoothness_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minSmoothness_add {n m : Nat∞ω} : minSmoothness 𝕜 (n + m) = minSmoothness 
𝕜 n + m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minSmoothness_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] (
n : WithTop ℕ∞),   minSmoothness 𝕜 n = if IsRCLikeNormedField 𝕜 then n else ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma minSmoothness_add {n m : ℕ∞ω} : minSmoothness 𝕜 (n + m) = minSmoothness 𝕜 n + m := by
  simp only [minSmoothness]
  split_ifs <;> simp
/-
**minSmoothness_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minSmoothness_monotone : Monotone (minSmoothness 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minSmoothness_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] (
n : WithTop ℕ∞),   minSmoothness 𝕜 n = if IsRCLikeNormedField 𝕜 then n else ⊤
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma minSmoothness_monotone : Monotone (minSmoothness 𝕜) := by
  intro m n hmn
  simp only [minSmoothness]
  split_ifs <;> simp [hmn]
/-
**minSmoothness_eq_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {n : WithTop ℕ∞},   mi
nSmoothness 𝕜 n = ↑⊤ ↔ n = ↑⊤ ∧ IsRCLikeNormedField 𝕜
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minSmoothness_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] (
n : WithTop ℕ∞),   minSmoothness 𝕜 n = if IsRCLikeNormedField 𝕜 then n else ⊤
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
@[simp] lemma minSmoothness_eq_infty {n : ℕ∞ω} :
    minSmoothness 𝕜 n = ∞ ↔ (n = ∞ ∧ IsRCLikeNormedField 𝕜) := by
  simp only [minSmoothness]
  split_ifs with h <;> simp [h]

/-- If `minSmoothness 𝕜 m ≤ n` for some (finite) integer `m`, then one can
find `n' ∈ [minSmoothness 𝕜 m, n]` which is not `∞`: over `ℝ` or `ℂ`, just take `m`, and otherwise
just take `ω`. The interest of this technical lemma is that, if a function is `C^{n'}` at a point
for `n' ≠ ∞`, then it is `C^{n'}` on a neighborhood of the point (this property fails only
in `C^∞` smoothness, see `ContDiffWithinAt.contDiffOn`). -/
/-
**exist_minSmoothness_le_ne_infty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exist_minSmoothness_le_ne_infty {n : Nat∞ω} {m : Nat} (hm : minSmoothness 
𝕜 m <= n) : exists n', minSmoothness 𝕜 m <= n' ∧ n' <= n ∧ n' != ∞
参数：hm : minSmoothness 𝕜 m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minSmoothness_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] (
n : WithTop ℕ∞),   minSmoothness 𝕜 n = if IsRCLikeNormedField 𝕜 then n else ⊤
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
If `minSmoothness 𝕜 m ≤ n` for some (finite) integer `m`, then one can
find `n' ∈ [minSmoothness 𝕜 m, n]` which is not `∞`: over `ℝ` or `ℂ`, just take 
`m`, and otherwise
just take `ω`. The interest of this technical lemma is that, if a function is `C
^{n'}` at a point
for `n' ≠ ∞`, then it is `C^{n'}` on a neighborhood of the point (this property 
fails only
in `C^∞` smoothness, see `ContDiffWithinAt.contDiffOn`).
-/
lemma exist_minSmoothness_le_ne_infty {n : ℕ∞ω} {m : ℕ} (hm : minSmoothness 𝕜 m ≤ n) :
    ∃ n', minSmoothness 𝕜 m ≤ n' ∧ n' ≤ n ∧ n' ≠ ∞ := by
  simp only [minSmoothness] at hm ⊢
  split_ifs with h
  · simp only [h, ↓reduceIte] at hm
    exact ⟨m, le_rfl, hm, by simp⟩
  · simp only [h, ↓reduceIte] at hm
    refine ⟨ω, le_rfl, by simp [hm], by simp⟩

/-- If a function is `C^2` at a point, then its second derivative there is symmetric. Over a field
different from `ℝ` or `ℂ`, we should require that the function is analytic. -/
/-
**ContDiffAt.isSymmSndFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.isSymmSndFDerivAt {n : Nat∞ω} (hf : ContDiffAt 𝕜 n f x) (hn : m
inSmoothness 𝕜 2 <= n) : IsSymmSndFDerivAt 𝕜 f x
参数：hf : ContDiffAt 𝕜 n f x；hn : minSmoothness 𝕜 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `second_derivative_symmetric_of_eventually`：second_derivative_symmetric_o
f_eventually [IsRCLikeNormedField 𝕜] {f' : E -> E ->L[𝕜] F} {x : E} {f'' : E ->L
[𝕜] E ->L[𝕜] F} (hf : forallᶠ y…
· 使用定理 `ContDiffAt.contDiffOn`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type uF} […
· 使用定理 `ContDiffAt.of_le`：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= 
n) : ContDiffAt 𝕜 m f x
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minSmoothness_of_isRCLikeNormedField`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] [h : IsRCLikeNormedField 𝕜] {n : WithTop ℕ∞}, minSmoothness 𝕜 
n = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.fderiv_right`：ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f 
x₀) (hmn : m + 1 <= n) : ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is `C^2` at a point, then its second derivative there is symmetric
. Over a field
different from `ℝ` or `ℂ`, we should require that the function is analytic.
-/
theorem ContDiffAt.isSymmSndFDerivAt {n : ℕ∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 ≤ n) : IsSymmSndFDerivAt 𝕜 f x := by
  by_cases h : IsRCLikeNormedField 𝕜
  -- First deal with the `ℝ` or `ℂ` case, where `C^2` is enough.
  · intro v w
    apply second_derivative_symmetric_of_eventually (f := f) (f' := fderiv 𝕜 f) (x := x)
    · obtain ⟨u, hu, h'u⟩ : ∃ u ∈ 𝓝 x, ContDiffOn 𝕜 2 f u :=
        (hf.of_le hn).contDiffOn (m := 2) le_minSmoothness (by simp)
      rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, xv⟩
      filter_upwards [v_open.mem_nhds xv] with y hy
      have : DifferentiableAt 𝕜 f y := by
        have := (h'u.mono vu y hy).contDiffAt (v_open.mem_nhds hy)
        exact this.differentiableAt two_ne_zero
      exact DifferentiableAt.hasFDerivAt this
    · have : DifferentiableAt 𝕜 (fderiv 𝕜 f) x := by
        apply ContDiffAt.differentiableAt _ one_ne_zero
        exact hf.fderiv_right (le_minSmoothness.trans hn)
      exact DifferentiableAt.hasFDerivAt this
  -- then deal with the case of an arbitrary field, with analytic functions.
  · simp only [minSmoothness, h, ↓reduceIte, top_le_iff] at hn
    apply ContDiffAt.isSymmSndFDerivAt_of_omega
    simpa [hn] using hf

/-- If a function is `C^2` within a set at a point, and accumulated by points in the interior
of the set, then its second derivative there is symmetric. Over a field
different from `ℝ` or `ℂ`, we should require that the function is analytic. -/
/-
**ContDiffWithinAt.isSymmSndFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.isSymmSndFDerivWithinAt {n : Nat∞ω} (hf : ContDiffWithinA
t 𝕜 n f s x) (hn : minSmoothness 𝕜 2 <= n) (hs : UniqueDiffOn 𝕜 s) (hx : x in cl
osure (interior s)) (h'x : x in s) : IsSymmSndFDerivWithinAt 𝕜 f s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hn : minSmoothness 𝕜 2 <= n；hs : UniqueDiffOn
 𝕜 s；hx : x in closure (interior s)；h'x : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `exist_minSmoothness_le_ne_infty`：exist_minSmoothness_le_ne_infty {n : Na
t∞ω} {m : Nat} (hm : minSmoothness 𝕜 m <= n) : exists n', minSmoothness 𝕜 m <= n
' ∧ n' <= n ∧ n' != ∞
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_seq_limit`：mem_closure_iff_seq_limit [FrechetUrysohnSpac
e X] {s : Set X} {a : X} : a in closure s ↔ exists x : Nat -> X, (forall n : Nat
, x n in s) ∧ T…
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `ContDiffAt.isSymmSndFDerivAt`：ContDiffAt.isSymmSndFDerivAt {n : Nat∞ω} (
hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 <= n) : IsSymmSndFDerivAt 𝕜 f x
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is `C^2` within a set at a point, and accumulated by points in the
 interior
of the set, then its second derivative there is symmetric. Over a field
different from `ℝ` or `ℂ`, we should require that the function is analytic.
-/
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt {n : ℕ∞ω}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s)) (h'x : x ∈ s) :
    IsSymmSndFDerivWithinAt 𝕜 f s x := by
  /- We argue that, at interior points, the second derivative is symmetric, and moreover by
  continuity it converges to the second derivative at `x`. Therefore, the latter is also
  symmetric. -/
  obtain ⟨m, hm, hmn, m_ne⟩ := exist_minSmoothness_le_ne_infty hn
  rcases (hf.of_le hmn).contDiffOn' le_rfl (by simp [m_ne]) with ⟨u, u_open, xu, hu⟩
  simp only [insert_eq_of_mem h'x] at hu
  have h'u : UniqueDiffOn 𝕜 (s ∩ u) := hs.inter u_open
  obtain ⟨y, hy, y_lim⟩ : ∃ y, (∀ (n : ℕ), y n ∈ interior s) ∧ Tendsto y atTop (𝓝 x) :=
    mem_closure_iff_seq_limit.1 hx
  have L : ∀ᶠ k in atTop, y k ∈ u := y_lim (u_open.mem_nhds xu)
  have I : ∀ᶠ k in atTop, IsSymmSndFDerivWithinAt 𝕜 f s (y k) := by
    filter_upwards [L] with k hk
    have s_mem : s ∈ 𝓝 (y k) := by
      apply mem_of_superset (isOpen_interior.mem_nhds (hy k))
      exact interior_subset
    have : IsSymmSndFDerivAt 𝕜 f (y k) := by
      apply ContDiffAt.isSymmSndFDerivAt _ (n := m) hm
      apply (hu (y k) ⟨(interior_subset (hy k)), hk⟩).contDiffAt
      exact inter_mem s_mem (u_open.mem_nhds hk)
    intro v w
    rw [fderivWithin_fderivWithin_eq_of_mem_nhds s_mem]
    exact this v w
  have A : ContinuousOn (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s) (s ∩ u) := by
    have : ContinuousOn (fderivWithin 𝕜 (fderivWithin 𝕜 f (s ∩ u)) (s ∩ u)) (s ∩ u) :=
      ((hu.fderivWithin h'u (m := 1) (le_minSmoothness.trans hm)).fderivWithin h'u
      (m := 0) le_rfl).continuousOn
    apply this.congr
    intro y hy
    apply fderivWithin_fderivWithin_eq_of_eventuallyEq
    filter_upwards [u_open.mem_nhds hy.2] with z hz
    change (z ∈ s) = (z ∈ s ∩ u)
    simp_all
  have B : Tendsto (fun k ↦ fderivWithin 𝕜 (fderivWithin 𝕜 f s) s (y k)) atTop
      (𝓝 (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x)) := by
    have : Tendsto y atTop (𝓝[s ∩ u] x) := by
      apply tendsto_nhdsWithin_iff.2 ⟨y_lim, ?_⟩
      filter_upwards [L] with k hk using ⟨interior_subset (hy k), hk⟩
    exact (A x ⟨h'x, xu⟩ ).tendsto.comp this
  have C (v w : E) : Tendsto (fun k ↦ fderivWithin 𝕜 (fderivWithin 𝕜 f s) s (y k) v w) atTop
      (𝓝 (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w)) := by
    have : Continuous (fun (A : E →L[𝕜] E →L[𝕜] F) ↦ A v w) := by fun_prop
    exact (this.tendsto _).comp B
  have C' (v w : E) : Tendsto (fun k ↦ fderivWithin 𝕜 (fderivWithin 𝕜 f s) s (y k) w v) atTop
      (𝓝 (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v w)) := by
    apply (C v w).congr'
    filter_upwards [I] with k hk using hk v w
  intro v w
  exact tendsto_nhds_unique (C v w) (C' w v)

end IsRCLikeNormedField

