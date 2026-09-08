/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Higher differentiability of composition

We prove that the composition of `C^n` functions is `C^n`.
We also expand the API around `C^n` functions.

## Main results

* `ContDiff.comp` states that the composition of two `C^n` functions is `C^n`.

Similar results are given for `C^n` functions on domains.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Filter Function

open scoped Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {m n : ℕ∞ω}

section comp

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to do this would be to
use the following simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There are two difficulties in this proof.

The first one is that it is an induction over all Banach
spaces. In Lean, this is only possible if they belong to a fixed universe. One could formalize this
by first proving the statement in this case, and then extending the result to general universes
by embedding all the spaces we consider in a common universe through `ULift`.

The second one is that it does not work cleanly for analytic maps: for this case, we need to
exhibit a whole sequence of derivatives which are all analytic, not just finitely many of them, so
an induction is never enough at a finite step.

Both these difficulties can be overcome with some cost. However, we choose a different path: we
write down an explicit formula for the `n`-th derivative of `g ∘ f` in terms of derivatives of
`g` and `f` (this is the formula of Faa-Di Bruno) and use this formula to get a suitable Taylor
expansion for `g ∘ f`. Writing down the formula of Faa-Di Bruno is not easy as the formula is quite
intricate, but it is also useful for other purposes and once available it makes the proof here
essentially trivial.
-/

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
/-
**ContDiffWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x
 : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (s
t : MapsTo f s t) : ContDiffWithinAt 𝕜 n (g ∘ f) s x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；st 
: MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin'`：ContinuousWithinAt.preimage
_mem_nhdsWithin' {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝[f '' s]
 f x) : f ⁻¹' t in 𝓝[s] x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_insert_self`：continuousWithinAt_insert_self : Continu
ousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `HasFTaylorSeriesUpToOn.comp`：HasFTaylorSeriesUpToOn.comp {n : WithTop Na
t∞} {g : F -> G} {f : E -> F} (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTa
ylorSeriesUpToOn …
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticOn.congr`：AnalyticOn.congr {f g : E -> F} {s : Set E} (hf : Anal
yticOn 𝕜 f s) (hs : EqOn g f s) : AnalyticOn 𝕜 g s
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq'`：HasFTaylorSeriesUpToOn.zero_eq' (h : Ha
sFTaylorSeriesUpToOn n f p s) {x : E} (hx : x in s) : p x 0 = (continuousMultili
nearCurryFin0 𝕜 E F).…
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `LinearIsometryEquiv.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `analyticOn_taylorComp`：analyticOn_taylorComp (hq : forall (n : Nat), Ana
lyticOn 𝕜 (fun x => q x n) t) (hp : forall n, AnalyticOn 𝕜 (fun x => p x n) s) {
f : E -> F}…

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`.
-/
theorem ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (st : MapsTo f s t) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  match n with
  | ω =>
    have h'f : ContDiffWithinAt 𝕜 ω f s x := hf
    obtain ⟨u, hu, p, hp, h'p⟩ := h'f
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    let w := insert x s ∩ (u ∩ f ⁻¹' v)
    have wv : w ⊆ f ⁻¹' v := fun y hy => hy.2.2
    have wu : w ⊆ u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y ↦ (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv, ?_⟩
    · apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
      apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
      apply nhdsWithin_mono _ _ hv
      simp only [image_insert_eq]
      apply insert_subset_insert
      exact image_subset_iff.mpr st
    · have : AnalyticOn 𝕜 f w := by
        have : AnalyticOn 𝕜 (fun y ↦ (continuousMultilinearCurryFin0 𝕜 E F).symm (f y)) w :=
          ((h'p 0).mono wu).congr fun y hy ↦ (hp.zero_eq' (wu hy)).symm
        have : AnalyticOn 𝕜 (fun y ↦ (continuousMultilinearCurryFin0 𝕜 E F)
            ((continuousMultilinearCurryFin0 𝕜 E F).symm (f y))) w :=
          AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _) this
          (mapsTo_univ _ _)
        simpa using this
      exact analyticOn_taylorComp h'q (fun n ↦ (h'p n).mono wu) this wv
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    let w := insert x s ∩ (u ∩ f ⁻¹' v)
    have wv : w ⊆ f ⁻¹' v := fun y hy => hy.2.2
    have wu : w ⊆ u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y ↦ (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv⟩
    apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
    apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
    apply nhdsWithin_mono _ _ hv
    simp only [image_insert_eq]
    apply insert_subset_insert
    exact image_subset_iff.mpr st

/-- The composition of `C^n` functions on domains is `C^n`. -/
/-
**ContDiffOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg : Co
ntDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s t) : ContDiffOn 𝕜 n
 (g ∘ f) s
参数：hg : ContDiffOn 𝕜 n g t；hf : ContDiffOn 𝕜 n f s；st : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…

--- 原说明 ---
The composition of `C^n` functions on domains is `C^n`.
-/
theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s t) : ContDiffOn 𝕜 n (g ∘ f) s :=
  fun x hx ↦ ContDiffWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
/-
**ContDiffOn.comp_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.comp_inter {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (h
g : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s in
ter f ⁻¹' t)
参数：hg : ContDiffOn 𝕜 n g t；hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The composition of `C^n` functions on domains is `C^n`.
-/
theorem ContDiffOn.comp_inter
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
/-
**ContDiff.comp_contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_contDiffOn {s : Set E} {g : F -> G} {f : E -> F} (hg : ContD
iff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s
参数：hg : ContDiff 𝕜 n g；hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
The composition of a `C^n` function on a domain with a `C^n` function is `C^n`.
-/
theorem ContDiff.comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

@[fun_prop]
/-
**ContDiff.fun_comp_contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.fun_comp_contDiffOn {s : Set E} {g : F -> G} {f : E -> F} (hg : C
ontDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => g (f x)) s
参数：hg : ContDiff 𝕜 n g；hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem ContDiff.fun_comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => g (f x)) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)
/-
**ContDiffOn.comp_contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.comp_contDiff {s : Set F} {g : F -> G} {f : E -> F} (hg : ContD
iffOn 𝕜 n g s) (hf : ContDiff 𝕜 n f) (hs : forall x, f x in s) : ContDiff 𝕜 n (g
 ∘ f)
参数：hg : ContDiffOn 𝕜 n g s；hf : ContDiff 𝕜 n f；hs : forall x, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
-/
theorem ContDiffOn.comp_contDiff {s : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g s)
    (hf : ContDiff 𝕜 n f) (hs : ∀ x, f x ∈ s) : ContDiff 𝕜 n (g ∘ f) := by
  rw [← contDiffOn_univ] at *
  exact hg.comp hf fun x _ => hs x
/-
**ContDiffOn.image_comp_contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.image_comp_contDiff {s : Set E} {g : F -> G} {f : E -> F} (hg :
 ContDiffOn 𝕜 n g (f '' s)) (hf : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n (g ∘ f) s
参数：hg : ContDiffOn 𝕜 n g (f '' s)；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContDiffOn.image_comp_contDiff {s : Set E} {g : F → G} {f : E → F}
    (hg : ContDiffOn 𝕜 n g (f '' s)) (hf : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n (g ∘ f) s :=
  hg.comp hf.contDiffOn (s.mapsTo_image f)

/-- The composition of `C^n` functions is `C^n`. -/
/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
The composition of `C^n` functions is `C^n`.
-/
theorem ContDiff.comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (g ∘ f) :=
  contDiffOn_univ.1 <| ContDiffOn.comp (contDiffOn_univ.2 hg) (contDiffOn_univ.2 hf) (subset_univ _)

@[fun_prop]
/-
**ContDiff.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : Co
ntDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => g (f x))
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
-/
theorem ContDiff.fun_comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (fun x => g (f x)) := hg.comp hf

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
/-
**ContDiffWithinAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_of_eq {s : Set E} {t : Set F} {g : F -> G} {f : E ->
 F} {y : F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n
 f s x) (st : MapsTo f s t) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t y；hf : ContDiffWithinAt 𝕜 n f s x；st : Ma
psTo f s t；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`.
-/
theorem ContDiffWithinAt.comp_of_eq {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x) (st : MapsTo f s t)
    (hy : f x = y) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp x hf st

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
/-
**ContDiffWithinAt.comp_of_mem_nhdsWithin_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_of_mem_nhdsWithin_image {s : Set E} {t : Set F} {g :
 F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDi
ffWithinAt 𝕜 n f s x) (hs : t in 𝓝[f '' s] f x) : ContDiffWithinAt 𝕜 n (g ∘ f) s
 x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；hs 
: t in 𝓝[f '' s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`.
-/
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t ∈ 𝓝[f '' s] f x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.mono_of_mem_nhdsWithin hs).comp x hf (subset_preimage_image f s)

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
/-
**ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq {s : Set E} {t : Set F
} {g : F -> G} {f : E -> F} {y : F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t y) (h
f : ContDiffWithinAt 𝕜 n f s x) (hs : t in 𝓝[f '' s] f x) (hy : f x = y) : ContD
iffWithinAt 𝕜 n (g ∘ f) s x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t y；hf : ContDiffWithinAt 𝕜 n f s x；hs : t 
in 𝓝[f '' s] f x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp_of_mem_nhdsWithin_image`：ContDiffWithinAt.comp_of_
mem_nhdsWithin_image {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E) (
hg : ContDiffWithinAt 𝕜 n g t (f x)…

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`.
-/
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t ∈ 𝓝[f '' s] f x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image x hf hs

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
/-
**ContDiffWithinAt.comp_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_inter {s : Set E} {t : Set F} {g : F -> G} {f : E ->
 F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s
 x) : ContDiffWithinAt 𝕜 n (g ∘ f) (s inter f ⁻¹' t) x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`.
-/
theorem ContDiffWithinAt.comp_inter {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
/-
**ContDiffWithinAt.comp_inter_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_inter_of_eq {s : Set E} {t : Set F} {g : F -> G} {f 
: E -> F} {y : F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithin
At 𝕜 n f s x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) (s inter f ⁻¹' t) x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t y；hf : ContDiffWithinAt 𝕜 n f s x；hy : f 
x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp_inter`：ContDiffWithinAt.comp_inter {s : Set E} {t 
: Set F} {g : F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x))
 (hf : ContDiffWi…

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`.
-/
theorem ContDiffWithinAt.comp_inter_of_eq {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F}
    (x : E) (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x := by
  subst hy; exact hg.comp_inter x hf

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
/-
**ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin {s : Set E} {t : Set F} {
g : F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : Con
tDiffWithinAt 𝕜 n f s x) (hs : f ⁻¹' t in 𝓝[s] x) : ContDiffWithinAt 𝕜 n (g ∘ f)
 s x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；hs 
: f ⁻¹' t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.comp_inter`：ContDiffWithinAt.comp_inter {s : Set E} {t 
: Set F} {g : F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x))
 (hf : ContDiffWi…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`.
-/
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : f ⁻¹' t ∈ 𝓝[s] x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.comp_inter x hf).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hs)

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
/-
**ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {s : Set E} {t : Se
t F} {g : F -> G} {f : E -> F} {y : F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t y)
 (hf : ContDiffWithinAt 𝕜 n f s x) (hs : f ⁻¹' t in 𝓝[s] x) (hy : f x = y) : Con
tDiffWithinAt 𝕜 n (g ∘ f) s x
参数：x : E；hg : ContDiffWithinAt 𝕜 n g t y；hf : ContDiffWithinAt 𝕜 n f s x；hs : f 
⁻¹' t in 𝓝[s] x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin`：ContDiffWithinAt.comp_
of_preimage_mem_nhdsWithin {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x 
: E) (hg : ContDiffWithinAt 𝕜 n g t (f…

--- 原说明 ---
The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`.
-/
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : f ⁻¹' t ∈ 𝓝[s] x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin x hf hs
/-
**ContDiffAt.comp_contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.comp_contDiffWithinAt (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf
 : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x
参数：x : E；hg : ContDiffAt 𝕜 n g (f x)；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem ContDiffAt.comp_contDiffWithinAt (x : E) (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)
/-
**ContDiffAt.comp_contDiffWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.comp_contDiffWithinAt_of_eq {y : F} (x : E) (hg : ContDiffAt 𝕜 
n g y) (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (
g ∘ f) s x
参数：x : E；hg : ContDiffAt 𝕜 n g y；hf : ContDiffWithinAt 𝕜 n f s x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
-/
theorem ContDiffAt.comp_contDiffWithinAt_of_eq {y : F} (x : E) (hg : ContDiffAt 𝕜 n g y)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_contDiffWithinAt x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContDiffAt.comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

@[fun_prop]
/-
**ContDiffAt.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => g (f x)) x
参数：x : E；hg : ContDiffAt 𝕜 n g (f x)；hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
-/
theorem ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => g (f x)) x := hg.comp x hf
/-
**ContDiff.comp_contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_contDiffWithinAt {g : F -> G} {f : E -> F} (h : ContDiff 𝕜 n
 g) (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x
参数：h : ContDiff 𝕜 n g；hf : ContDiffWithinAt 𝕜 n f t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp_contDiffWithinAt {g : F → G} {f : E → F} (h : ContDiff 𝕜 n g)
    (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x :=
  haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)
/-
**ContDiff.comp_contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_contDiffAt {g : F -> G} {f : E -> F} (x : E) (hg : ContDiff 
𝕜 n g) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x
参数：x : E；hg : ContDiff 𝕜 n g；hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffWithinAt`：ContDiff.comp_contDiffWithinAt {g : F ->
 G} {f : E -> F} (h : ContDiff 𝕜 n g) (hf : ContDiffWithinAt 𝕜 n f t x) : ContDi
ffWithinAt 𝕜 n (g ∘ …
-/
theorem ContDiff.comp_contDiffAt {g : F → G} {f : E → F} (x : E) (hg : ContDiff 𝕜 n g)
    (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_contDiffWithinAt hf
/-
**iteratedFDerivWithin_comp_of_eventually_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_comp_of_eventually_mem {t : Set F} (hg : ContDiffWith
inAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (h
s : UniqueDiffOn 𝕜 s) (hxs : x in s) (hst : forallᶠ y in 𝓝[s] x, f y in t) {i : 
Nat} (hi : i <= n) : iteratedFDerivWithin 𝕜 i (g ∘ f) s x = (ftaylorSeriesWithin
 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i
参数：hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hxs : x in s；hst : forallᶠ y in 𝓝[s] x, f y i
n t；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
· 使用定理 `ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn`：ContDiffWithinAt.eve
ntually_hasFTaylorSeriesUpToOn {f : E -> F} {s : Set E} {a : E} (h : ContDiffWit
hinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s)…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.image_smallSets`：∀ {α : Type u_1} {β : Type u_2} {la : Fi
lter α} {lb : Filter β} {f : α → β},   Filter.Tendsto f la lb → Filter.Tendsto (
fun x => f '' x) la.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `HasFTaylorSeriesUpToOn.comp`：HasFTaylorSeriesUpToOn.comp {n : WithTop Na
t∞} {g : F -> G} {f : E -> F} (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTa
ylorSeriesUpToOn …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用引理 `le_rfl`：le_rfl : a <= a
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
-/
theorem iteratedFDerivWithin_comp_of_eventually_mem {t : Set F}
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hxs : x ∈ s) (hst : ∀ᶠ y in 𝓝[s] x, f y ∈ t)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i := by
  obtain ⟨u, hxu, huo, hfu, hgu⟩ : ∃ u, x ∈ u ∧ IsOpen u ∧
      HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) (s ∩ u) ∧
      HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' (s ∩ u)) := by
    have hxt : f x ∈ t := hst.self_of_nhdsWithin hxs
    have hf_tendsto : Tendsto f (𝓝[s] x) (𝓝[t] (f x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hst⟩
    have H₁ : ∀ᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) u :=
      hf.eventually_hasFTaylorSeriesUpToOn hs hxs hi
    have H₂ : ∀ᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' u) :=
      hf_tendsto.image_smallSets.eventually (hg.eventually_hasFTaylorSeriesUpToOn ht hxt hi)
    rcases (nhdsWithin_basis_open _ _).smallSets.eventually_iff.mp (H₁.and H₂)
      with ⟨u, ⟨hxu, huo⟩, hu⟩
    exact ⟨u, hxu, huo, hu (by simp [inter_comm])⟩
  exact .symm <| (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    (hs.inter huo) ⟨hxs, hxu⟩ |>.trans <| iteratedFDerivWithin_inter_open huo hxu
/-
**iteratedFDerivWithin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_comp {t : Set F} (hg : ContDiffWithinAt 𝕜 n g t (f x)
) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜
 s) (hx : x in s) (hst : MapsTo f s t) {i : Nat} (hi : i <= n) : iteratedFDerivW
ithin 𝕜 i (g ∘ f) s x = (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSer
iesWithin 𝕜 f s x) i
参数：hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedFDerivWithin_comp_of_eventually_mem`：iteratedFDerivWithin_comp_o
f_eventually_mem {t : Set F} (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDif
fWithinAt 𝕜 n f s x) (ht : Unique…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
-/
theorem iteratedFDerivWithin_comp {t : Set F} (hg : ContDiffWithinAt 𝕜 n g t (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) (hst : MapsTo f s t) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i :=
  iteratedFDerivWithin_comp_of_eventually_mem hg hf ht hs hx (eventually_mem_nhdsWithin.mono hst) hi
/-
**iteratedFDeriv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_comp (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x
) {i : Nat} (hi : i <= n) : iteratedFDeriv 𝕜 i (g ∘ f) x = (ftaylorSeries 𝕜 g (f
 x)).taylorComp (ftaylorSeries 𝕜 f x) i
参数：hg : ContDiffAt 𝕜 n g (f x)；hf : ContDiffAt 𝕜 n f x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
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
· 使用定理 `iteratedFDerivWithin_comp`：iteratedFDerivWithin_comp {t : Set F} (hg : C
ontDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDif
fOn 𝕜 t) (hs : …
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedFDeriv_comp (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      (ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) i := by
  simp only [← iteratedFDerivWithin_univ, ← ftaylorSeriesWithin_univ]
  exact iteratedFDerivWithin_comp hg.contDiffWithinAt hf.contDiffWithinAt
    uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _) (mapsTo_univ _ _) hi

end comp

/-!
### Smoothness of projections
-/

/-- The first projection in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiff_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.contDiff`：IsBoundedLinearMap.contDiff (hf : IsBounded
LinearMap 𝕜 f) : ContDiff 𝕜 n f
· 使用定理 `IsBoundedLinearMap.fst`：fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1

--- 原说明 ---
The first projection in a product is `C^∞`.
-/
theorem contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F → E) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst

/-- Postcomposing `f` with `Prod.fst` is `C^n` -/
@[fun_prop]
/-
**ContDiff.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.fst {f : E -> F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x =
> (f x).1
参数：hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)

--- 原说明 ---
Postcomposing `f` with `Prod.fst` is `C^n`
-/
theorem ContDiff.fst {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).1 :=
  contDiff_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is `C^n` -/
/-
**ContDiff.fst'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.fst' {f : E -> G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E 
× F => f x.1
参数：hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)

--- 原说明 ---
Precomposing `f` with `Prod.fst` is `C^n`
-/
theorem ContDiff.fst' {f : E → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.1 :=
  hf.comp contDiff_fst

/-- The first projection on a domain in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiffOn_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F -> E) 
s
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)

--- 原说明 ---
The first projection on a domain in a product is `C^∞`.
-/
theorem contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F → E) s :=
  ContDiff.contDiffOn contDiff_fst

@[fun_prop]
/-
**ContDiffOn.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.fst {f : E -> F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) : Co
ntDiffOn 𝕜 n (fun x => (f x).1) s
参数：hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)
-/
theorem ContDiffOn.fst {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).1) s :=
  contDiff_fst.comp_contDiffOn hf

/-- The first projection at a point in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiffAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F -> E) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)

--- 原说明 ---
The first projection at a point in a product is `C^∞`.
-/
theorem contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F → E) p :=
  contDiff_fst.contDiffAt

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
@[fun_prop]
/-
**ContDiffAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.fst {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) : ContDi
ffAt 𝕜 n (fun x => (f x).1) x
参数：hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p

--- 原说明 ---
Postcomposing `f` with `Prod.fst` is `C^n` at `(x, y)`
-/
theorem ContDiffAt.fst {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).1) x :=
  contDiffAt_fst.comp x hf

/-- Precomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
/-
**ContDiffAt.fst'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.fst' {f : E -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x) : C
ontDiffAt 𝕜 n (fun x : E × F => f x.1) (x, y)
参数：hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p

--- 原说明 ---
Precomposing `f` with `Prod.fst` is `C^n` at `(x, y)`
-/
theorem ContDiffAt.fst' {f : E → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_fst

/-- Precomposing `f` with `Prod.fst` is `C^n` at `x : E × F` -/
/-
**ContDiffAt.fst''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.fst'' {f : E -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1) : Co
ntDiffAt 𝕜 n (fun x : E × F => f x.1) x
参数：hf : ContDiffAt 𝕜 n f x.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p

--- 原说明 ---
Precomposing `f` with `Prod.fst` is `C^n` at `x : E × F`
-/
theorem ContDiffAt.fst'' {f : E → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) x :=
  hf.comp x contDiffAt_fst

/-- The first projection within a domain at a point in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiffWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_fst {s : Set (E × F)} {p : E × F} : ContDiffWithinAt 𝕜 n 
(Prod.fst : E × F -> E) s p
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)

--- 原说明 ---
The first projection within a domain at a point in a product is `C^∞`.
-/
theorem contDiffWithinAt_fst {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.fst : E × F → E) s p :=
  contDiff_fst.contDiffWithinAt

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `x` -/
@[fun_prop]
/-
**ContDiffWithinAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.fst {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f
 s x) : ContDiffWithinAt 𝕜 n (fun x => (f x).1) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `contDiffWithinAt_fst`：contDiffWithinAt_fst {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.fst : E × F -> E) s p
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)

--- 原说明 ---
Postcomposing `f` with `Prod.fst` is `C^n` at `x`
-/
theorem ContDiffWithinAt.fst {f : E → F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x ↦ (f x).1) s x :=
  contDiffWithinAt_fst.comp x hf (mapsTo_image f s)

/-- The second projection in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiff_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.contDiff`：IsBoundedLinearMap.contDiff (hf : IsBounded
LinearMap 𝕜 f) : ContDiff 𝕜 n f
· 使用定理 `IsBoundedLinearMap.snd`：snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2

--- 原说明 ---
The second projection in a product is `C^∞`.
-/
theorem contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F → F) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd

/-- Postcomposing `f` with `Prod.snd` is `C^n` -/
@[fun_prop]
/-
**ContDiff.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.snd {f : E -> F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x =
> (f x).2
参数：hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)

--- 原说明 ---
Postcomposing `f` with `Prod.snd` is `C^n`
-/
theorem ContDiff.snd {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).2 :=
  contDiff_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is `C^n` -/
/-
**ContDiff.snd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.snd' {f : F -> G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E 
× F => f x.2
参数：hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)

--- 原说明 ---
Precomposing `f` with `Prod.snd` is `C^n`
-/
theorem ContDiff.snd' {f : F → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.2 :=
  hf.comp contDiff_snd

/-- The second projection on a domain in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiffOn_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F -> F) 
s
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)

--- 原说明 ---
The second projection on a domain in a product is `C^∞`.
-/
theorem contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F → F) s :=
  ContDiff.contDiffOn contDiff_snd

@[fun_prop]
/-
**ContDiffOn.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.snd {f : E -> F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) : Co
ntDiffOn 𝕜 n (fun x => (f x).2) s
参数：hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)
-/
theorem ContDiffOn.snd {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).2) s :=
  contDiff_snd.comp_contDiffOn hf

/-- The second projection within a domain at a point in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiffWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_snd {s : Set (E × F)} {p : E × F} : ContDiffWithinAt 𝕜 n 
(Prod.snd : E × F -> F) s p
参数：E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)

--- 原说明 ---
The second projection within a domain at a point in a product is `C^∞`.
-/
theorem contDiffWithinAt_snd {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.snd : E × F → F) s p :=
  contDiff_snd.contDiffWithinAt

/-- The second projection at a point in a product is `C^∞`. -/
@[fun_prop]
/-
**contDiffAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F -> F) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)

--- 原说明 ---
The second projection at a point in a product is `C^∞`.
-/
theorem contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F → F) p :=
  contDiff_snd.contDiffAt

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
@[fun_prop]
/-
**ContDiffWithinAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.snd {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f
 s x) : ContDiffWithinAt 𝕜 n (fun x => (f x).2) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `contDiffWithinAt_snd`：contDiffWithinAt_snd {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.snd : E × F -> F) s p
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)

--- 原说明 ---
Postcomposing `f` with `Prod.snd` is `C^n` at `x`
-/
theorem ContDiffWithinAt.snd {f : E → F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x ↦ (f x).2) s x :=
  contDiffWithinAt_snd.comp x hf (mapsTo_image f s)

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
@[fun_prop]
/-
**ContDiffAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) : ContDi
ffAt 𝕜 n (fun x => (f x).2) x
参数：hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p

--- 原说明 ---
Postcomposing `f` with `Prod.snd` is `C^n` at `x`
-/
theorem ContDiffAt.snd {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).2) x :=
  contDiffAt_snd.comp x hf

/-- Precomposing `f` with `Prod.snd` is `C^n` at `(x, y)` -/
/-
**ContDiffAt.snd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.snd' {f : F -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y) : C
ontDiffAt 𝕜 n (fun x : E × F => f x.2) (x, y)
参数：hf : ContDiffAt 𝕜 n f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p

--- 原说明 ---
Precomposing `f` with `Prod.snd` is `C^n` at `(x, y)`
-/
theorem ContDiffAt.snd' {f : F → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_snd

/-- Precomposing `f` with `Prod.snd` is `C^n` at `x : E × F` -/
/-
**ContDiffAt.snd''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.snd'' {f : F -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2) : Co
ntDiffAt 𝕜 n (fun x : E × F => f x.2) x
参数：hf : ContDiffAt 𝕜 n f x.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p

--- 原说明 ---
Precomposing `f` with `Prod.snd` is `C^n` at `x : E × F`
-/
theorem ContDiffAt.snd'' {f : F → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) x :=
  hf.comp x contDiffAt_snd
/-
**contDiffWithinAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_prod_iff (f : E -> F × G) : ContDiffWithinAt 𝕜 n f s x ↔ 
ContDiffWithinAt 𝕜 n (Prod.fst ∘ f) s x ∧ ContDiffWithinAt 𝕜 n (Prod.snd ∘ f) s 
x
参数：f : E -> F × G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.fst`：ContDiffWithinAt.fst {f : E -> F × G} {x : E} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => (f x).1) s x
· 使用定理 `ContDiffWithinAt.snd`：ContDiffWithinAt.snd {f : E -> F × G} {x : E} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => (f x).2) s x
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contDiffWithinAt_prod_iff (f : E → F × G) :
    ContDiffWithinAt 𝕜 n f s x ↔
      ContDiffWithinAt 𝕜 n (Prod.fst ∘ f) s x ∧ ContDiffWithinAt 𝕜 n (Prod.snd ∘ f) s x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩
/-
**contDiffAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_prod_iff (f : E -> F × G) : ContDiffAt 𝕜 n f x ↔ ContDiffAt 𝕜 n
 (Prod.fst ∘ f) x ∧ ContDiffAt 𝕜 n (Prod.snd ∘ f) x
参数：f : E -> F × G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.fst`：ContDiffAt.fst {f : E -> F × G} {x : E} (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).1) x
· 使用定理 `ContDiffAt.snd`：ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).2) x
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contDiffAt_prod_iff (f : E → F × G) :
    ContDiffAt 𝕜 n f x ↔
      ContDiffAt 𝕜 n (Prod.fst ∘ f) x ∧ ContDiffAt 𝕜 n (Prod.snd ∘ f) x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩
/-
**contDiffOn_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_prod_iff (f : E -> F × G) : ContDiffOn 𝕜 n f s ↔ ContDiffOn 𝕜 n
 (Prod.fst ∘ f) s ∧ ContDiffOn 𝕜 n (Prod.snd ∘ f) s
参数：f : E -> F × G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.fst`：ContDiffOn.fst {f : E -> F × G} {s : Set E} (hf : ContDi
ffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => (f x).1) s
· 使用定理 `ContDiffOn.snd`：ContDiffOn.snd {f : E -> F × G} {s : Set E} (hf : ContDi
ffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => (f x).2) s
· 使用定理 `ContDiffOn.prodMk`：ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> 
G} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x :
 E => (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contDiffOn_prod_iff (f : E → F × G) :
    ContDiffOn 𝕜 n f s ↔
      ContDiffOn 𝕜 n (Prod.fst ∘ f) s ∧ ContDiffOn 𝕜 n (Prod.snd ∘ f) s :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩
/-
**contDiff_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prod_iff (f : E -> F × G) : ContDiff 𝕜 n f ↔ ContDiff 𝕜 n (Prod.f
st ∘ f) ∧ ContDiff 𝕜 n (Prod.snd ∘ f)
参数：f : E -> F × G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.fst`：ContDiff.fst {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).1
· 使用定理 `ContDiff.snd`：ContDiff.snd {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).2
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contDiff_prod_iff (f : E → F × G) :
    ContDiff 𝕜 n f ↔
      ContDiff 𝕜 n (Prod.fst ∘ f) ∧ ContDiff 𝕜 n (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

section NAry

variable {E₁ E₂ E₃ : Type*}
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 E₃]

/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : ContDiff 𝕜 n fun x => g (f₁ x, f₂ x) :=
  hg.comp <| hf₁.prodMk hf₂
/-
**ContDiffAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f : E → F} {g : F → G} {n : WithTop
 ℕ∞} (x : E),   ContDiffAt 𝕜 n g (f x) → ContDiffAt 𝕜 n f x → ContDiffAt 𝕜 n (g 
∘ f) x
参数：x : E；f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem ContDiffAt.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.comp x (hf₁.prodMk hf₂)
/-
**ContDiffAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f : E → F} {g : F → G} {n : WithTop
 ℕ∞} (x : E),   ContDiffAt 𝕜 n g (f x) → ContDiffAt 𝕜 n f x → ContDiffAt 𝕜 n (g 
∘ f) x
参数：x : E；f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem ContDiffAt.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
    {s : Set F} {x : F} (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.comp_contDiffWithinAt x (hf₁.prodMk hf₂)
/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp₂_contDiffAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.contDiffAt.comp₂ hf₁ hf₂
/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
    {s : Set F} {x : F} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.contDiffAt.comp_contDiffWithinAt x (hf₁.prodMk hf₂)
/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp₂_contDiffOn {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : Set F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) :
    ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x)) s :=
  hg.comp_contDiffOn <| hf₁.prodMk hf₂
/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) (hf₃ : ContDiff 𝕜 n f₃) :
    ContDiff 𝕜 n fun x => g (f₁ x, f₂ x, f₃ x) :=
  hg.comp₂ hf₁ <| hf₂.prodMk hf₃
/-
**ContDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDi
ff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ContDiff.comp₃_contDiffOn {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s)
    (hf₃ : ContDiffOn 𝕜 n f₃ s) : ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x, f₃ x)) s :=
  hg.comp₂_contDiffOn hf₁ <| hf₂.prodMk hf₃

end NAry

section SpecificBilinearMaps

@[fun_prop]
/-
**ContDiff.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} (hg : ContDi
ff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g x).comp (f x)
参数：hg : ContDiff 𝕜 n g；hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂`：ContDiff.comp₂ {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F
 -> E₂} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : 
Cont…
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
-/
theorem ContDiff.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g x).comp (f x) :=
  isBoundedBilinearMap_comp.contDiff.comp₂ (g := fun p => p.1.comp p.2) hg hf

@[fun_prop]
/-
**ContDiffOn.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set X
} (hg : ContDiffOn 𝕜 n g s) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x =>
 (g x).comp (f x)) s
参数：hg : ContDiffOn 𝕜 n g s；hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂_contDiffOn`：ContDiff.comp₂_contDiffOn {g : E₁ × E₂ -> G} 
{f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffO
n 𝕜 n f₁ s) (hf…
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
-/
theorem ContDiffOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X}
    (hg : ContDiffOn 𝕜 n g s) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (g x).comp (f x)) s :=
  (isBoundedBilinearMap_comp (E := E) (F := F) (G := G)).contDiff.comp₂_contDiffOn hg hf

@[fun_prop]
/-
**ContDiffAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {x : X} (h
g : ContDiffAt 𝕜 n g x) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (g 
x).comp (f x)) x
参数：hg : ContDiffAt 𝕜 n g x；hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂_contDiffAt`：ContDiff.comp₂_contDiffAt {g : E₁ × E₂ -> G} 
{f₁ : F -> E₁} {f₂ : F -> E₂} {x : F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 
n f₁ x) (hf₂ : …
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
-/
theorem ContDiffAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {x : X}
    (hg : ContDiffAt 𝕜 n g x) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (g x).comp (f x)) x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffAt hg hf

@[fun_prop]
/-
**ContDiffWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s :
 Set X} {x : X} (hg : ContDiffWithinAt 𝕜 n g s x) (hf : ContDiffWithinAt 𝕜 n f s
 x) : ContDiffWithinAt 𝕜 n (fun x => (g x).comp (f x)) s x
参数：hg : ContDiffWithinAt 𝕜 n g s x；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂_contDiffWithinAt`：ContDiff.comp₂_contDiffWithinAt {g : E₁
 × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F} {x : F} (hg : ContDiff 𝕜 n
 g) (hf₁ : ContDiffWi…
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
-/
theorem ContDiffWithinAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X} {x : X}
    (hg : ContDiffWithinAt 𝕜 n g s x) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => (g x).comp (f x)) s x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffWithinAt hg hf

@[fun_prop]
/-
**ContDiff.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiff 𝕜 n f
) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x)
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂`：ContDiff.comp₂ {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F
 -> E₂} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : 
Cont…
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
-/
theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x) :=
  isBoundedBilinearMap_apply.contDiff.comp₂ hf hg

@[fun_prop]
/-
**ContDiffOn.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffOn 𝕜
 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂_contDiffOn`：ContDiff.comp₂_contDiffOn {g : E₁ × E₂ -> G} 
{f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffO
n 𝕜 n f₁ s) (hf…
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
-/
theorem ContDiffOn.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffOn hf hg

@[fun_prop]
/-
**ContDiffAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffAt 𝕜
 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x) (g x)) x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂_contDiffAt`：ContDiff.comp₂_contDiffAt {g : E₁ × E₂ -> G} 
{f₁ : F -> E₁} {f₂ : F -> E₂} {x : F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 
n f₁ x) (hf₂ : …
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
-/
theorem ContDiffAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x) (g x)) x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffAt hf hg

@[fun_prop]
/-
**ContDiffWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDi
ffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (
fun x => (f x) (g x)) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp₂_contDiffWithinAt`：ContDiff.comp₂_contDiffWithinAt {g : E₁
 × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F} {x : F} (hg : ContDiff 𝕜 n
 g) (hf₁ : ContDiffWi…
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
-/
theorem ContDiffWithinAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x) (g x)) s x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffWithinAt hf hg

@[fun_prop]
/-
**ContDiff.smulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiff 𝕜
 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x).smulRight (g x)
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContDiff.comp₂`：ContDiff.comp₂ {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F
 -> E₂} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : 
Cont…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_smulRight`：isBoundedBilinearMap_smulRight : IsBound
edBilinearMap 𝕜 fun p => (ContinuousLinearMap.smulRight : StrongDual 𝕜 E -> F ->
 E ->L[𝕜] F) p.1 p.2
-/
theorem ContDiff.smulRight {f : E → StrongDual 𝕜 F} {g : E → G} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x).smulRight (g x) :=
  isBoundedBilinearMap_smulRight.contDiff.comp₂ (g := fun p => p.1.smulRight p.2) hf hg

@[fun_prop]
/-
**ContDiffOn.smulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiff
On 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x).smulRight
 (g x)) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContDiff.comp₂_contDiffOn`：ContDiff.comp₂_contDiffOn {g : E₁ × E₂ -> G} 
{f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffO
n 𝕜 n f₁ s) (hf…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_smulRight`：isBoundedBilinearMap_smulRight : IsBound
edBilinearMap 𝕜 fun p => (ContinuousLinearMap.smulRight : StrongDual 𝕜 E -> F ->
 E ->L[𝕜] F) p.1 p.2
-/
theorem ContDiffOn.smulRight {f : E → StrongDual 𝕜 F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x).smulRight (g x)) s :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffOn hf hg

@[fun_prop]
/-
**ContDiffAt.smulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiff
At 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x).smulRight
 (g x)) x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContDiff.comp₂_contDiffAt`：ContDiff.comp₂_contDiffAt {g : E₁ × E₂ -> G} 
{f₁ : F -> E₁} {f₂ : F -> E₂} {x : F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 
n f₁ x) (hf₂ : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_smulRight`：isBoundedBilinearMap_smulRight : IsBound
edBilinearMap 𝕜 fun p => (ContinuousLinearMap.smulRight : StrongDual 𝕜 E -> F ->
 E ->L[𝕜] F) p.1 p.2
-/
theorem ContDiffAt.smulRight {f : E → StrongDual 𝕜 F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x).smulRight (g x)) x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffAt hf hg

@[fun_prop]
/-
**ContDiffWithinAt.smulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : Co
ntDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜
 n (fun x => (f x).smulRight (g x)) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContDiff.comp₂_contDiffWithinAt`：ContDiff.comp₂_contDiffWithinAt {g : E₁
 × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F} {x : F} (hg : ContDiff 𝕜 n
 g) (hf₁ : ContDiffWi…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_smulRight`：isBoundedBilinearMap_smulRight : IsBound
edBilinearMap 𝕜 fun p => (ContinuousLinearMap.smulRight : StrongDual 𝕜 E -> F ->
 E ->L[𝕜] F) p.1 p.2
-/
theorem ContDiffWithinAt.smulRight {f : E → StrongDual 𝕜 F} {g : E → G}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x).smulRight (g x)) s x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffWithinAt hf hg

end SpecificBilinearMaps

section ClmApplyConst

/-- Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDerivWithin`. -/
/-
**iteratedFDerivWithin_clm_apply_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_clm_apply_const_apply {s : Set E} (hs : UniqueDiffOn 
𝕜 s) {c : E -> F ->L[𝕜] G} (hc : ContDiffOn 𝕜 n c s) {i : Nat} (hi : i <= n) {x 
: E} (hx : x in s) {u : F} {m : Fin i -> E} : (iteratedFDerivWithin 𝕜 i (fun y =
> (c y) u) s x) m = (iteratedFDerivWithin 𝕜 i c s x) m u
参数：hs : UniqueDiffOn 𝕜 s；hc : ContDiffOn 𝕜 n c s；hi : i <= n；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffOn.differentiableOn_iteratedFDerivWithin`：ContDiffOn.differentia
bleOn_iteratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs 
: UniqueDiffOn 𝕜 s) : DifferentiableOn…
· 使用定理 `ContDiffOn.clm_apply`：ContDiffOn.clm_apply {f : E -> F ->L[𝕜] G} {g : E 
-> F} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun 
x => (f x)…
· 使用定理 `contDiffOn_const`：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n 
(fun _ : E => c) s
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_continuousMultilinear_apply_const_apply`：fderivWithin_conti
nuousMultilinear_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differ
entiableWithinAt 𝕜 c s x) (u : forall i, M…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `fderivWithin_congr'`：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s
) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_clm_apply`：fderivWithin_clm_apply (hxs : UniqueDiffWithinAt
 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s
 x) : fderiv…
· 使用定理 `DifferentiableOn.continuousMultilinear_apply_const`：DifferentiableOn.con
tinuousMultilinear_apply_const (hc : DifferentiableOn 𝕜 c s) (u : forall i, M i)
 : DifferentiableOn 𝕜 (fun y => (c y) u)…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDer
ivWithin`.
-/
theorem iteratedFDerivWithin_clm_apply_const_apply
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {c : E → F →L[𝕜] G}
    (hc : ContDiffOn 𝕜 n c s) {i : ℕ} (hi : i ≤ n) {x : E} (hx : x ∈ s) {u : F} {m : Fin i → E} :
    (iteratedFDerivWithin 𝕜 i (fun y ↦ (c y) u) s x) m = (iteratedFDerivWithin 𝕜 i c s x) m u := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    replace hi : (i : ℕ∞ω) < n := lt_of_lt_of_le (by norm_cast; simp) hi
    have h_deriv_apply : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i (fun y ↦ (c y) u) s) s :=
      (hc.clm_apply contDiffOn_const).differentiableOn_iteratedFDerivWithin hi hs
    have h_deriv : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i c s) s :=
      hc.differentiableOn_iteratedFDerivWithin hi hs
    simp only [iteratedFDerivWithin_succ_apply_left]
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv_apply x hx)]
    rw [fderivWithin_congr' (fun x hx ↦ ih hi.le hx) hx]
    rw [fderivWithin_clm_apply (hs x hx) (h_deriv.continuousMultilinear_apply_const _ x hx)
      (differentiableWithinAt_const u)]
    rw [fderivWithin_const_apply]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv x hx)]

/-- Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDeriv`. -/
/-
**iteratedFDeriv_clm_apply_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_clm_apply_const_apply {c : E -> F ->L[𝕜] G} (hc : ContDiff 
𝕜 n c) {i : Nat} (hi : i <= n) {x : E} {u : F} {m : Fin i -> E} : (iteratedFDeri
v 𝕜 i (fun y => (c y) u) x) m = (iteratedFDeriv 𝕜 i c x) m u
参数：hc : ContDiff 𝕜 n c；hi : i <= n。
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
· 使用定理 `iteratedFDerivWithin_clm_apply_const_apply`：iteratedFDerivWithin_clm_app
ly_const_apply {s : Set E} (hs : UniqueDiffOn 𝕜 s) {c : E -> F ->L[𝕜] G} (hc : C
ontDiffOn 𝕜 n c s) {i : Nat} (hi…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDer
iv`.
-/
theorem iteratedFDeriv_clm_apply_const_apply
    {c : E → F →L[𝕜] G} (hc : ContDiff 𝕜 n c)
    {i : ℕ} (hi : i ≤ n) {x : E} {u : F} {m : Fin i → E} :
    (iteratedFDeriv 𝕜 i (fun y ↦ (c y) u) x) m = (iteratedFDeriv 𝕜 i c x) m u := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hc.contDiffOn hi (mem_univ _)

end ClmApplyConst

/-! ### Bundled derivatives are smooth -/
section bundled

/-- One direction of `contDiffWithinAt_succ_iff_hasFDerivWithinAt`, but where all derivatives are
taken within the same set. Version for partial derivatives / functions with parameters. If `f x` is
a `C^n+1` family of functions and `g x` is a `C^n` family of points, then the derivative of `f x` at
`g x` depends in a `C^n` way on `x`. We give a general version of this fact relative to sets which
may not have unique derivatives, in the following form.  If `f : E × F → G` is `C^n+1` at
`(x₀, g(x₀))` in `(s ∪ {x₀}) × t ⊆ E × F` and `g : E → F` is `C^n` at `x₀` within some set `s ⊆ E`,
then there is a function `f' : E → F →L[𝕜] G` that is `C^n` at `x₀` within `s` such that for all `x`
sufficiently close to `x₀` within `s ∪ {x₀}` the function `y ↦ f x y` has derivative `f' x` at `g x`
within `t ⊆ F`.  For convenience, we return an explicit set of `x`'s where this holds that is a
subset of `s ∪ {x₀}`.  We need one additional condition, namely that `t` is a neighborhood of
`g(x₀)` within `g '' s`. -/
/-
**ContDiffWithinAt.hasFDerivWithinAt_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.hasFDerivWithinAt_nhds {f : E -> F -> G} {g : E -> F} {t 
: Set F} (hn : n != ∞) {x₀ : E} (hf : ContDiffWithinAt 𝕜 (n + 1) (uncurry f) (in
sert x₀ s ×ˢ t) (x₀, g x₀)) (hg : ContDiffWithinAt 𝕜 n g s x₀) (hgt : t in 𝓝[g '
' s] g x₀) : exists v in 𝓝[insert x₀ s] x₀, v subseteq insert x₀ s ∧ exists f' :
 E -> F ->L[𝕜] G, (forall x in v, HasFDerivWithinAt (f x) (f' x) t (g x)) ∧ Cont
DiffWithinAt 𝕜 n (fun x => f' x) s x₀
参数：hn : n != ∞；hf : ContDiffWithinAt 𝕜 (n + 1) (uncurry f) (insert x₀ s ×ˢ t) (x
₀, g x₀)；hg : ContDiffWithinAt 𝕜 n g s x₀；hgt : t in 𝓝[g '' s] g x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `nhdsWithin_prod`：nhdsWithin_prod [TopologicalSpace β] {s u : Set α} {t v
 : Set β} {a : α} {b : β} (hu : u in 𝓝[s] a) (hv : v in 𝓝[t] b) : u ×ˢ v in 𝓝[s 
×ˢ t]…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt'`：contDiffWithinAt_succ_iff_
hasFDerivWithinAt' (hn : n != ∞) : ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u i
n 𝓝[insert x s] x, u subseteq inse…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin_insert`：mem_nhdsWithin_insert {a : α} {s t : Set α} : t i
n 𝓝[insert a s] a ↔ a in t ∧ t in 𝓝[s] a
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin'`：ContinuousWithinAt.preimage
_mem_nhdsWithin' {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝[f '' s]
 f x) : f ⁻¹' t in 𝓝[s] x
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `hasFDerivAt_prodMk_right`：hasFDerivAt_prodMk_right (e₀ : E) (f₀ : F) : H
asFDerivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `Set.image_prodMk_subset_prod_right`：image_prodMk_subset_prod_right (ha :
 a in s) : Prod.mk a '' t subseteq s ×ˢ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
One direction of `contDiffWithinAt_succ_iff_hasFDerivWithinAt`, but where all de
rivatives are
taken within the same set. Version for partial derivatives / functions with para
meters. If `f x` is
a `C^n+1` family of functions and `g x` is a `C^n` family of points, then the de
rivative of `f x` at
`g x` depends in a `C^n` way on `x`. We give a general version of this fact rela
tive to sets which
may not have unique derivatives, in the following form.  If `f : E × F → G` is `
C^n+1` at
`(x₀, g(x₀))` in `(s ∪ {x₀}) × t ⊆ E × F` and `g : E → F` is `C^n` at `x₀` withi
n some set `s ⊆ E`,
then there is a function `f' : E → F →L[𝕜] G` that is `C^n` at `x₀` within `s` s
uch that for all `x`
sufficiently close to `x₀` within `s ∪ {x₀}` the function `y ↦ f x y` has deriva
tive `f' x` at `g x`
within `t ⊆ F`.  For convenience, we return an explicit set of `x`'s where this 
holds that is a
subset of `s ∪ {x₀}`.  We need one additional condition, namely that `t` is a ne
ighborhood of
`g(x₀)` within `g '' s`.
-/
theorem ContDiffWithinAt.hasFDerivWithinAt_nhds {f : E → F → G} {g : E → F} {t : Set F} (hn : n ≠ ∞)
    {x₀ : E} (hf : ContDiffWithinAt 𝕜 (n + 1) (uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 n g s x₀) (hgt : t ∈ 𝓝[g '' s] g x₀) :
    ∃ v ∈ 𝓝[insert x₀ s] x₀, v ⊆ insert x₀ s ∧ ∃ f' : E → F →L[𝕜] G,
      (∀ x ∈ v, HasFDerivWithinAt (f x) (f' x) t (g x)) ∧
        ContDiffWithinAt 𝕜 n (fun x => f' x) s x₀ := by
  have hst : insert x₀ s ×ˢ t ∈ 𝓝[(fun x => (x, g x)) '' s] (x₀, g x₀) := by
    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and, subset_preimage_image]
  obtain ⟨v, hv, hvs, f_an, f', hvf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' hn).mp hf
  refine
    ⟨(fun z => (z, g z)) ⁻¹' v ∩ insert x₀ s, ?_, inter_subset_right, fun z =>
      (f' (z, g z)).comp (ContinuousLinearMap.inr 𝕜 E F), ?_, ?_⟩
  · refine inter_mem ?_ self_mem_nhdsWithin
    have := mem_of_mem_nhdsWithin (mem_insert _ _) hv
    refine mem_nhdsWithin_insert.mpr ⟨this, ?_⟩
    refine (continuousWithinAt_id.prodMk hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prodMk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo_iff_image_subset.mpr (image_prodMk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem_nhdsWithin_image x₀
      (contDiffWithinAt_id.prodMk hg) hst

/-- The most general lemma stating that `x ↦ fderivWithin 𝕜 (f x) t (g x)` is `C^n`
at a point within a set.
To show that `x ↦ D_yf(x,y)g(x)` (taken within `t`) is `C^m` at `x₀` within `s`, we require that
* `f` is `C^n` at `(x₀, g(x₀))` within `(s ∪ {x₀}) × t` for `n ≥ m+1`.
* `g` is `C^m` at `x₀` within `s`;
* Derivatives are unique at `g(x)` within `t` for `x` sufficiently close to `x₀` within `s ∪ {x₀}`;
* `t` is a neighborhood of `g(x₀)` within `g '' s`; -/
/-
**ContDiffWithinAt.fderivWithin''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.fderivWithin'' {f : E -> F -> G} {g : E -> F} {t : Set F}
 (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀)) 
(hg : ContDiffWithinAt 𝕜 m g s x₀) (ht : forallᶠ x in 𝓝[insert x₀ s] x₀, UniqueD
iffWithinAt 𝕜 t (g x)) (hmn : m + 1 <= n) (hgt : t in 𝓝[g '' s] g x₀) : ContDiff
WithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀
参数：hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀)；
hg : ContDiffWithinAt 𝕜 m g s x₀；ht : forallᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiff
WithinAt 𝕜 t (g x)；hmn : m + 1 <= n；hgt : t in 𝓝[g '' s] g x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.hasFDerivWithinAt_nhds`：ContDiffWithinAt.hasFDerivWithi
nAt_nhds {f : E -> F -> G} {g : E -> F} {t : Set F} (hn : n != ∞) {x₀ : E} (hf :
 ContDiffWithinAt 𝕜 (n + 1) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
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
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq_insert`：ContDiffWithinAt.congr_of
_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[insert x s] 
x] f) : ContDiffWithinAt 𝕜 n f₁ s x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_infty`：contDiffWithinAt_infty : ContDiffWithinAt 𝕜 ∞ f 
s x ↔ forall n : Nat, ContDiffWithinAt 𝕜 n f s x
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The most general lemma stating that `x ↦ fderivWithin 𝕜 (f x) t (g x)` is `C^n`
at a point within a set.
To show that `x ↦ D_yf(x,y)g(x)` (taken within `t`) is `C^m` at `x₀` within `s`,
 we require that
* `f` is `C^n` at `(x₀, g(x₀))` within `(s ∪ {x₀}) × t` for `n ≥ m+1`.
* `g` is `C^m` at `x₀` within `s`;
* Derivatives are unique at `g(x)` within `t` for `x` sufficiently close to `x₀`
 within `s ∪ {x₀}`;
* `t` is a neighborhood of `g(x₀)` within `g '' s`;
-/
theorem ContDiffWithinAt.fderivWithin'' {f : E → F → G} {g : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 ≤ n)
    (hgt : t ∈ 𝓝[g '' s] g x₀) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  have : ∀ k : ℕ, k ≤ m → ContDiffWithinAt 𝕜 k (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
    intro k hkm
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le <| by grw [hkm, hmn]).hasFDerivWithinAt_nhds (by simp) (hg.of_le hkm) hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  match m with
  | ω =>
    obtain rfl : n = ω := by simpa using hmn
    obtain ⟨v, hv, -, f', hvf', hf'⟩ := hf.hasFDerivWithinAt_nhds (by simp) hg hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  | ∞ =>
    rw [contDiffWithinAt_infty]
    exact fun k ↦ this k (by exact_mod_cast le_top)
  | (m : ℕ) => exact this _ le_rfl

/-- A special case of `ContDiffWithinAt.fderivWithin''` where we require that `s ⊆ g⁻¹(t)`. -/
/-
**ContDiffWithinAt.fderivWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.fderivWithin' {f : E -> F -> G} {g : E -> F} {t : Set F} 
(hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀)) (
hg : ContDiffWithinAt 𝕜 m g s x₀) (ht : forallᶠ x in 𝓝[insert x₀ s] x₀, UniqueDi
ffWithinAt 𝕜 t (g x)) (hmn : m + 1 <= n) (hst : s subseteq g ⁻¹' t) : ContDiffWi
thinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀
参数：hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀)；
hg : ContDiffWithinAt 𝕜 m g s x₀；ht : forallᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiff
WithinAt 𝕜 t (g x)；hmn : m + 1 <= n；hst : s subseteq g ⁻¹' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.fderivWithin''`：ContDiffWithinAt.fderivWithin'' {f : E 
-> F -> G} {g : E -> F} {t : Set F} (hf : ContDiffWithinAt 𝕜 n (Function.uncurry
 f) (insert x₀ s ×ˢ t…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t

--- 原说明 ---
A special case of `ContDiffWithinAt.fderivWithin''` where we require that `s ⊆ g
⁻¹(t)`.
-/
theorem ContDiffWithinAt.fderivWithin' {f : E → F → G} {g : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 ≤ n)
    (hst : s ⊆ g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ :=
  hf.fderivWithin'' hg ht hmn <| mem_of_superset self_mem_nhdsWithin <| image_subset_iff.mpr hst

/-- A special case of `ContDiffWithinAt.fderivWithin'` where we require that `x₀ ∈ s` and there
are unique derivatives everywhere within `t`. -/
/-
**ContDiffWithinAt.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {s : Set E} {x₀ : E} {m n : WithTop 
ℕ∞} {f : E → F → G}   {g : E → F} {t : Set F},   ContDiffWithinAt 𝕜 n (Function.
uncurry f) (s ×ˢ t) (x₀, g x₀) →     ContDiffWithinAt 𝕜 m g s x₀ →       UniqueD
iffOn 𝕜 t →         m + 1 ≤ n → x₀ ∈ s → s ⊆ g ⁻¹' t → ContDiffWithinAt 𝕜 m (fun
 x => fderivWithin 𝕜 (f x) t (g x)) s x₀
参数：Function.uncurry f；s ×ˢ t；x₀, g x₀；fun x => fderivWithin 𝕜 (f x) t (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.fderivWithin'`：ContDiffWithinAt.fderivWithin' {f : E ->
 F -> G} {g : E -> F} {t : Set F} (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f
) (insert x₀ s ×ˢ t)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_eq_self`：insert_eq_self : insert a s = s ↔ a in s
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
A special case of `ContDiffWithinAt.fderivWithin'` where we require that `x₀ ∈ s
` and there
are unique derivatives everywhere within `t`.
-/
protected theorem ContDiffWithinAt.fderivWithin {f : E → F → G} {g : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (ht : UniqueDiffOn 𝕜 t) (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s)
    (hst : s ⊆ g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  rw [← insert_eq_self.mpr hx₀] at hf
  refine hf.fderivWithin' hg ?_ hmn hst
  rw [insert_eq_self.mpr hx₀]
  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)

/-- `x ↦ fderivWithin 𝕜 (f x) t (g x) (k x)` is smooth at a point within a set. -/
/-
**ContDiffWithinAt.fderivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.fderivWithin_apply {f : E -> F -> G} {g k : E -> F} {t : 
Set F} (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀)) (hg 
: ContDiffWithinAt 𝕜 m g s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀) (ht : UniqueDi
ffOn 𝕜 t) (hmn : m + 1 <= n) (hx₀ : x₀ in s) (hst : s subseteq g ⁻¹' t) : ContDi
ffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x) (k x)) s x₀
参数：hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀)；hg : ContD
iffWithinAt 𝕜 m g s x₀；hk : ContDiffWithinAt 𝕜 m k s x₀；ht : UniqueDiffOn 𝕜 t；hm
n : m + 1 <= n；hx₀ : x₀ in s；hst : s subseteq g ⁻¹' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `ContDiff.clm_apply`：ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F
} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x
)
· 使用定理 `contDiff_fst`：contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E)
· 使用定理 `contDiff_snd`：contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F)
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `ContDiffWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} {G : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCom
mGroup E] [inst_2 :…

--- 原说明 ---
`x ↦ fderivWithin 𝕜 (f x) t (g x) (k x)` is smooth at a point within a set.
-/
theorem ContDiffWithinAt.fderivWithin_apply {f : E → F → G} {g k : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀) (ht : UniqueDiffOn 𝕜 t)
    (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s) (hst : s ⊆ g ⁻¹' t) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x) (k x)) s x₀ :=
  (contDiff_fst.clm_apply contDiff_snd).contDiffAt.comp_contDiffWithinAt x₀
    ((hf.fderivWithin hg ht hmn hx₀ hst).prodMk hk)

/-- `fderivWithin 𝕜 f s` is smooth at `x₀` within `s`. -/
/-
**ContDiffWithinAt.fderivWithin_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.fderivWithin_right (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs
 : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (hx₀s : x₀ in s) : ContDiffWithinAt 𝕜 m 
(fderivWithin 𝕜 f s) s x₀
参数：hf : ContDiffWithinAt 𝕜 n f s x₀；hs : UniqueDiffOn 𝕜 s；hmn : m + 1 <= n；hx₀s 
: x₀ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} {G : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCom
mGroup E] [inst_2 :…
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `contDiffWithinAt_snd`：contDiffWithinAt_snd {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.snd : E × F -> F) s p
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_id'`：preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
`fderivWithin 𝕜 f s` is smooth at `x₀` within `s`.
-/
theorem ContDiffWithinAt.fderivWithin_right (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 f s) s x₀ :=
  ContDiffWithinAt.fderivWithin
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hs hmn hx₀s (by rw [preimage_id'])

/-- `x ↦ fderivWithin 𝕜 f s x (k x)` is smooth at `x₀` within `s`. -/
/-
**ContDiffWithinAt.fderivWithin_right_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.fderivWithin_right_apply {f : F -> G} {k : F -> F} {s : S
et F} {x₀ : F} (hf : ContDiffWithinAt 𝕜 n f s x₀) (hk : ContDiffWithinAt 𝕜 m k s
 x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (hx₀s : x₀ in s) : ContDiffWithi
nAt 𝕜 m (fun x => fderivWithin 𝕜 f s x (k x)) s x₀
参数：hf : ContDiffWithinAt 𝕜 n f s x₀；hk : ContDiffWithinAt 𝕜 m k s x₀；hs : Unique
DiffOn 𝕜 s；hmn : m + 1 <= n；hx₀s : x₀ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.fderivWithin_apply`：ContDiffWithinAt.fderivWithin_apply
 {f : E -> F -> G} {g k : E -> F} {t : Set F} (hf : ContDiffWithinAt 𝕜 n (Functi
on.uncurry f) (s ×ˢ t) (x…
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `contDiffWithinAt_snd`：contDiffWithinAt_snd {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.snd : E × F -> F) s p
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_id'`：preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
`x ↦ fderivWithin 𝕜 f s x (k x)` is smooth at `x₀` within `s`.
-/
theorem ContDiffWithinAt.fderivWithin_right_apply
    {f : F → G} {k : F → F} {s : Set F} {x₀ : F}
    (hf : ContDiffWithinAt 𝕜 n f s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 f s x (k x)) s x₀ :=
  ContDiffWithinAt.fderivWithin_apply
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hk hs hmn hx₀s (by rw [preimage_id'])

-- TODO: can we make a version of `ContDiffWithinAt.fderivWithin` for iterated derivatives?
/-
**ContDiffWithinAt.iteratedFDerivWithin_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.iteratedFDerivWithin_right {i : Nat} (hf : ContDiffWithin
At 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + i <= n) (hx₀s : x₀ in s) : Con
tDiffWithinAt 𝕜 m (iteratedFDerivWithin 𝕜 i f s) s x₀
参数：hf : ContDiffWithinAt 𝕜 n f s x₀；hs : UniqueDiffOn 𝕜 s；hmn : m + i <= n；hx₀s 
: x₀ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousLinearMap_comp`：ContDiffWithinAt.continuousLi
nearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithin
At 𝕜 n (g ∘ f) s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ContDiffWithinAt.iteratedFDerivWithin_right {i : ℕ} (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + i ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (iteratedFDerivWithin 𝕜 i f s) s x₀ := by
  induction i generalizing m with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ →L[𝕜] E [×0]→L[𝕜] F)
  | succ i hi =>
    rw [Nat.cast_succ, add_comm _ 1, ← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) ↦ E) F).symm :
        _ →L[𝕜] E [×(i + 1)]→L[𝕜] F)

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth at `x₀`. -/
/-
**ContDiffAt.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x₀ : E} {m n : WithTop ℕ∞} {f : E →
 F → G} {g : E → F},   ContDiffAt 𝕜 n (Function.uncurry f) (x₀, g x₀) →     Cont
DiffAt 𝕜 m g x₀ → m + 1 ≤ n → ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀
参数：Function.uncurry f；x₀, g x₀；fun x => fderiv 𝕜 (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} {G : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCom
mGroup E] [inst_2 :…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
`x ↦ fderiv 𝕜 (f x) (g x)` is smooth at `x₀`.
-/
protected theorem ContDiffAt.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀)
    (hmn : m + 1 ≤ n) : ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ := by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]

@[fun_prop]
/-
**ContDiffAt.fderiv_succ** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {x₀ : E} {m : WithTop ℕ∞} {f : E → F
 → G} {g : E → F},   ContDiffAt 𝕜 (m + 1) (Function.uncurry f) (x₀, g x₀) →     
ContDiffAt 𝕜 m g x₀ → ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀
参数：m + 1；Function.uncurry f；x₀, g x₀；fun x => fderiv 𝕜 (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : T
ype u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [i
nst_2 :…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem ContDiffAt.fderiv_succ {f : E → F → G} {g : E → F}
    (hf : ContDiffAt 𝕜 (m + 1) (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀) :
    ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ :=
  ContDiffAt.fderiv hf hg (le_refl _)

/-- `fderiv 𝕜 f` is smooth at `x₀`. -/
/-
**ContDiffAt.fderiv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 <= n) : Co
ntDiffAt 𝕜 m (fderiv 𝕜 f) x₀
参数：hf : ContDiffAt 𝕜 n f x₀；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : T
ype u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [i
nst_2 :…
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x

--- 原说明 ---
`fderiv 𝕜 f` is smooth at `x₀`.
-/
theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn
/-
**ContDiffAt.fderiv_right_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.fderiv_right_succ (hf : ContDiffAt 𝕜 (n + 1) f x₀) : ContDiffAt
 𝕜 n (fderiv 𝕜 f) x₀
参数：hf : ContDiffAt 𝕜 (n + 1) f x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : T
ype u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [i
nst_2 :…
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ContDiffAt.fderiv_right_succ (hf : ContDiffAt 𝕜 (n + 1) f x₀) :
    ContDiffAt 𝕜 n (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id (le_refl (n + 1))
/-
**ContDiffAt.iteratedFDeriv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.iteratedFDeriv_right {i : Nat} (hf : ContDiffAt 𝕜 n f x₀) (hmn 
: m + i <= n) : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 i f) x₀
参数：hf : ContDiffAt 𝕜 n f x₀；hmn : m + i <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.iteratedFDerivWithin_right`：ContDiffWithinAt.iteratedFD
erivWithin_right {i : Nat} (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn
 𝕜 s) (hmn : m + i <= n) (hx₀s : …
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `trivial`：True
-/
theorem ContDiffAt.iteratedFDeriv_right {i : ℕ} (hf : ContDiffAt 𝕜 n f x₀)
    (hmn : m + i ≤ n) : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 i f) x₀ := by
  rw [← iteratedFDerivWithin_univ, ← contDiffWithinAt_univ] at *
  exact hf.iteratedFDerivWithin_right uniqueDiffOn_univ hmn trivial

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth. -/
/-
**ContDiff.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {m n : WithTop ℕ∞} {f : E → F → G} {
g : E → F},   ContDiff 𝕜 m (Function.uncurry f) → ContDiff 𝕜 n g → n + 1 ≤ m → C
ontDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x)
参数：Function.uncurry f；f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : T
ype u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [i
nst_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
`x ↦ fderiv 𝕜 (f x) (g x)` is smooth.
-/
protected theorem ContDiff.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hnm : n + 1 ≤ m) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

@[fun_prop]
/-
**ContDiff.fderiv_succ** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {n : WithTop ℕ∞} {f : E → F → G} {g 
: E → F},   ContDiff 𝕜 (n + 1) (Function.uncurry f) → ContDiff 𝕜 n g → ContDiff 
𝕜 n fun x => fderiv 𝕜 (f x) (g x)
参数：n + 1；Function.uncurry f；f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : T
ype u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [i
nst_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem ContDiff.fderiv_succ {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 (n + 1) <| Function.uncurry f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl (n + 1))

/-- `fderiv 𝕜 f` is smooth. -/
/-
**ContDiff.fderiv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 <= n) : ContDiff 
𝕜 m (fderiv 𝕜 f)
参数：hf : ContDiff 𝕜 n f；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.fderiv_right`：ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f 
x₀) (hmn : m + 1 <= n) : ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
`fderiv 𝕜 f` is smooth.
-/
theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (fderiv 𝕜 f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn
/-
**ContDiff.iteratedFDeriv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.iteratedFDeriv_right {i : Nat} (hf : ContDiff 𝕜 n f) (hmn : m + i
 <= n) : ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f)
参数：hf : ContDiff 𝕜 n f；hmn : m + i <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.iteratedFDeriv_right`：ContDiffAt.iteratedFDeriv_right {i : Na
t} (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + i <= n) : ContDiffAt 𝕜 m (iteratedFDeri
v 𝕜 i f) x₀
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.iteratedFDeriv_right {i : ℕ} (hf : ContDiff 𝕜 n f)
    (hmn : m + i ≤ n) : ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

@[fun_prop]
/-
**ContDiff.iteratedFDeriv_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.iteratedFDeriv_right' {i : Nat} (hf : ContDiff 𝕜 (m + i) f) : Con
tDiff 𝕜 m (iteratedFDeriv 𝕜 i f)
参数：hf : ContDiff 𝕜 (m + i) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.iteratedFDeriv_right`：ContDiffAt.iteratedFDeriv_right {i : Na
t} (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + i <= n) : ContDiffAt 𝕜 m (iteratedFDeri
v 𝕜 i f) x₀
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ContDiff.iteratedFDeriv_right' {i : ℕ} (hf : ContDiff 𝕜 (m + i) f) :
    ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right (le_refl _)

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is continuous. -/
/-
**Continuous.fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.fderiv {f : E -> F -> G} {g : E -> F} (hf : ContDiff 𝕜 n <| Fun
ction.uncurry f) (hg : Continuous g) (hn : 1 <= n) : Continuous fun x => fderiv 
𝕜 (f x) (g x)
参数：hf : ContDiff 𝕜 n <| Function.uncurry f；hg : Continuous g；hn : 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `ContDiff.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f

--- 原说明 ---
`x ↦ fderiv 𝕜 (f x) (g x)` is continuous.
-/
theorem Continuous.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 n <| Function.uncurry f) (hg : Continuous g) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

@[fun_prop]
/-
**Continuous.fderiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.fderiv_one {f : E -> F -> G} {g : E -> F} (hf : ContDiff 𝕜 1 <|
 Function.uncurry f) (hg : Continuous g) : Continuous fun x => _root_.fderiv 𝕜 (
f x) (g x)
参数：hf : ContDiff 𝕜 1 <| Function.uncurry f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `ContDiff.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Continuous.fderiv_one {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 1 <| Function.uncurry f) (hg : Continuous g) :
    Continuous fun x => _root_.fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) (le_refl 1)).continuous

@[fun_prop]
/-
**Differentiable.fderiv_two** 是 Mathlib 中的一个定理，位于命名空间 `Differentiable`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜
 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {f : E → F → G} {g : E → F},   ContD
iff 𝕜 2 (Function.uncurry f) → ContDiff 𝕜 1 g → Differentiable 𝕜 fun x => fderiv
 𝕜 (f x) (g x)
参数：Function.uncurry f；f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContDiff.differentiable`：ContDiff.differentiable (h : ContDiff 𝕜 n f) (h
n : n != 0) : Differentiable 𝕜 f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : T
ype u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [i
nst_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
protected theorem Differentiable.fderiv_two {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 2 <| Function.uncurry f) (hg : ContDiff 𝕜 1 g) :
    Differentiable 𝕜 fun x => fderiv 𝕜 (f x) (g x) :=
  ContDiff.differentiable
    (contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl 2))
    one_ne_zero

/-- `x ↦ fderiv 𝕜 (f x) (g x) (k x)` is smooth. -/
/-
**ContDiff.fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.fderiv_apply {f : E -> F -> G} {g k : E -> F} (hf : ContDiff 𝕜 m 
<| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hk : ContDiff 𝕜 n k) (hnm : n + 1 
<= m) : ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) (k x)
参数：hf : ContDiff 𝕜 m <| Function.uncurry f；hg : ContDiff 𝕜 n g；hk : ContDiff 𝕜 n
 k；hnm : n + 1 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.clm_apply`：ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F
} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x
)
· 使用定理 `ContDiff.fderiv`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…

--- 原说明 ---
`x ↦ fderiv 𝕜 (f x) (g x) (k x)` is smooth.
-/
theorem ContDiff.fderiv_apply {f : E → F → G} {g k : E → F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hk : ContDiff 𝕜 n k)
    (hnm : n + 1 ≤ m) : ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) (k x) :=
  (hf.fderiv hg hnm).clm_apply hk

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
/-
**contDiffOn_fderivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_fderivWithin_apply {s : Set E} {f : E -> F} (hf : ContDiffOn 𝕜 
n f s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) : ContDiffOn 𝕜 m (fun p : E × 
E => (fderivWithin 𝕜 f s p.1 : E ->L[𝕜] F) p.2) (s ×ˢ univ)
参数：hf : ContDiffOn 𝕜 n f s；hs : UniqueDiffOn 𝕜 s；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.clm_apply`：ContDiffOn.clm_apply {f : E -> F ->L[𝕜] G} {g : E 
-> F} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun 
x => (f x)…
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `ContDiffOn.fderivWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F
 : Type uF} […
· 使用定理 `contDiffOn_fst`：contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.
fst : E × F -> E) s
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
· 使用定理 `contDiffOn_snd`：contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.
snd : E × F -> F) s

--- 原说明 ---
The bundled derivative of a `C^{n+1}` function is `C^n`.
-/
theorem contDiffOn_fderivWithin_apply {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E →L[𝕜] F) p.2) (s ×ˢ univ) :=
  ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
    contDiffOn_snd

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
/-
**ContDiffOn.continuousOn_fderivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_fderivWithin_apply (hf : ContDiffOn 𝕜 n f s) (hs :
 UniqueDiffOn 𝕜 s) (hn : 1 <= n) : ContinuousOn (fun p : E × E => (fderivWithin 
𝕜 f s p.1 : E -> F) p.2) (s ×ˢ univ)
参数：hf : ContDiffOn 𝕜 n f s；hs : UniqueDiffOn 𝕜 s；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `contDiffOn_fderivWithin_apply`：contDiffOn_fderivWithin_apply {s : Set E}
 {f : E -> F} (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= 
n) : ContDiffOn 𝕜 m…

--- 原说明 ---
If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df
(x) v`) is
continuous.
-/
theorem ContDiffOn.continuousOn_fderivWithin_apply (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) :
    ContinuousOn (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E → F) p.2) (s ×ˢ univ) :=
  (contDiffOn_fderivWithin_apply (m := 0) hf hs hn).continuousOn

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
/-
**ContDiff.contDiff_fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.contDiff_fderiv_apply {f : E -> F} (hf : ContDiff 𝕜 n f) (hmn : m
 + 1 <= n) : ContDiff 𝕜 m fun p : E × E => (fderiv 𝕜 f p.1 : E ->L[𝕜] F) p.2
参数：hf : ContDiff 𝕜 n f；hmn : m + 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `contDiffOn_fderivWithin_apply`：contDiffOn_fderivWithin_apply {s : Set E}
 {f : E -> F} (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= 
n) : ContDiffOn 𝕜 m…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The bundled derivative of a `C^{n+1}` function is `C^n`.
-/
theorem ContDiff.contDiff_fderiv_apply {f : E → F} (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m fun p : E × E => (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2 := by
  rw [← contDiffOn_univ] at hf ⊢
  rw [← fderivWithin_univ, ← univ_prod_univ]
  exact contDiffOn_fderivWithin_apply hf uniqueDiffOn_univ hmn
/-
**ContDiffWithinAt.continuousWithinAt_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.continuousWithinAt_fderivWithin (hf : ContDiffWithinAt 𝕜 
n f s x) (hs : UniqueDiffOn 𝕜 s) (hn : n != 0) (hx : x in s) : ContinuousWithinA
t (fderivWithin 𝕜 f s) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hs : UniqueDiffOn 𝕜 s；hn : n != 0；hx : x in s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem ContDiffWithinAt.continuousWithinAt_fderivWithin
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hn : n ≠ 0) (hx : x ∈ s) :
    ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
  hf.fderivWithin_right (m := 0) hs (by simpa [ENat.one_le_iff_ne_zero_withTop]) hx
    |>.continuousWithinAt
/-
**ContDiffAt.continuousAt_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.continuousAt_fderiv (hf : ContDiffAt 𝕜 n f x) (hn : n != 0) : C
ontinuousAt (fderiv 𝕜 f) x
参数：hf : ContDiffAt 𝕜 n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `ContDiffAt.fderiv_right`：ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f 
x₀) (hmn : m + 1 <= n) : ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem ContDiffAt.continuousAt_fderiv (hf : ContDiffAt 𝕜 n f x) (hn : n ≠ 0) :
    ContinuousAt (fderiv 𝕜 f) x :=
  hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop]) |>.continuousAt
/-
**ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin {k : Nat} (hf : C
ontDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hk : k <= n) (hx : x in s) :
 ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hs : UniqueDiffOn 𝕜 s；hk : k <= n；hx : x in s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x
· 使用定理 `ContDiffWithinAt.iteratedFDerivWithin_right`：ContDiffWithinAt.iteratedFD
erivWithin_right {i : Nat} (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn
 𝕜 s) (hmn : m + i <= n) (hx₀s : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin {k : ℕ}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hk : k ≤ n) (hx : x ∈ s) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s x :=
  hf.iteratedFDerivWithin_right (m := 0) hs (by simpa) hx |>.continuousWithinAt
/-
**ContinuousOn.continuousOn_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuousOn_iteratedFDerivWithin {k : Nat} (hf : ContDiffOn 
𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hk : k <= n) : ContinuousOn (iteratedFDerivWit
hin 𝕜 k f s) s
参数：hf : ContDiffOn 𝕜 n f s；hs : UniqueDiffOn 𝕜 s；hk : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin`：ContDiffWithin
At.continuousWithinAt_iteratedFDerivWithin {k : Nat} (hf : ContDiffWithinAt 𝕜 n 
f s x) (hs : UniqueDiffOn 𝕜 s) (hk : k <= n) (…
· 使用定理 `ContDiffOn.contDiffWithinAt`：ContDiffOn.contDiffWithinAt (h : ContDiffOn
 𝕜 n f s) (hx : x in s) : ContDiffWithinAt 𝕜 n f s x
-/
theorem ContinuousOn.continuousOn_iteratedFDerivWithin {k : ℕ}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hk : k ≤ n) :
    ContinuousOn (iteratedFDerivWithin 𝕜 k f s) s :=
  fun _x hx ↦ hf.contDiffWithinAt hx |>.continuousWithinAt_iteratedFDerivWithin hs hk hx
/-
**ContDiffAt.continuousAt_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.continuousAt_iteratedFDeriv {k : Nat} (hf : ContDiffAt 𝕜 n f x)
 (hk : k <= n) : ContinuousAt (iteratedFDeriv 𝕜 k f) x
参数：hf : ContDiffAt 𝕜 n f x；hk : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `ContDiffAt.iteratedFDeriv_right`：ContDiffAt.iteratedFDeriv_right {i : Na
t} (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + i <= n) : ContDiffAt 𝕜 m (iteratedFDeri
v 𝕜 i f) x₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem ContDiffAt.continuousAt_iteratedFDeriv {k : ℕ} (hf : ContDiffAt 𝕜 n f x) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) x :=
  hf.iteratedFDeriv_right (m := 0) (by simpa) |>.continuousAt
/-
**ContinuousOn.continuousOn_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuousOn_iteratedFDeriv {k : Nat} (hf : ContDiffOn 𝕜 n f 
s) (hs : IsOpen s) (hk : k <= n) : ContinuousOn (iteratedFDeriv 𝕜 k f) s
参数：hf : ContDiffOn 𝕜 n f s；hs : IsOpen s；hk : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiffAt.continuousAt_iteratedFDeriv`：ContDiffAt.continuousAt_iterated
FDeriv {k : Nat} (hf : ContDiffAt 𝕜 n f x) (hk : k <= n) : ContinuousAt (iterate
dFDeriv 𝕜 k f) x
· 使用定理 `ContDiffOn.contDiffAt`：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (h
x : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem ContinuousOn.continuousOn_iteratedFDeriv {k : ℕ}
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hk : k ≤ n) :
    ContinuousOn (iteratedFDeriv 𝕜 k f) s :=
  fun _x hx ↦ hf.contDiffAt (hs.mem_nhds hx) |>.continuousAt_iteratedFDeriv hk |>.continuousWithinAt

end bundled

