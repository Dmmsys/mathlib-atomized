/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
## Basic properties of `C^n` functions between manifolds

In this file, we show that standard operations on `C^n` maps between manifolds are `C^n` :
* `ContMDiffOn.comp` gives the invariance of the `Cⁿ` property under composition
* `contMDiff_id` gives the smoothness of the identity
* `contMDiff_const` gives the smoothness of constant functions
* `contMDiff_inclusion` shows that the inclusion between open sets of a topological space is `C^n`
* `contMDiff_isOpenEmbedding` shows that if `M` has a `ChartedSpace` structure induced by an open
  embedding `e : M → H`, then `e` is `C^n`.

## Tags
chain rule, manifolds, higher derivative

-/

public section

assert_not_exists mfderiv

open Filter Function Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare the prerequisites for a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  -- declare the prerequisites for a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  -- declare the prerequisites for a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']

section ChartedSpace
variable [ChartedSpace H M] [ChartedSpace H' M'] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {f : M → M'} {s : Set M} {x : M} {n : ℕ∞ω}

/-! ### Regularity of the composition of `C^n` functions between manifolds -/

section Composition

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
/-
**ContMDiffWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M''} (x : M) (hg : ContMDif
fWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) (st : MapsTo
 f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x
参数：x : M；hg : ContMDiffWithinAt I' I'' n g t (f x)；hf : ContMDiffWithinAt I I' n
 f s x；st : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The composition of `C^n` functions within domains at points is `C^n`.
-/
theorem ContMDiffWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  rw [contMDiffWithinAt_iff] at hg hf ⊢
  refine ⟨hg.1.comp hf.1 st, ?_⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg
  have A : ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x, f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source := by
    simp only [e, ← map_extChartAt_nhdsWithin, eventually_map]
    filter_upwards [hf.1.tendsto (extChartAt_source_mem_nhds (I := I') (f x)),
      inter_mem_nhdsWithin s (extChartAt_source_mem_nhds (I := I) x)]
    rintro x' (hfx' : f x' ∈ e'.source) ⟨hx's, hx'⟩
    simp only [e, true_and, e.left_inv hx', st hx's, *]
  refine ((hg.2.comp _ (hf.2.mono inter_subset_right)
      ((mapsTo_preimage _ _).mono_left inter_subset_left)).mono_of_mem_nhdsWithin
      (inter_mem ?_ self_mem_nhdsWithin)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [A]
    rintro x' ⟨ht, hfx'⟩
    simp only [*, e, e', mem_preimage, writtenInExtChartAt, (· ∘ ·), mem_inter_iff, e'.left_inv,
      true_and]
    exact mem_range_self _
  · filter_upwards [A]
    rintro x' ⟨-, hfx'⟩
    simp only [*, e, e', (· ∘ ·), writtenInExtChartAt, e'.left_inv]
  · simp only [e, e', writtenInExtChartAt, (· ∘ ·), mem_extChartAt_source,
      e.left_inv, e'.left_inv]

/-- See note [comp_of_eq lemmas] -/
/-
**ContMDiffWithinAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.comp_of_eq {t : Set M'} {g : M' -> M''} {x : M} {y : M'}
 (hg : ContMDiffWithinAt I' I'' n g t y) (hf : ContMDiffWithinAt I I' n f s x) (
st : MapsTo f s t) (hx : f x = y) : ContMDiffWithinAt I I'' n (g ∘ f) s x
参数：hg : ContMDiffWithinAt I' I'' n g t y；hf : ContMDiffWithinAt I I' n f s x；st 
: MapsTo f s t；hx : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…

--- 原说明 ---
See note [comp_of_eq lemmas]
-/
theorem ContMDiffWithinAt.comp_of_eq {t : Set M'} {g : M' → M''} {x : M} {y : M'}
    (hg : ContMDiffWithinAt I' I'' n g t y) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) (hx : f x = y) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp x hf st

/-- The composition of `C^n` functions on domains is `C^n`. -/
/-
**ContMDiffOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g
 t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) : ContMDiffOn I I'' 
n (g ∘ f) s
参数：hg : ContMDiffOn I' I'' n g t；hf : ContMDiffOn I I' n f s；st : s subseteq f ⁻
¹' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…

--- 原说明 ---
The composition of `C^n` functions on domains is `C^n`.
-/
theorem ContMDiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) (st : s ⊆ f ⁻¹' t) : ContMDiffOn I I'' n (g ∘ f) s := fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
/-
**ContMDiffOn.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.comp' {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n 
g t) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) (s inter f ⁻¹' 
t)
参数：hg : ContMDiffOn I' I'' n g t；hf : ContMDiffOn I I' n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The composition of `C^n` functions on domains is `C^n`.
-/
theorem ContMDiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/-- The composition of `C^n` functions is `C^n`. -/
/-
**ContMDiff.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff
 I I' n f) : ContMDiff I I'' n (g ∘ f)
参数：hg : ContMDiff I' I'' n g；hf : ContMDiff I I' n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ

--- 原说明 ---
The composition of `C^n` functions is `C^n`.
-/
theorem ContMDiff.comp {g : M' → M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
    ContMDiff I I'' n (g ∘ f) := by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
/-
**ContMDiffWithinAt.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.comp' {t : Set M'} {g : M' -> M''} (x : M) (hg : ContMDi
ffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) : ContMDiff
WithinAt I I'' n (g ∘ f) (s inter f ⁻¹' t) x
参数：x : M；hg : ContMDiffWithinAt I' I'' n g t (f x)；hf : ContMDiffWithinAt I I' n
 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `ContMDiffWithinAt.mono`：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I
 I' n f s x) (hts : t subseteq s) : ContMDiffWithinAt I I' n f t x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The composition of `C^n` functions within domains at points is `C^n`.
-/
theorem ContMDiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
/-
**ContMDiffAt.comp_contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.comp_contMDiffWithinAt {g : M' -> M''} (x : M) (hg : ContMDiff
At I' I'' n g (f x)) (hf : ContMDiffWithinAt I I' n f s x) : ContMDiffWithinAt I
 I'' n (g ∘ f) s x
参数：x : M；hg : ContMDiffAt I' I'' n g (f x)；hf : ContMDiffWithinAt I I' n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
`g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`.
-/
theorem ContMDiffAt.comp_contMDiffWithinAt {g : M' → M''} (x : M)
    (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
/-
**ContMDiffAt.comp_contMDiffWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.comp_contMDiffWithinAt_of_eq {g : M' -> M''} {x : M} {y : M'} 
(hg : ContMDiffAt I' I'' n g y) (hf : ContMDiffWithinAt I I' n f s x) (hx : f x 
= y) : ContMDiffWithinAt I I'' n (g ∘ f) s x
参数：hg : ContMDiffAt I' I'' n g y；hf : ContMDiffWithinAt I I' n f s x；hx : f x = 
y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…

--- 原说明 ---
`g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`.
-/
theorem ContMDiffAt.comp_contMDiffWithinAt_of_eq {g : M' → M''} {x : M} {y : M'}
    (hg : ContMDiffAt I' I'' n g y) (hf : ContMDiffWithinAt I I' n f s x) (hx : f x = y) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp_contMDiffWithinAt x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContMDiffAt.comp {g : M' → M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x))
    (hf : ContMDiffAt I I' n f x) : ContMDiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

/-- See note [comp_of_eq lemmas] -/
/-
**ContMDiffAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.comp_of_eq {g : M' -> M''} {x : M} {y : M'} (hg : ContMDiffAt 
I' I'' n g y) (hf : ContMDiffAt I I' n f x) (hx : f x = y) : ContMDiffAt I I'' n
 (g ∘ f) x
参数：hg : ContMDiffAt I' I'' n g y；hf : ContMDiffAt I I' n f x；hx : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…

--- 原说明 ---
See note [comp_of_eq lemmas]
-/
theorem ContMDiffAt.comp_of_eq {g : M' → M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
    (hf : ContMDiffAt I I' n f x) (hx : f x = y) : ContMDiffAt I I'' n (g ∘ f) x := by
  subst hx; exact hg.comp x hf
/-
**ContMDiff.comp_contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.comp_contMDiffOn {f : M -> M'} {g : M' -> M''} {s : Set M} (hg :
 ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ 
f) s
参数：hg : ContMDiff I' I'' n g；hf : ContMDiffOn I I' n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ
-/
theorem ContMDiff.comp_contMDiffOn {f : M → M'} {g : M' → M''} {s : Set M}
    (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) s :=
  hg.contMDiffOn.comp hf Set.subset_preimage_univ
/-
**ContMDiffOn.comp_contMDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.comp_contMDiff {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn 
I' I'' n g t) (hf : ContMDiff I I' n f) (ht : forall x, f x in t) : ContMDiff I 
I'' n (g ∘ f)
参数：hg : ContMDiffOn I' I'' n g t；hf : ContMDiff I I' n f；ht : forall x, f x in t
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
-/
theorem ContMDiffOn.comp_contMDiff {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiff I I' n f) (ht : ∀ x, f x ∈ t) : ContMDiff I I'' n (g ∘ f) :=
  contMDiffOn_univ.mp <| hg.comp hf.contMDiffOn fun x _ => ht x

end Composition

/-! ### The identity is `C^n` -/

section id

/-
**contMDiff_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_id : ContMDiff I I n (id : M -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftProp_id`：liftProp_id (hG : G.Lo
calInvariantProp G Q) (hQ : forall y, Q id univ y) : LiftProp Q (id : M -> M)
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `contDiffWithinAtProp_id`：contDiffWithinAtProp_id (x : H) : ContDiffWithi
nAtProp I I n id univ x
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem contMDiff_id : ContMDiff I I n (id : M → M) :=
  ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp ⊤).liftProp_id contDiffWithinAtProp_id) le_top
/-
**contMDiffOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_id : ContMDiffOn I I n (id : M -> M) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
-/
theorem contMDiffOn_id : ContMDiffOn I I n (id : M → M) s :=
  contMDiff_id.contMDiffOn
/-
**contMDiffAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
-/
theorem contMDiffAt_id : ContMDiffAt I I n (id : M → M) x :=
  contMDiff_id.contMDiffAt
/-
**contMDiffWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id : M -> M) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x
-/
theorem contMDiffWithinAt_id : ContMDiffWithinAt I I n (id : M → M) s x :=
  contMDiffAt_id.contMDiffWithinAt

end id

/-! ### Iterated functions -/

section Iterate

/-- The iterates of `C^n` functions on domains are `C^n`. -/
/-
**ContMDiffOn.iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.iterate {f : M -> M} (hf : ContMDiffOn I I n f s) (hmaps : Set
.MapsTo f s s) (k : Nat) : ContMDiffOn I I n (f^[k]) s
参数：hf : ContMDiffOn I I n f s；hmaps : Set.MapsTo f s s；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_id`：contMDiffOn_id : ContMDiffOn I I n (id : M -> M) s
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…

--- 原说明 ---
The iterates of `C^n` functions on domains are `C^n`.
-/
theorem ContMDiffOn.iterate {f : M → M} (hf : ContMDiffOn I I n f s)
    (hmaps : Set.MapsTo f s s) (k : ℕ) :
    ContMDiffOn I I n (f^[k]) s := by
  induction k with
  | zero => simpa using contMDiffOn_id
  | succ k h => simpa using h.comp hf hmaps

/-- The iterates of `C^n` functions are `C^n`. -/
/-
**ContMDiff.iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.iterate {f : M -> M} (hf : ContMDiff I I n f) (k : Nat) : ContMD
iff I I n (f^[k])
参数：hf : ContMDiff I I n f；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `ContMDiffOn.iterate`：ContMDiffOn.iterate {f : M -> M} (hf : ContMDiffOn 
I I n f s) (hmaps : Set.MapsTo f s s) (k : Nat) : ContMDiffOn I I n (f^[k]) s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
The iterates of `C^n` functions are `C^n`.
-/
theorem ContMDiff.iterate {f : M → M} (hf : ContMDiff I I n f) (k : ℕ) :
    ContMDiff I I n (f^[k]) :=
  contMDiffOn_univ.mp ((contMDiffOn_univ.mpr hf).iterate (univ.mapsTo_univ f) k)

end Iterate

/-! ### Constants are `C^n` -/

section const
variable {c : M'}

/-
**contMDiff_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_const : ContMDiff I I' n fun _ : M => c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
-/
theorem contMDiff_const : ContMDiff I I' n fun _ : M => c := by
  intro x
  refine ⟨by fun_prop, ?_⟩
  simp only [ContDiffWithinAtProp, Function.comp_def]
  exact contDiffWithinAt_const

@[to_additive]
/-
**contMDiff_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_one [One M'] : ContMDiff I I' n (1 : M -> M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem contMDiff_one [One M'] : ContMDiff I I' n (1 : M → M') := by
  simp only [Pi.one_def, contMDiff_const]
/-
**contMDiffOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
-/
theorem contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => c) s :=
  contMDiff_const.contMDiffOn

@[to_additive]
/-
**contMDiffOn_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_one [One M'] : ContMDiffOn I I' n (1 : M -> M') s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `contMDiff_one`：contMDiff_one [One M'] : ContMDiff I I' n (1 : M -> M')
-/
theorem contMDiffOn_one [One M'] : ContMDiffOn I I' n (1 : M → M') s :=
  contMDiff_one.contMDiffOn
/-
**contMDiffAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => c) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
-/
theorem contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => c) x :=
  contMDiff_const.contMDiffAt

@[to_additive]
/-
**contMDiffAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_one [One M'] : ContMDiffAt I I' n (1 : M -> M') x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_one`：contMDiff_one [One M'] : ContMDiff I I' n (1 : M -> M')
-/
theorem contMDiffAt_one [One M'] : ContMDiffAt I I' n (1 : M → M') x :=
  contMDiff_one.contMDiffAt
/-
**contMDiffWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_const : ContMDiffWithinAt I I' n (fun _ : M => c) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
-/
theorem contMDiffWithinAt_const : ContMDiffWithinAt I I' n (fun _ : M => c) s x :=
  contMDiffAt_const.contMDiffWithinAt

@[to_additive]
/-
**contMDiffWithinAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_one [One M'] : ContMDiffWithinAt I I' n (1 : M -> M') s 
x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
-/
theorem contMDiffWithinAt_one [One M'] : ContMDiffWithinAt I I' n (1 : M → M') s x :=
  contMDiffAt_const.contMDiffWithinAt

@[nontriviality]
/-
**contMDiff_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_of_subsingleton [Subsingleton M'] : ContMDiff I I' n f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
-/
theorem contMDiff_of_subsingleton [Subsingleton M'] : ContMDiff I I' n f := by
  intro x
  rw [Subsingleton.elim f fun _ => (f x)]
  exact contMDiffAt_const

@[nontriviality]
/-
**contMDiffAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_of_subsingleton [Subsingleton M'] : ContMDiffAt I I' n f x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_of_subsingleton`：contMDiff_of_subsingleton [Subsingleton M'] :
 ContMDiff I I' n f
-/
theorem contMDiffAt_of_subsingleton [Subsingleton M'] : ContMDiffAt I I' n f x :=
  contMDiff_of_subsingleton.contMDiffAt

@[nontriviality]
/-
**contMDiffWithinAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_of_subsingleton [Subsingleton M'] : ContMDiffWithinAt I 
I' n f s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `contMDiffAt_of_subsingleton`：contMDiffAt_of_subsingleton [Subsingleton M
'] : ContMDiffAt I I' n f x
-/
theorem contMDiffWithinAt_of_subsingleton [Subsingleton M'] : ContMDiffWithinAt I I' n f s x :=
  contMDiffAt_of_subsingleton.contMDiffWithinAt

@[nontriviality]
/-
**contMDiffOn_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_of_subsingleton [Subsingleton M'] : ContMDiffOn I I' n f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `contMDiff_of_subsingleton`：contMDiff_of_subsingleton [Subsingleton M'] :
 ContMDiff I I' n f
-/
theorem contMDiffOn_of_subsingleton [Subsingleton M'] : ContMDiffOn I I' n f s :=
  contMDiff_of_subsingleton.contMDiffOn
/-
**contMDiff_of_discreteTopology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_of_discreteTopology [DiscreteTopology M] : ContMDiff I I' n f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma contMDiff_of_discreteTopology [DiscreteTopology M] :
    ContMDiff I I' n f := by
  intro x
  -- f is locally constant, and constant functions are smooth.
  apply contMDiff_const (c := f x).contMDiffAt.congr_of_eventuallyEq
  simp [EventuallyEq]

end const

/-- `f` is continuously differentiable if it is cont. differentiable at
each `x ∈ mulTSupport f`. -/
@[to_additive /-- `f` is continuously differentiable if it is continuously
differentiable at each `x ∈ tsupport f`. See also `contMDiff_section_of_tsupport`
for a similar result for sections of vector bundles. -/]
/-
**contMDiff_of_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_of_mulTSupport [One M'] {f : M -> M'} (hf : forall x in mulTSupp
ort f, ContMDiffAt I I' n f x) : ContMDiff I I' n f
参数：hf : forall x in mulTSupport f, ContMDiffAt I I' n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `notMem_mulTSupport_iff_eventuallyEq`：notMem_mulTSupport_iff_eventuallyEq
 : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1
-/
theorem contMDiff_of_mulTSupport [One M'] {f : M → M'}
    (hf : ∀ x ∈ mulTSupport f, ContMDiffAt I I' n f x) : ContMDiff I I' n f := by
  intro x
  by_cases hx : x ∈ mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_mulTSupport_iff_eventuallyEq.1 hx)

@[to_additive contMDiffWithinAt_of_notMem]
/-
**contMDiffWithinAt_of_notMem_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_of_notMem_mulTSupport {f : M -> M'} [One M'] {x : M} (hx
 : x ∉ mulTSupport f) (n : Nat∞ω) (s : Set M) : ContMDiffWithinAt I I' n f s x
参数：hx : x ∉ mulTSupport f；n : Nat∞ω；s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `notMem_mulTSupport_iff_eventuallyEq`：notMem_mulTSupport_iff_eventuallyEq
 : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1
· 使用定理 `image_eq_one_of_notMem_mulTSupport`：image_eq_one_of_notMem_mulTSupport {
f : X -> α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1
-/
theorem contMDiffWithinAt_of_notMem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : ℕ∞ω) (s : Set M) : ContMDiffWithinAt I I' n f s x := by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| notMem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_notMem_mulTSupport hx)

/-- `f` is continuously differentiable at each point outside of its `mulTSupport`. -/
@[to_additive contMDiffAt_of_notMem]
/-
**contMDiffAt_of_notMem_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_of_notMem_mulTSupport {f : M -> M'} [One M'] {x : M} (hx : x ∉
 mulTSupport f) (n : Nat∞ω) : ContMDiffAt I I' n f x
参数：hx : x ∉ mulTSupport f；n : Nat∞ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_of_notMem_mulTSupport`：contMDiffWithinAt_of_notMem_mul
TSupport {f : M -> M'} [One M'] {x : M} (hx : x ∉ mulTSupport f) (n : Nat∞ω) (s 
: Set M) : ContMDiffWithinAt …

--- 原说明 ---
`f` is continuously differentiable at each point outside of its `mulTSupport`.
-/
theorem contMDiffAt_of_notMem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : ℕ∞ω) : ContMDiffAt I I' n f x :=
  contMDiffWithinAt_of_notMem_mulTSupport hx n univ

/-- Given two `C^n` functions `f` and `g` which coincide locally around the frontier of a set `s`,
then the piecewise function defined using `f` on `s` and `g` elsewhere is `C^n`. -/
/-
**ContMDiff.piecewise** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.piecewise {f g : M -> M'} {s : Set M} [DecidablePred (· in s)] (
hf : ContMDiff I I' n f) (hg : ContMDiff I I' n g) (hfg : forall x in frontier s
, f =ᶠ[𝓝 x] g) : ContMDiff I I' n (piecewise s f g)
参数：· in s；hf : ContMDiff I I' n f；hg : ContMDiff I I' n g；hfg : forall x in fron
tier s, f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
Given two `C^n` functions `f` and `g` which coincide locally around the frontier
 of a set `s`,
then the piecewise function defined using `f` on `s` and `g` elsewhere is `C^n`.
-/
lemma ContMDiff.piecewise
    {f g : M → M'} {s : Set M} [DecidablePred (· ∈ s)]
    (hf : ContMDiff I I' n f) (hg : ContMDiff I I' n g)
    (hfg : ∀ x ∈ frontier s, f =ᶠ[𝓝 x] g) :
    ContMDiff I I' n (piecewise s f g) := by
  intro x
  by_cases hx : x ∈ interior s
  · apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [piecewise_eq_of_mem]
    apply interior_subset hy
  by_cases h'x : x ∈ closure s
  · have : x ∈ frontier s := ⟨h'x, hx⟩
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [hfg x this] with y hy
    simp [Set.piecewise, hy]
  · apply (hg x).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h'x] with y hy
    rw [piecewise_eq_of_notMem]
    contrapose hy
    simpa using subset_closure hy

/-- Given two `C^n` functions `f` and `g` from `ℝ` to a real manifold which coincide locally
around a point `s`, then the piecewise function using `f` before `t` and `g` after is `C^n`. -/
/-
**ContMDiff.piecewise_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.piecewise_Iic {E : Type*} [NormedAddCommGroup E] [NormedSpace Re
al E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} {M : Type
*} [TopologicalSpace M] [ChartedSpace H M] {f g : Real -> M} {s : Real} (hf : Co
ntMDiff 𝓘(Real) I n f) (hg : ContMDiff 𝓘(Real) I n g) (hfg : f =ᶠ[𝓝 s] g) : Cont
MDiff 𝓘(Real) I n (Set.piecewise (Iic s) f g)
参数：hf : ContMDiff 𝓘(Real) I n f；hg : ContMDiff 𝓘(Real) I n g；hfg : f =ᶠ[𝓝 s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiff.piecewise`：ContMDiff.piecewise {f g : M -> M'} {s : Set M} [De
cidablePred (· in s)] (hf : ContMDiff I I' n f) (hg : ContMDiff I I' n g) (hfg :
 forall x…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_Iic'`：frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier 
(Iic a) = {a}
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R

--- 原说明 ---
Given two `C^n` functions `f` and `g` from `ℝ` to a real manifold which coincide
 locally
around a point `s`, then the piecewise function using `f` before `t` and `g` aft
er is `C^n`.
-/
lemma ContMDiff.piecewise_Iic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f g : ℝ → M} {s : ℝ}
    (hf : ContMDiff 𝓘(ℝ) I n f) (hg : ContMDiff 𝓘(ℝ) I n g) (hfg : f =ᶠ[𝓝 s] g) :
    ContMDiff 𝓘(ℝ) I n (Set.piecewise (Iic s) f g) :=
  hf.piecewise hg (by simpa using hfg)

/-! ### Being `C^k` on a union of open sets can be tested on each set -/
section contMDiff_union

variable {s t : Set M}

/-- If a function is `C^k` on two open sets, it is also `C^n` on their union. -/
/-
**ContMDiffOn.union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.union_of_isOpen (hf : ContMDiffOn I I' n f s) (hf' : ContMDiff
On I I' n f t) (hs : IsOpen s) (ht : IsOpen t) : ContMDiffOn I I' n f (s union t
)
参数：hf : ContMDiffOn I I' n f s；hf' : ContMDiffOn I I' n f t；hs : IsOpen s；ht : I
sOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is `C^k` on two open sets, it is also `C^n` on their union.
-/
lemma ContMDiffOn.union_of_isOpen (hf : ContMDiffOn I I' n f s) (hf' : ContMDiffOn I I' n f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiffOn I I' n f (s ∪ t) := by
  intro x hx
  obtain (hx | hx) := hx
  · exact (hf x hx).contMDiffAt (hs.mem_nhds hx) |>.contMDiffWithinAt
  · exact (hf' x hx).contMDiffAt (ht.mem_nhds hx) |>.contMDiffWithinAt

/-- A function is `C^k` on two open sets iff it is `C^k` on their union. -/
/-
**contMDiffOn_union_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) : ContMDif
fOn I I' n f (s union t) ↔ ContMDiffOn I I' n f s ∧ ContMDiffOn I I' n f t
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `ContMDiffOn.union_of_isOpen`：ContMDiffOn.union_of_isOpen (hf : ContMDiff
On I I' n f s) (hf' : ContMDiffOn I I' n f t) (hs : IsOpen s) (ht : IsOpen t) : 
ContMDiffOn I I' …

--- 原说明 ---
A function is `C^k` on two open sets iff it is `C^k` on their union.
-/
lemma contMDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiffOn I I' n f (s ∪ t) ↔ ContMDiffOn I I' n f s ∧ ContMDiffOn I I' n f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ ↦ ContMDiffOn.union_of_isOpen hfs hft hs ht⟩
/-
**contMDiff_of_contMDiffOn_union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_of_contMDiffOn_union_of_isOpen (hf : ContMDiffOn I I' n f s) (hf
' : ContMDiffOn I I' n f t) (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpe
n t) : ContMDiff I I' n f
参数：hf : ContMDiffOn I I' n f s；hf' : ContMDiffOn I I' n f t；hst : s union t = un
iv；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用引理 `ContMDiffOn.union_of_isOpen`：ContMDiffOn.union_of_isOpen (hf : ContMDiff
On I I' n f s) (hf' : ContMDiffOn I I' n f t) (hs : IsOpen s) (ht : IsOpen t) : 
ContMDiffOn I I' …
-/
lemma contMDiff_of_contMDiffOn_union_of_isOpen (hf : ContMDiffOn I I' n f s)
    (hf' : ContMDiffOn I I' n f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiff I I' n f := by
  rw [← contMDiffOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is `C^k` on open sets `s i`, it is `C^k` on their union -/
/-
**ContMDiffOn.iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set M} (hf : forall i :
 ι, ContMDiffOn I I' n f (s i)) (hs : forall i, IsOpen (s i)) : ContMDiffOn I I'
 n f (⋃ i, s i)
参数：hf : forall i : ι, ContMDiffOn I I' n f (s i)；hs : forall i, IsOpen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is `C^k` on open sets `s i`, it is `C^k` on their union
-/
lemma ContMDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, ContMDiffOn I I' n f (s i)) (hs : ∀ i, IsOpen (s i)) :
    ContMDiffOn I I' n f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).contMDiffAt ((hs i).mem_nhds hxsi) |>.contMDiffWithinAt

/-- A function is `C^k` on a union of open sets `s i` iff it is `C^k` on each `s i`. -/
/-
**contMDiffOn_iUnion_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set M} (hs : forall
 i, IsOpen (s i)) : ContMDiffOn I I' n f (⋃ i, s i) ↔ forall i : ι, ContMDiffOn 
I I' n f (s i)
参数：hs : forall i, IsOpen (s i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用引理 `ContMDiffOn.iUnion_of_isOpen`：ContMDiffOn.iUnion_of_isOpen {ι : Type*} {
s : ι -> Set M} (hf : forall i : ι, ContMDiffOn I I' n f (s i)) (hs : forall i, 
IsOpen (s i)) : Co…

--- 原说明 ---
A function is `C^k` on a union of open sets `s i` iff it is `C^k` on each `s i`.
-/
lemma contMDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set M}
    (hs : ∀ i, IsOpen (s i)) :
    ContMDiffOn I I' n f (⋃ i, s i) ↔ ∀ i : ι, ContMDiffOn I I' n f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ ContMDiffOn.iUnion_of_isOpen h hs⟩
/-
**contMDiff_of_contMDiffOn_iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_of_contMDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set M} (hf
 : forall i : ι, ContMDiffOn I I' n f (s i)) (hs : forall i, IsOpen (s i)) (hs' 
: ⋃ i, s i = univ) : ContMDiff I I' n f
参数：hf : forall i : ι, ContMDiffOn I I' n f (s i)；hs : forall i, IsOpen (s i)；hs'
 : ⋃ i, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用引理 `ContMDiffOn.iUnion_of_isOpen`：ContMDiffOn.iUnion_of_isOpen {ι : Type*} {
s : ι -> Set M} (hf : forall i : ι, ContMDiffOn I I' n f (s i)) (hs : forall i, 
IsOpen (s i)) : Co…
-/
lemma contMDiff_of_contMDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, ContMDiffOn I I' n f (s i)) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    ContMDiff I I' n f := by
  rw [← contMDiffOn_univ, ← hs']
  exact ContMDiffOn.iUnion_of_isOpen hf hs

end contMDiff_union


/-! ### The inclusion map from one open set to another is `C^n` -/

section Inclusion

open TopologicalSpace

/-
**contMDiffAt_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_subtype_iff {n : Nat∞ω} {U : Opens M} {f : M -> M'} {x : U} : 
ContMDiffAt I I' n (fun x : U => f x) x ↔ ContMDiffAt I I' n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_iff_comp_subtype_val`：li
ftPropAt_iff_comp_subtype_val (hG : LocalInvariantProp G G' P) {U : Opens M} (f 
: M -> M') (x : U) : LiftPropAt P f x ↔ LiftPropAt P (f ∘ …
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffAt_subtype_iff {n : ℕ∞ω} {U : Opens M} {f : M → M'} {x : U} :
    ContMDiffAt I I' n (fun x : U ↦ f x) x ↔ ContMDiffAt I I' n f x :=
  ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_subtype_val _ _).symm
/-
**contMDiff_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_subtype_val {n : Nat∞ω} {U : Opens M} : ContMDiff I I n (Subtype
.val : U -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffAt_subtype_iff`：contMDiffAt_subtype_iff {n : Nat∞ω} {U : Opens 
M} {f : M -> M'} {x : U} : ContMDiffAt I I' n (fun x : U => f x) x ↔ ContMDiffAt
 I I' n f x
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x
-/
theorem contMDiff_subtype_val {n : ℕ∞ω} {U : Opens M} :
    ContMDiff I I n (Subtype.val : U → M) :=
  fun _ ↦ contMDiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]
/-
**ContMDiff.extend_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.extend_one [T2Space M] [One M'] {n : Nat∞ω} {U : Opens M} {f : U
 -> M'} (supp : HasCompactMulSupport f) (diff : ContMDiff I I' n f) : ContMDiff 
I I' n (Subtype.val.extend f 1)
参数：supp : HasCompactMulSupport f；diff : ContMDiff I I' n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_of_mulTSupport`：contMDiff_of_mulTSupport [One M'] {f : M -> M'
} (hf : forall x in mulTSupport f, ContMDiffAt I I' n f x) : ContMDiff I I' n f
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
· 使用定理 `HasCompactMulSupport.mulTSupport_extend_one_subset`：mulTSupport_extend_o
ne_subset : mulTSupport (g.extend f 1) subseteq g '' mulTSupport f
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffAt_subtype_iff`：contMDiffAt_subtype_iff {n : Nat∞ω} {U : Opens 
M} {f : M -> M'} {x : U} : ContMDiffAt I I' n (fun x : U => f x) x ↔ ContMDiffAt
 I I' n f x
· 使用定理 `Function.extend_comp`：extend_comp (hf : Injective f) (g : α -> γ) (e' : 
β -> γ) : extend f g e' ∘ f = g
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
-/
theorem ContMDiff.extend_one [T2Space M] [One M'] {n : ℕ∞ω} {U : Opens M} {f : U → M'}
    (supp : HasCompactMulSupport f) (diff : ContMDiff I I' n f) :
    ContMDiff I I' n (Subtype.val.extend f 1) := fun x ↦ by
  refine contMDiff_of_mulTSupport (fun x h ↦ ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMDiffAt_subtype_iff]
  simp_rw [← comp_def]
  rw [extend_comp Subtype.val_injective]
  exact diff.contMDiffAt
/-
**contMDiff_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_inclusion {n : Nat∞ω} {U V : Opens M} (h : U <= V) : ContMDiff I
 I n (Opens.inclusion h : U -> V)
参数：h : U <= V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftProp_inclusion`：liftProp_inclus
ion {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvariantProp G G Q) (hQ : f
orall y, Q id univ y) {U V : Opens M} (hUV : …
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `contDiffWithinAtProp_id`：contDiffWithinAtProp_id (x : H) : ContDiffWithi
nAtProp I I n id univ x
-/
theorem contMDiff_inclusion {n : ℕ∞ω} {U V : Opens M} (h : U ≤ V) :
    ContMDiff I I n (Opens.inclusion h : U → V) := fun _ ↦
  (contDiffWithinAt_localInvariantProp n).liftProp_inclusion (contDiffWithinAtProp_id ·) _ _

end Inclusion

@[simp]
/-
**ContMDiffWithinAt.subtypeVal_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f :
 M -> U) (s : Set M) (x : M) : ContMDiffWithinAt I I' ∞ (Subtype.val ∘ f) s x ↔ 
ContMDiffWithinAt I I' ∞ f s x
参数：U : TopologicalSpace.Opens M'；f : M -> U；s : Set M；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff`：liftPropWithinAt_subt
ypeVal_comp_iff {P : (H -> H') -> Set H -> H -> Prop} {U : Opens M'} (f : M -> U
) (s : Set M) (x : M) : LiftPropWithinA…
-/
lemma ContMDiffWithinAt.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M → U) (s : Set M)
    (x : M) :
    ContMDiffWithinAt I I' ∞ (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I I' ∞ f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

@[simp]
/-
**ContMDiffAt.subtypeVal_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M -> 
U) (x : M) : ContMDiffAt I I' ∞ (Subtype.val ∘ f) x ↔ ContMDiffAt I I' ∞ f x
参数：U : TopologicalSpace.Opens M'；f : M -> U；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContMDiffAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用引理 `ContMDiffWithinAt.subtypeVal_comp_iff`：ContMDiffWithinAt.subtypeVal_comp
_iff (U : TopologicalSpace.Opens M') (f : M -> U) (s : Set M) (x : M) : ContMDif
fWithinAt I I' ∞ (Subtype.v…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ContMDiffAt.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M → U) (x : M) :
    ContMDiffAt I I' ∞ (Subtype.val ∘ f) x ↔ ContMDiffAt I I' ∞ f x := by
  rw [ContMDiffAt, ContMDiffAt, ContMDiffWithinAt.subtypeVal_comp_iff]

@[simp]
/-
**ContMDiff.subtypeVal_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M -> U)
 : ContMDiff I I' ∞ (Subtype.val ∘ f) ↔ ContMDiff I I' ∞ f
参数：U : TopologicalSpace.Opens M'；f : M -> U。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ContMDiff.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M → U) :
    ContMDiff I I' ∞ (Subtype.val ∘ f) ↔ ContMDiff I I' ∞ f := by
  simp_rw [ContMDiff, ContMDiffAt.subtypeVal_comp_iff]

end ChartedSpace

/-! ### Open embeddings and their inverses are `C^n` -/

section

variable {e : M → H} (h : IsOpenEmbedding e) {n : ℕ∞ω}

set_option backward.isDefEq.respectTransparency false in
/-- If the `ChartedSpace` structure on a manifold `M` is given by an open embedding `e : M → H`,
then `e` is `C^n`. -/
/-
**contMDiff_isOpenEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_isOpenEmbedding [Nonempty M] : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isManifold_singleton`：Topology.IsOpenEmbedding.
isManifold_singleton {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommG
roup E] [NormedSpace 𝕜 E] [Topologi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiff_iff`：contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] : C
ontMDiff I I' n f ↔ Continuous f ∧ forall (x : M) (y : M'), ContDiffOn 𝕜 n (extC
har…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用引理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv`：toOpenPartia
lHomeomorph_right_inv {x : Y} (hx : x in Set.range f) : f ((h.toOpenPartialHomeo
morph f).symm x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `extChartAt_target`：extChartAt_target (x : M) : (extChartAt I x).target =
 I.symm ⁻¹' (chartAt H x).target inter range I
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq`：singletonCharted
Space_chartAt_eq (h : e.source = Set.univ) {x : α} : @chartAt H _ α _ (e.singlet
onChartedSpace h) x = e
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I

--- 原说明 ---
If the `ChartedSpace` structure on a manifold `M` is given by an open embedding 
`e : M → H`,
then `e` is `C^n`.
-/
lemma contMDiff_isOpenEmbedding [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiff I I n e := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intro x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  intro z hz
  -- factorise into the chart `e` and the model `id`
  simp only [mfld_simps]
  rw [h.toOpenPartialHomeomorph_right_inv]
  · rw [I.right_inv]
    apply mem_of_subset_of_mem _ hz.1
    exact letI := h.singletonChartedSpace; extChartAt_target_subset_range (I := I) x
  · -- `hz` implies that `z ∈ range (I ∘ e)`
    have := hz.1
    rw [@extChartAt_target _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace] at this
    have := this.1
    rw [mem_preimage, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
      h.toOpenPartialHomeomorph_target] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
/-- If the `ChartedSpace` structure on a manifold `M` is given by an open embedding `e : M → H`,
then the inverse of `e` is `C^n`. -/
/-
**contMDiffOn_isOpenEmbedding_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_isOpenEmbedding_symm [Nonempty M] : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isManifold_singleton`：Topology.IsOpenEmbedding.
isManifold_singleton {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommG
roup E] [NormedSpace 𝕜 E] [Topologi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffOn_iff`：contMDiffOn_iff [IsManifold I n M] [IsManifold I' n M']
 : ContMDiffOn I I' n f s ↔ ContinuousOn f s ∧ forall (x : M) (y : M'), ContDiff
On 𝕜 …
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1}
 {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X
 → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `ModelWithCorners.symm.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv`：toOpenPartia
lHomeomorph_right_inv {x : Y} (hx : x in Set.range f) : f ((h.toOpenPartialHomeo
morph f).symm x) = x
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I

--- 原说明 ---
If the `ChartedSpace` structure on a manifold `M` is given by an open embedding 
`e : M → H`,
then the inverse of `e` is `C^n`.
-/
lemma contMDiffOn_isOpenEmbedding_symm [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiffOn I I
      n (IsOpenEmbedding.toOpenPartialHomeomorph e h).symm (range e) := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiffOn_iff]
  constructor
  · rw [← h.toOpenPartialHomeomorph_target]
    exact (h.toOpenPartialHomeomorph e).continuousOn_symm
  · intro z hz
    -- show the function is actually the identity on the range of I ∘ e
    apply contDiffOn_id.congr
    intro z hz
    -- factorise into the chart `e` and the model `id`
    simp only [mfld_simps]
    have : I.symm z ∈ range e := by
      rw [ModelWithCorners.symm, ← mem_preimage]
      exact hz.2.1
    rw [h.toOpenPartialHomeomorph_right_inv e this]
    apply I.right_inv
    exact mem_of_subset_of_mem (extChartAt_target_subset_range _) hz.1

variable [ChartedSpace H M]
variable [Nonempty M'] {e' : M' → H'} (h' : IsOpenEmbedding e')

/-- Let `M'` be a manifold whose chart structure is given by an open embedding `e'` into its model
space `H'`. If `e' ∘ f : M → H'` is `C^n`, then `f` is `C^n`.

This is useful, for example, when `e' ∘ f = g ∘ e` for smooth maps `e : M → X` and `g : X → H'`. -/
/-
**ContMDiff.of_comp_isOpenEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.of_comp_isOpenEmbedding {f : M -> M'} (hf : ContMDiff I I' n (e'
 ∘ f)) : haveI
参数：hf : ContMDiff I I' n (e' ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv`：toOpenPartial
Homeomorph_left_inv {x : X} : (h.toOpenPartialHomeomorph f).symm (f x) = x
· 使用定理 `ContMDiffOn.comp_contMDiff`：ContMDiffOn.comp_contMDiff {t : Set M'} {g :
 M' -> M''} (hg : ContMDiffOn I' I'' n g t) (hf : ContMDiff I I' n f) (ht : fora
ll x, f x in t) …
· 使用引理 `contMDiffOn_isOpenEmbedding_symm`：contMDiffOn_isOpenEmbedding_symm [None
mpty M] : haveI
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Let `M'` be a manifold whose chart structure is given by an open embedding `e'` 
into its model
space `H'`. If `e' ∘ f : M → H'` is `C^n`, then `f` is `C^n`.

This is useful, for example, when `e' ∘ f = g ∘ e` for smooth maps `e : M → X` a
nd `g : X → H'`.
-/
lemma ContMDiff.of_comp_isOpenEmbedding {f : M → M'} (hf : ContMDiff I I' n (e' ∘ f)) :
    haveI := h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toOpenPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply, Function.comp_apply, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h'.singletonChartedSpace _ _ (range e') _ (contMDiffOn_isOpenEmbedding_symm h') hf
  simp

end

