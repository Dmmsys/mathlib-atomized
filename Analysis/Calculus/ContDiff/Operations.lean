/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Higher differentiability of usual operations

We prove that the usual operations (addition, multiplication, difference, and
so on) preserve `C^n` functions.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

@[expose] public section

open scoped NNReal Nat ContDiff

universe u uE uF uG

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {b : E × F → G} {m n : ℕ∞ω} {p : E → FormalMultilinearSeries 𝕜 E F}

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/

section Pi

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {p' : ∀ i, E → FormalMultilinearSeries 𝕜 E (F' i)}
  {Φ : E → ∀ i, F' i} {P' : E → FormalMultilinearSeries 𝕜 E (∀ i, F' i)}

/-
**hasFTaylorSeriesUpToOn_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFTaylorSeriesUpToOn_pi {n : Nat∞ω} : HasFTaylorSeriesUpToOn n (fun x i 
=> φ i x) (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔ forall 
i, HasFTaylorSeriesUpToOn n (φ i) (p' i) s
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
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
· 使用定理 `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`：HasFTaylorSeriesUpToOn.
continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] G) (hf : HasFTaylorSeriesUpTo
On n f p s) : HasFTaylorSeriesUpToOn …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `LinearIsometryEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `continuousOn_pi`：continuousOn_pi {ι : Type*} {X : ι -> Type*} [forall i,
 TopologicalSpace (X i)] {f : α -> forall i, X i} {s : Set α} : ContinuousOn f s
 ↔ fo…
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
-/
theorem hasFTaylorSeriesUpToOn_pi {n : ℕ∞ω} :
    HasFTaylorSeriesUpToOn n (fun x i => φ i x)
        (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (φ i) (p' i) s := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  set L : ∀ m : ℕ, (∀ i, E [×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E [×m]→L[𝕜] ∀ i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · exact h.continuousLinearMap_comp (pr i)
  · ext1 i
    exact (h i).zero_eq x hx
  · intro m hm x hx
    exact (L m).hasFDerivAt.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.2 fun i => (h i).fderivWithin m hm x hx
  · intro m hm
    exact (L m).continuous.comp_continuousOn <| continuousOn_pi.2 fun i => (h i).cont m hm

@[simp]
/-
**hasFTaylorSeriesUpToOn_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFTaylorSeriesUpToOn_pi' {n : Nat∞ω} : HasFTaylorSeriesUpToOn n Φ P' s ↔
 forall i, HasFTaylorSeriesUpToOn n (fun x => Φ x i) (fun x m => (@ContinuousLin
earMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap (P' x m)) s
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
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `hasFTaylorSeriesUpToOn_pi`：hasFTaylorSeriesUpToOn_pi {n : Nat∞ω} : HasFT
aylorSeriesUpToOn n (fun x i => φ i x) (fun x m => ContinuousMultilinearMap.pi f
un i => p' i x …
-/
theorem hasFTaylorSeriesUpToOn_pi' {n : ℕ∞ω} :
    HasFTaylorSeriesUpToOn n Φ P' s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (fun x => Φ x i)
        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap
          (P' x m)) s := by
  convert! hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x ↦ Φ x i); ext; rfl
/-
**contDiffWithinAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_pi : ContDiffWithinAt 𝕜 n Φ s x ↔ forall i, ContDiffWithi
nAt 𝕜 n (fun x => Φ x i) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousLinearMap_comp`：ContDiffWithinAt.continuousLi
nearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithin
At 𝕜 n (g ∘ f) s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `hasFTaylorSeriesUpToOn_pi`：hasFTaylorSeriesUpToOn_pi {n : Nat∞ω} : HasFT
aylorSeriesUpToOn n (fun x i => φ i x) (fun x m => ContinuousMultilinearMap.pi f
un i => p' i x …
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
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
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `LinearIsometryEquiv.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOn.pi`：AnalyticOn.pi (hf : forall i, AnalyticOn 𝕜 (f i) s) : Ana
lyticOn 𝕜 (fun x => (f · x)) s
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem contDiffWithinAt_pi :
    ContDiffWithinAt 𝕜 n Φ s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h ↦ ?_⟩
  match n with
  | ω =>
    choose u hux p hp h'p using h
    refine ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
      hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _, fun m ↦ ?_⟩
    set L : (∀ i, E [×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E [×m]→L[𝕜] ∀ i, F' i :=
      ContinuousMultilinearMap.piₗᵢ _ _
    change AnalyticOn 𝕜 (fun x ↦ L (fun i ↦ p i x m)) (⋂ i, u i)
    apply (L.analyticOnNhd univ).comp_analyticOn ?_ (mapsTo_univ _ _)
    exact AnalyticOn.pi (fun i ↦ (h'p i m).mono (iInter_subset _ _))
  | (n : ℕ∞) =>
    intro m hm
    choose u hux p hp using fun i => h i m hm
    exact ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
      hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _⟩
/-
**contDiffOn_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ forall i, ContDiffOn 𝕜 n (fun x => Φ 
x i) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_pi`：contDiffWithinAt_pi : ContDiffWithinAt 𝕜 n Φ s x ↔ 
forall i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩
/-
**contDiffAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ forall i, ContDiffAt 𝕜 n (fun x => Φ 
x i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_pi`：contDiffWithinAt_pi : ContDiffWithinAt 𝕜 n Φ s x ↔ 
forall i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x
-/
theorem contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x :=
  contDiffWithinAt_pi
/-
**contDiff_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x => Φ x i
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
theorem contDiff_pi : ContDiff 𝕜 n Φ ↔ ∀ i, ContDiff 𝕜 n fun x => Φ x i := by
  simp only [← contDiffOn_univ, contDiffOn_pi]

@[fun_prop]
/-
**contDiff_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_pi' (hΦ : forall i, ContDiff 𝕜 n fun x => Φ x i) : ContDiff 𝕜 n Φ
参数：hΦ : forall i, ContDiff 𝕜 n fun x => Φ x i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_pi`：contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x
 => Φ x i
-/
theorem contDiff_pi' (hΦ : ∀ i, ContDiff 𝕜 n fun x => Φ x i) : ContDiff 𝕜 n Φ :=
  contDiff_pi.2 hΦ

@[fun_prop]
/-
**contDiffOn_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_pi' (hΦ : forall i, ContDiffOn 𝕜 n (fun x => Φ x i) s) : ContDi
ffOn 𝕜 n Φ s
参数：hΦ : forall i, ContDiffOn 𝕜 n (fun x => Φ x i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_pi`：contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ forall i, ContDiffOn
 𝕜 n (fun x => Φ x i) s
-/
theorem contDiffOn_pi' (hΦ : ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s) : ContDiffOn 𝕜 n Φ s :=
  contDiffOn_pi.2 hΦ

@[fun_prop]
/-
**contDiffAt_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_pi' (hΦ : forall i, ContDiffAt 𝕜 n (fun x => Φ x i) x) : ContDi
ffAt 𝕜 n Φ x
参数：hΦ : forall i, ContDiffAt 𝕜 n (fun x => Φ x i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffAt_pi`：contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ forall i, ContDiffAt
 𝕜 n (fun x => Φ x i) x
-/
theorem contDiffAt_pi' (hΦ : ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x) : ContDiffAt 𝕜 n Φ x :=
  contDiffAt_pi.2 hΦ
/-
**contDiff_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_update [DecidableEq ι] (k : Nat∞ω) (x : forall i, F' i) (i : ι) :
 ContDiff 𝕜 k (update x i)
参数：k : Nat∞ω；x : forall i, F' i；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_pi`：contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x
 => Φ x i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiff_update [DecidableEq ι] (k : ℕ∞ω) (x : ∀ i, F' i) (i : ι) :
    ContDiff 𝕜 k (update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

variable (F') in
/-
**contDiff_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_single [DecidableEq ι] (k : Nat∞ω) (i : ι) : ContDiff 𝕜 k (Pi.sin
gle i : F' i -> forall i, F' i)
参数：k : Nat∞ω；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiff_update`：contDiff_update [DecidableEq ι] (k : Nat∞ω) (x : forall
 i, F' i) (i : ι) : ContDiff 𝕜 k (update x i)
-/
theorem contDiff_single [DecidableEq ι] (k : ℕ∞ω) (i : ι) :
    ContDiff 𝕜 k (Pi.single i : F' i → ∀ i, F' i) :=
  contDiff_update k 0 i

variable (𝕜 E)

@[fun_prop]
/-
**contDiff_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι -> E => f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_pi`：contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x
 => Φ x i
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι → E => f i :=
  contDiff_pi.mp contDiff_id i

@[fun_prop]
/-
**contDiffAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_apply (i : ι) (f : ι -> E) : ContDiffAt 𝕜 n (fun f : ι -> E => 
f i) f
参数：i : ι；f : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_apply`：contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι -> E => 
f i
-/
theorem contDiffAt_apply (i : ι) (f : ι → E) : ContDiffAt 𝕜 n (fun f : ι → E => f i) f :=
  (contDiff_apply 𝕜 E i).contDiffAt

@[fun_prop]
/-
**contDiffOn_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_apply (i : ι) (s : Set (ι -> E)) : ContDiffOn 𝕜 n (fun f : ι ->
 E => f i) s
参数：i : ι；s : Set (ι -> E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_apply`：contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι -> E => 
f i
-/
theorem contDiffOn_apply (i : ι) (s : Set (ι → E)) : ContDiffOn 𝕜 n (fun f : ι → E => f i) s :=
  (contDiff_apply 𝕜 E i).contDiffOn
/-
**contDiff_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι -> ι' -> E 
=> f i j
参数：i : ι；j : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_pi`：contDiff_pi : ContDiff 𝕜 n Φ ↔ forall i, ContDiff 𝕜 n fun x
 => Φ x i
· 使用定理 `contDiff_apply`：contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι -> E => 
f i
-/
theorem contDiff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι → ι' → E => f i j :=
  contDiff_pi.mp (contDiff_apply 𝕜 (ι' → E) i) j

end Pi

/-! ### Sum of two functions -/

section Add

/-
**HasFTaylorSeriesUpToOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.add {n : Nat∞ω} {q g} (hf : HasFTaylorSeriesUpToOn 
n f p s) (hg : HasFTaylorSeriesUpToOn n g q s) : HasFTaylorSeriesUpToOn n (f + g
) (p + q) s
参数：hf : HasFTaylorSeriesUpToOn n f p s；hg : HasFTaylorSeriesUpToOn n g q s。
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
· 使用定理 `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`：HasFTaylorSeriesUpToOn.
continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] G) (hf : HasFTaylorSeriesUpTo
On n f p s) : HasFTaylorSeriesUpToOn …
· 使用定理 `HasFTaylorSeriesUpToOn.prodMk`：HasFTaylorSeriesUpToOn.prodMk {n : Nat∞ω}
 (hf : HasFTaylorSeriesUpToOn n f p s) {g : E -> G} {q : E -> FormalMultilinearS
eries 𝕜 E G} (hg : …
-/
theorem HasFTaylorSeriesUpToOn.add {n : ℕ∞ω} {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
    (hg : HasFTaylorSeriesUpToOn n g q s) : HasFTaylorSeriesUpToOn n (f + g) (p + q) s := by
  exact HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prodMk hg)

-- The sum is smooth.
@[fun_prop]
/-
**contDiff_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.contDiff`：IsBoundedLinearMap.contDiff (hf : IsBounded
LinearMap 𝕜 f) : ContDiff 𝕜 n f
· 使用定理 `IsBoundedLinearMap.add`：add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBounde
dLinearMap 𝕜 g) : IsBoundedLinearMap 𝕜 fun e => f e + g e
· 使用定理 `IsBoundedLinearMap.fst`：fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1
· 使用定理 `IsBoundedLinearMap.snd`：snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2
-/
theorem contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2 :=
  (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
/-
**ContDiffWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n
 f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x +
 g x) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiff_add`：contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ

--- 原说明 ---
The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point.
-/
theorem ContDiffWithinAt.add {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x + g x) s x :=
  contDiff_add.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
/-
**ContDiffAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.add {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜
 n g x) : ContDiffAt 𝕜 n (fun x => f x + g x) x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…

--- 原说明 ---
The sum of two `C^n` functions at a point is `C^n` at this point.
-/
theorem ContDiffAt.add {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x + g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg

/-- The sum of two `C^n` functions is `C^n`. -/
@[fun_prop]
/-
**ContDiff.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : 
ContDiff 𝕜 n fun x => f x + g x
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_add`：contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)

--- 原说明 ---
The sum of two `C^n` functions is `C^n`.
-/
theorem ContDiff.add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x + g x :=
  contDiff_add.comp (hf.prodMk hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.add {s : Set E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s) (hg : 
ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…

--- 原说明 ---
The sum of two `C^n` functions on a domain is `C^n`.
-/
theorem ContDiffOn.add {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s := fun x hx =>
  (hf x hx).add (hg x hx)

variable {i : ℕ}

/--
The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
-/
/-
**iteratedFDerivWithin_add_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Nor
medAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   {x : E} {i : ℕ} {f g
 : E → F},   ContDiffWithinAt 𝕜 (↑i) f s x →     ContDiffWithinAt 𝕜 (↑i) g s x →
       UniqueDiffOn 𝕜 s →         x ∈ s → iteratedFDerivWithin 𝕜 i (f + g) s x =
 iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x
参数：↑i；↑i；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `ContDiffWithinAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.inter_eventuallyEq_left`：inter_eventuallyEq_left {s t : Set α} {l
 : Filter α} : (s inter t : Set α) =ᶠ[l] s ↔ forallᶠ x in l, x in s -> x in t
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_congr_set`：iteratedFDerivWithin_congr_set (h : s =ᶠ
[𝓝 x] t) (n : Nat) : iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f
 t x
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFTaylorSeriesUpToOn.add`：HasFTaylorSeriesUpToOn.add {n : Nat∞ω} {q g}
 (hf : HasFTaylorSeriesUpToOn n f p s) (hg : HasFTaylorSeriesUpToOn n g q s) : H
asFTaylorSeriesU…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The iterated derivative of the sum of two functions is the sum of the iterated d
erivatives.
-/
@[to_fun] theorem iteratedFDerivWithin_add_apply {f g : E → F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (f + g) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x := by
  have := (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨t, ht, hxt, h⟩ := mem_nhdsWithin.mp this
  have hft : ContDiffOn 𝕜 i f (s ∩ t) := fun a ha ↦ (h (by simp_all)).1.mono inter_subset_left
  have hgt : ContDiffOn 𝕜 i g (s ∩ t) := fun a ha ↦ (h (by simp_all)).2.mono inter_subset_left
  have hut : UniqueDiffOn 𝕜 (s ∩ t) := hu.inter ht
  have H : ↑(s ∩ t) =ᶠ[𝓝 x] s :=
    inter_eventuallyEq_left.mpr (eventually_of_mem (ht.mem_nhds hxt) (fun _ h _ ↦ h))
  rw [← iteratedFDerivWithin_congr_set H, ← iteratedFDerivWithin_congr_set H,
    ← iteratedFDerivWithin_congr_set H]
  exact .symm (((hft.ftaylorSeriesWithin hut).add
      (hgt.ftaylorSeriesWithin hut)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hut ⟨hx, hxt⟩)

@[deprecated (since := "2026-02-13")]
alias iteratedFDerivWithin_add_apply' := fun_iteratedFDerivWithin_add_apply
/-
**iteratedFDeriv_add_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Nor
medAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E} {i : ℕ}   {f g : E → F},  
 ContDiffAt 𝕜 (↑i) f x →     ContDiffAt 𝕜 (↑i) g x → iteratedFDeriv 𝕜 i (f + g) 
x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x
参数：↑i；↑i；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_add_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type uF}…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
@[to_fun] theorem iteratedFDeriv_add_apply {i : ℕ} {f g : E → F}
    (hf : ContDiffAt 𝕜 i f x) (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (f + g) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

@[deprecated (since := "2026-02-13")]
alias iteratedFDeriv_add_apply' := fun_iteratedFDeriv_add_apply
/-
**iteratedFDeriv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Nor
medAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {i : ℕ}   {f g : E → F},   ContDif
f 𝕜 (↑i) f → ContDiff 𝕜 (↑i) g → iteratedFDeriv 𝕜 i (f + g) = iteratedFDeriv 𝕜 i
 f + iteratedFDeriv 𝕜 i g
参数：↑i；↑i；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDeriv_add_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {F : Type uF}…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
@[to_fun] theorem iteratedFDeriv_add {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f)
    (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f + g) = iteratedFDeriv 𝕜 i f + iteratedFDeriv 𝕜 i g :=
  funext fun _ ↦ iteratedFDeriv_add_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

end Add

/-! ### Negative -/

section Neg

-- The negative is smooth.
@[fun_prop]
/-
**contDiff_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.contDiff`：IsBoundedLinearMap.contDiff (hf : IsBounded
LinearMap 𝕜 f) : ContDiff 𝕜 n f
· 使用定理 `IsBoundedLinearMap.neg`：neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLin
earMap 𝕜 fun e => -f e
· 使用定理 `IsBoundedLinearMap.id`：id : IsBoundedLinearMap 𝕜 fun x : E => x
-/
theorem contDiff_neg : ContDiff 𝕜 n fun p : F => -p :=
  IsBoundedLinearMap.id.neg.contDiff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
@[fun_prop]
/-
**ContDiffWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf : ContDiffWithinAt 𝕜 n f
 s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ

--- 原说明 ---
The negative of a `C^n` function within a domain at a point is `C^n` within this
 domain at
this point.
-/
theorem ContDiffWithinAt.neg {s : Set E} {f : E → F} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
@[fun_prop]
/-
**ContDiffAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.neg {f : E -> F} (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fu
n x => -f x) x
参数：hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.neg`：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x

--- 原说明 ---
The negative of a `C^n` function at a point is `C^n` at this point.
-/
theorem ContDiffAt.neg {f : E → F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => -f x) x := by rw [← contDiffWithinAt_univ] at *; exact hf.neg

/-- The negative of a `C^n` function is `C^n`. -/
@[fun_prop]
/-
**ContDiff.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.neg {f : E -> F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f
 x
参数：hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p

--- 原说明 ---
The negative of a `C^n` function is `C^n`.
-/
theorem ContDiff.neg {f : E → F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f x :=
  contDiff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.neg {s : Set E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s) : ContDi
ffOn 𝕜 n (fun x => -f x) s
参数：hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.neg`：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x

--- 原说明 ---
The negative of a `C^n` function on a domain is `C^n`.
-/
theorem ContDiffOn.neg {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => -f x) s := fun x hx => (hf x hx).neg

variable {i : ℕ}

-- TODO: define `Neg` instance on `ContinuousLinearEquiv`,
-- prove it from `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`
/-
**iteratedFDerivWithin_neg_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_neg_apply {f : E -> F} (hu : UniqueDiffOn 𝕜 s) (hx : 
x in s) : iteratedFDerivWithin 𝕜 i (-f) s x = -iteratedFDerivWithin 𝕜 i f s x
参数：hu : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousMultilinearMap.instIsNegApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iteratedFDerivWithin_succ_apply_left`：iteratedFDerivWithin_succ_apply_le
ft {n : Nat} (m : Fin (n + 1) -> E) : (iteratedFDerivWithin 𝕜 (n + 1) f s x : (F
in (n + 1) -> E) -> F) m =…
· 使用定理 `fderivWithin_congr'`：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s
) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
· 使用定理 `Pi.neg_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg (G
 i)] (f : (i : ι) → G i), -f = fun i => -f i
· 使用定理 `fderivWithin_neg`：fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : fd
erivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
-/
theorem iteratedFDerivWithin_neg_apply {f : E → F} (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (-f) s x = -iteratedFDerivWithin 𝕜 i f s x := by
  induction i generalizing x with ext h
  | zero => simp
  | succ i hi =>
    calc
      iteratedFDerivWithin 𝕜 (i + 1) (-f) s x h =
          fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (-f) s) s x (h 0) (Fin.tail h) :=
        iteratedFDerivWithin_succ_apply_left _
      _ = fderivWithin 𝕜 (-iteratedFDerivWithin 𝕜 i f s) s x (h 0) (Fin.tail h) := by
        rw [fderivWithin_congr' (@hi) hx, Pi.neg_def]
      _ = -(fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i f s) s) x (h 0) (Fin.tail h) := by
        rw [fderivWithin_neg (hu x hx), neg_apply, neg_apply]
      _ = -(iteratedFDerivWithin 𝕜 (i + 1) f s) x h := by
        rw [iteratedFDerivWithin_succ_apply_left]
/-
**iteratedFDeriv_neg_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_neg_apply {i : Nat} {f : E -> F} : iteratedFDeriv 𝕜 i (-f) 
x = -iteratedFDeriv 𝕜 i f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_neg_apply`：iteratedFDerivWithin_neg_apply {f : E ->
 F} (hu : UniqueDiffOn 𝕜 s) (hx : x in s) : iteratedFDerivWithin 𝕜 i (-f) s x = 
-iteratedFDerivWithi…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem iteratedFDeriv_neg_apply {i : ℕ} {f : E → F} :
    iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)
/-
**iteratedFDeriv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_neg {i : Nat} {f : E -> F} : iteratedFDeriv 𝕜 i (-f) = -ite
ratedFDeriv 𝕜 i f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDeriv_neg_apply`：iteratedFDeriv_neg_apply {i : Nat} {f : E -> F
} : iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x
-/
theorem iteratedFDeriv_neg {i : ℕ} {f : E → F} :
    iteratedFDeriv 𝕜 i (-f) = -iteratedFDeriv 𝕜 i f :=
  funext fun _ ↦ iteratedFDeriv_neg_apply

end Neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
/-
**ContDiffWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.sub {s : Set E} {f g : E -> F} (hf : ContDiffWithinAt 𝕜 n
 f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x -
 g x) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `ContDiffWithinAt.neg`：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x

--- 原说明 ---
The difference of two `C^n` functions within a set at a point is `C^n` within th
is set
at this point.
-/
theorem ContDiffWithinAt.sub {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x - g x) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
/-
**ContDiffAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜
 n g x) : ContDiffAt 𝕜 n (fun x => f x - g x) x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ContDiffAt.add`：ContDiffAt.add {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x + g x) x
· 使用定理 `ContDiffAt.neg`：ContDiffAt.neg {f : E -> F} (hf : ContDiffAt 𝕜 n f x) : 
ContDiffAt 𝕜 n (fun x => -f x) x

--- 原说明 ---
The difference of two `C^n` functions at a point is `C^n` at this point.
-/
theorem ContDiffAt.sub {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x - g x) x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.sub {s : Set E} {f g : E -> F} (hf : ContDiffOn 𝕜 n f s) (hg : 
ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ContDiffOn.add`：ContDiffOn.add {s : Set E} {f g : E -> F} (hf : ContDiff
On 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s
· 使用定理 `ContDiffOn.neg`：ContDiffOn.neg {s : Set E} {f : E -> F} (hf : ContDiffOn
 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => -f x) s

--- 原说明 ---
The difference of two `C^n` functions on a domain is `C^n`.
-/
theorem ContDiffOn.sub {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
@[fun_prop]
/-
**ContDiff.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : 
ContDiff 𝕜 n fun x => f x - g x
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.neg`：ContDiff.neg {f : E -> F} (hf : ContDiff 𝕜 n f) : ContDiff
 𝕜 n fun x => -f x

--- 原说明 ---
The difference of two `C^n` functions is `C^n`.
-/
theorem ContDiff.sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x - g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

variable {i : ℕ}

/--
The iterated derivative of the difference of two functions is the difference of the iterated
derivatives.
-/
/-
**iteratedFDerivWithin_sub_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Nor
medAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   {x : E} {i : ℕ} {f g
 : E → F},   ContDiffWithinAt 𝕜 (↑i) f s x →     ContDiffWithinAt 𝕜 (↑i) g s x →
       UniqueDiffOn 𝕜 s →         x ∈ s → iteratedFDerivWithin 𝕜 i (f - g) s x =
 iteratedFDerivWithin 𝕜 i f s x - iteratedFDerivWithin 𝕜 i g s x
参数：↑i；↑i；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `iteratedFDerivWithin_add_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type uF}…
· 使用定理 `ContDiffWithinAt.neg`：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x
· 使用定理 `iteratedFDerivWithin_neg_apply`：iteratedFDerivWithin_neg_apply {f : E ->
 F} (hu : UniqueDiffOn 𝕜 s) (hx : x in s) : iteratedFDerivWithin 𝕜 i (-f) s x = 
-iteratedFDerivWithi…

--- 原说明 ---
The iterated derivative of the difference of two functions is the difference of 
the iterated
derivatives.
-/
@[to_fun] theorem iteratedFDerivWithin_sub_apply {f g : E → F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (f - g) s x =
      iteratedFDerivWithin 𝕜 i f s x - iteratedFDerivWithin 𝕜 i g s x := by
  rw [sub_eq_add_neg, iteratedFDerivWithin_add_apply hf _ hu hx,
    iteratedFDerivWithin_neg_apply hu hx, sub_eq_add_neg]
  exact hg.neg

/--
The iterated derivative of the difference of two functions is the difference of the iterated
derivatives.
-/
/-
**iteratedFDeriv_sub_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Nor
medAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E} {i : ℕ}   {f g : E → F},  
 ContDiffAt 𝕜 (↑i) f x →     ContDiffAt 𝕜 (↑i) g x → iteratedFDeriv 𝕜 i (f - g) 
x = iteratedFDeriv 𝕜 i f x - iteratedFDeriv 𝕜 i g x
参数：↑i；↑i；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_sub_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type uF}…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The iterated derivative of the difference of two functions is the difference of 
the iterated
derivatives.
-/
@[to_fun] theorem iteratedFDeriv_sub_apply {i : ℕ} {f g : E → F}
    (hf : ContDiffAt 𝕜 i f x) (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (f - g) x = iteratedFDeriv 𝕜 i f x - iteratedFDeriv 𝕜 i g x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_sub_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

/--
The iterated derivative of the difference of two functions is the difference of the iterated
derivatives.
-/
/-
**iteratedFDeriv_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type uF} [inst_3 : Nor
medAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {i : ℕ}   {f g : E → F},   ContDif
f 𝕜 (↑i) f → ContDiff 𝕜 (↑i) g → iteratedFDeriv 𝕜 i (f - g) = iteratedFDeriv 𝕜 i
 f - iteratedFDeriv 𝕜 i g
参数：↑i；↑i；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDeriv_sub_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {F : Type uF}…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
The iterated derivative of the difference of two functions is the difference of 
the iterated
derivatives.
-/
@[to_fun] theorem iteratedFDeriv_sub {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f)
    (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f - g) = iteratedFDeriv 𝕜 i f - iteratedFDeriv 𝕜 i g :=
  funext fun _ ↦ iteratedFDeriv_sub_apply (ContDiff.contDiffAt hf) (ContDiff.contDiffAt hg)

/-! ### Sum of finitely many functions -/

@[fun_prop]
/-
**ContDiffWithinAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {t : Set
 E} {x : E} (h : forall i in s, ContDiffWithinAt 𝕜 n (fun x => f i x) t x) : Con
tDiffWithinAt 𝕜 n (fun x => ∑ i in s, f i x) t x
参数：h : forall i in s, ContDiffWithinAt 𝕜 n (fun x => f i x) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
### Sum of finitely many functions
-/
theorem ContDiffWithinAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E} {x : E}
    (h : ∀ i ∈ s, ContDiffWithinAt 𝕜 n (fun x => f i x) t x) :
    ContDiffWithinAt 𝕜 n (fun x => ∑ i ∈ s, f i x) t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contDiffWithinAt_const]
  | insert i s is IH =>
    simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add
      (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))

@[fun_prop]
/-
**ContDiffAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {x : E} (h : f
orall i in s, ContDiffAt 𝕜 n (fun x => f i x) x) : ContDiffAt 𝕜 n (fun x => ∑ i 
in s, f i x) x
参数：h : forall i in s, ContDiffAt 𝕜 n (fun x => f i x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.sum`：ContDiffWithinAt.sum {ι : Type*} {f : ι -> E -> F}
 {s : Finset ι} {t : Set E} {x : E} (h : forall i in s, ContDiffWithinAt 𝕜 n (fu
n x => f i…
-/
theorem ContDiffAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {x : E}
    (h : ∀ i ∈ s, ContDiffAt 𝕜 n (fun x => f i x) x) :
    ContDiffAt 𝕜 n (fun x => ∑ i ∈ s, f i x) x := by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h

@[fun_prop]
/-
**ContDiffOn.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} {t : Set E} (h
 : forall i in s, ContDiffOn 𝕜 n (fun x => f i x) t) : ContDiffOn 𝕜 n (fun x => 
∑ i in s, f i x) t
参数：h : forall i in s, ContDiffOn 𝕜 n (fun x => f i x) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.sum`：ContDiffWithinAt.sum {ι : Type*} {f : ι -> E -> F}
 {s : Finset ι} {t : Set E} {x : E} (h : forall i in s, ContDiffWithinAt 𝕜 n (fu
n x => f i…
-/
theorem ContDiffOn.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn 𝕜 n (fun x => f i x) t) :
    ContDiffOn 𝕜 n (fun x => ∑ i ∈ s, f i x) t := fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

@[fun_prop]
/-
**ContDiff.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.sum {ι : Type*} {f : ι -> E -> F} {s : Finset ι} (h : forall i in
 s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i in s, f i x
参数：h : forall i in s, ContDiff 𝕜 n fun x => f i x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.sum`：ContDiffOn.sum {ι : Type*} {f : ι -> E -> F} {s : Finset
 ι} {t : Set E} (h : forall i in s, ContDiffOn 𝕜 n (fun x => f i x) t) : ContDif
fOn …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem ContDiff.sum {ι : Type*} {f : ι → E → F} {s : Finset ι}
    (h : ∀ i ∈ s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i ∈ s, f i x := by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h
/-
**iteratedFDerivWithin_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι
} {i : Nat} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (h : forall j in u, Co
ntDiffWithinAt 𝕜 i (f j) s x) : iteratedFDerivWithin 𝕜 i (∑ j in u, f j) s x = ∑
 j in u, iteratedFDerivWithin 𝕜 i (f j) s x
参数：hs : UniqueDiffOn 𝕜 s；hx : x in s；h : forall j in u, ContDiffWithinAt 𝕜 i (f 
j) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_fun_zero`：iteratedFDerivWithin_fun_zero {i : Nat} :
 iteratedFDerivWithin 𝕜 i (fun (_ : E) => (0 : F)) s = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fun_iteratedFDerivWithin_add_apply`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type uF}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ContDiffWithinAt.sum`：ContDiffWithinAt.sum {ι : Type*} {f : ι -> E -> F}
 {s : Finset ι} {t : Set E} {x : E} (h : forall i in s, ContDiffWithinAt 𝕜 n (fu
n x => f i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem iteratedFDerivWithin_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : ∀ j ∈ u, ContDiffWithinAt 𝕜 i (f j) s x) :
    iteratedFDerivWithin 𝕜 i (∑ j ∈ u, f j) s x =
      ∑ j ∈ u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  rw [(by aesop : (∑ j ∈ u, f j) = (fun x ↦ ∑ j ∈ u, f j x))]
  induction u using Finset.cons_induction with
  | empty => simp
  | cons a u ha IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    simp only [Finset.sum_cons]
    rw [fun_iteratedFDerivWithin_add_apply h.1 (ContDiffWithinAt.sum h.2) hs hx, IH h.2]
/-
**iteratedFDerivWithin_fun_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_fun_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Fins
et ι} {i : Nat} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (h : forall j in u
, ContDiffWithinAt 𝕜 i (f j) s x) : iteratedFDerivWithin 𝕜 i (fun z => ∑ j in u,
 f j z) s x = ∑ j in u, iteratedFDerivWithin 𝕜 i (f j) s x
参数：hs : UniqueDiffOn 𝕜 s；hx : x in s；h : forall j in u, ContDiffWithinAt 𝕜 i (f 
j) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `iteratedFDerivWithin_sum_apply`：iteratedFDerivWithin_sum_apply {ι : Type
*} {f : ι -> E -> F} {u : Finset ι} {i : Nat} {x : E} (hs : UniqueDiffOn 𝕜 s) (h
x : x in s) (h : for…
-/
theorem iteratedFDerivWithin_fun_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ}
    {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : ∀ j ∈ u, ContDiffWithinAt 𝕜 i (f j) s x) :
    iteratedFDerivWithin 𝕜 i (fun z ↦ ∑ j ∈ u, f j z) s x =
      ∑ j ∈ u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  convert! iteratedFDerivWithin_sum_apply hs hx h
  rw [Finset.sum_apply]
/-
**iteratedFDeriv_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {n :
 Nat} {x : E} (h : forall j in u, ContDiffAt 𝕜 n (f j) x) : iteratedFDeriv 𝕜 n (
∑ j in u, f j) x = ∑ j in u, iteratedFDeriv 𝕜 n (f j) x
参数：h : forall j in u, ContDiffAt 𝕜 n (f j) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iteratedFDerivWithin_sum_apply`：iteratedFDerivWithin_sum_apply {ι : Type
*} {f : ι -> E -> F} {u : Finset ι} {i : Nat} {x : E} (hs : UniqueDiffOn 𝕜 s) (h
x : x in s) (h : for…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
-/
theorem iteratedFDeriv_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {n : ℕ} {x : E}
    (h : ∀ j ∈ u, ContDiffAt 𝕜 n (f j) x) :
    iteratedFDeriv 𝕜 n (∑ j ∈ u, f j) x = ∑ j ∈ u, iteratedFDeriv 𝕜 n (f j) x := by
  simp only [← iteratedFDerivWithin_univ]
  apply iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (Set.mem_univ x)
    (h · · |>.contDiffWithinAt)
/-
**iteratedFDeriv_fun_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_fun_sum_apply {ι : Type*} {f : ι -> E -> F} {u : Finset ι} 
{n : Nat} {x : E} (h : forall j in u, ContDiffAt 𝕜 n (f j) x) : iteratedFDeriv 𝕜
 n (fun z => ∑ j in u, f j z) x = ∑ j in u, iteratedFDeriv 𝕜 n (f j) x
参数：h : forall j in u, ContDiffAt 𝕜 n (f j) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `iteratedFDeriv_sum_apply`：iteratedFDeriv_sum_apply {ι : Type*} {f : ι ->
 E -> F} {u : Finset ι} {n : Nat} {x : E} (h : forall j in u, ContDiffAt 𝕜 n (f 
j) x) : iterat…
-/
theorem iteratedFDeriv_fun_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {n : ℕ} {x : E}
    (h : ∀ j ∈ u, ContDiffAt 𝕜 n (f j) x) :
    iteratedFDeriv 𝕜 n (fun z ↦ ∑ j ∈ u, f j z) x = ∑ j ∈ u, iteratedFDeriv 𝕜 n (f j) x := by
  convert! iteratedFDeriv_sum_apply h
  rw [Finset.sum_apply]
/-
**iteratedFDeriv_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_sum {ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat} 
(h : forall j in u, ContDiff 𝕜 i (f j)) : iteratedFDeriv 𝕜 i (∑ j in u, f j ·) =
 ∑ j in u, iteratedFDeriv 𝕜 i (f j)
参数：h : forall j in u, ContDiff 𝕜 i (f j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iteratedFDerivWithin_fun_sum_apply`：iteratedFDerivWithin_fun_sum_apply {
ι : Type*} {f : ι -> E -> F} {u : Finset ι} {i : Nat} {x : E} (hs : UniqueDiffOn
 𝕜 s) (hx : x in s) (h :…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
-/
theorem iteratedFDeriv_sum {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ}
    (h : ∀ j ∈ u, ContDiff 𝕜 i (f j)) :
    iteratedFDeriv 𝕜 i (∑ j ∈ u, f j ·) = ∑ j ∈ u, iteratedFDeriv 𝕜 i (f j) :=
  funext fun x ↦ by simpa [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) (h · · |>.contDiffWithinAt)

/-! ### Product of two functions -/

section MulProd

variable {𝔸 𝔸' ι 𝕜' : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [NormedCommRing 𝔸']
  [NormedAlgebra 𝕜 𝔸'] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

-- The product is smooth.
@[fun_prop]
/-
**contDiff_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
-/
theorem contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2 :=
  (ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.contDiff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
/-
**ContDiffWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n
 f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x *
 g x) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffWithinAt`：ContDiff.comp_contDiffWithinAt {g : F ->
 G} {f : E -> F} (h : ContDiff 𝕜 n g) (hf : ContDiffWithinAt 𝕜 n f t x) : ContDi
ffWithinAt 𝕜 n (g ∘ …
· 使用定理 `contDiff_mul`：contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…

--- 原说明 ---
The product of two `C^n` functions within a set at a point is `C^n` within this 
set
at this point.
-/
theorem ContDiffWithinAt.mul {s : Set E} {f g : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x * g x) s x :=
  contDiff_mul.comp_contDiffWithinAt (hf.prodMk hg)

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
nonrec theorem ContDiffAt.mul {f g : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x * g x) x :=
  hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.mul {f g : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜
 n g s) : ContDiffOn 𝕜 n (fun x => f x * g x) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mul`：ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…

--- 原说明 ---
The product of two `C^n` functions on a domain is `C^n`.
-/
theorem ContDiffOn.mul {f g : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x * g x) s := fun x hx => (hf x hx).mul (hg x hx)

/-- The product of two `C^n` functions is `C^n`. -/
@[fun_prop]
/-
**ContDiff.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : 
ContDiff 𝕜 n fun x => f x * g x
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_mul`：contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)

--- 原说明 ---
The product of two `C^n` functions is `C^n`.
-/
theorem ContDiff.mul {f g : E → 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x * g x :=
  contDiff_mul.comp (hf.prodMk hg)

@[fun_prop]
/-
**contDiffWithinAt_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in 
t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (∏ i in t, f i) s x
参数：h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `ContDiffWithinAt.mul`：ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
-/
theorem contDiffWithinAt_prod' {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (∏ i ∈ t, f i) s x :=
  Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h

@[fun_prop]
/-
**contDiffWithinAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t
, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (fun y => ∏ i in t, f i
 y) s x
参数：h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `contDiffWithinAt_prod'`：contDiffWithinAt_prod' {t : Finset ι} {f : ι -> 
E -> 𝔸'} (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 
𝕜 n (∏ i in …
-/
theorem contDiffWithinAt_prod {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) :
    ContDiffWithinAt 𝕜 n (fun y => ∏ i ∈ t, f i y) s x := by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h

@[fun_prop]
/-
**contDiffAt_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, Con
tDiffAt 𝕜 n (f i) x) : ContDiffAt 𝕜 n (∏ i in t, f i) x
参数：h : forall i in t, ContDiffAt 𝕜 n (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_prod'`：contDiffWithinAt_prod' {t : Finset ι} {f : ι -> 
E -> 𝔸'} (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 
𝕜 n (∏ i in …
-/
theorem contDiffAt_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (∏ i ∈ t, f i) x :=
  contDiffWithinAt_prod' h

@[fun_prop]
/-
**contDiffAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, Cont
DiffAt 𝕜 n (f i) x) : ContDiffAt 𝕜 n (fun y => ∏ i in t, f i y) x
参数：h : forall i in t, ContDiffAt 𝕜 n (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_prod`：contDiffWithinAt_prod {t : Finset ι} {f : ι -> E 
-> 𝔸'} (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 
n (fun y =>…
-/
theorem contDiffAt_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (fun y => ∏ i ∈ t, f i y) x :=
  contDiffWithinAt_prod h

@[fun_prop]
/-
**contDiffOn_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, Con
tDiffOn 𝕜 n (f i) s) : ContDiffOn 𝕜 n (∏ i in t, f i) s
参数：h : forall i in t, ContDiffOn 𝕜 n (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_prod'`：contDiffWithinAt_prod' {t : Finset ι} {f : ι -> 
E -> 𝔸'} (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 
𝕜 n (∏ i in …
-/
theorem contDiffOn_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (∏ i ∈ t, f i) s := fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx

@[fun_prop]
/-
**contDiffOn_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, Cont
DiffOn 𝕜 n (f i) s) : ContDiffOn 𝕜 n (fun y => ∏ i in t, f i y) s
参数：h : forall i in t, ContDiffOn 𝕜 n (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_prod`：contDiffWithinAt_prod {t : Finset ι} {f : ι -> E 
-> 𝔸'} (h : forall i in t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 
n (fun y =>…
-/
theorem contDiffOn_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (fun y => ∏ i ∈ t, f i y) s := fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx

@[fun_prop]
/-
**contDiff_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContD
iff 𝕜 n (f i)) : ContDiff 𝕜 n (∏ i in t, f i)
参数：h : forall i in t, ContDiff 𝕜 n (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `contDiffAt_prod'`：contDiffAt_prod' {t : Finset ι} {f : ι -> E -> 𝔸'} (h 
: forall i in t, ContDiffAt 𝕜 n (f i) x) : ContDiffAt 𝕜 n (∏ i in t, f i) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem contDiff_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n (∏ i ∈ t, f i) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt

@[fun_prop]
/-
**contDiff_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : forall i in t, ContDi
ff 𝕜 n (f i)) : ContDiff 𝕜 n fun y => ∏ i in t, f i y
参数：h : forall i in t, ContDiff 𝕜 n (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `contDiffAt_prod`：contDiffAt_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : 
forall i in t, ContDiffAt 𝕜 n (f i) x) : ContDiffAt 𝕜 n (fun y => ∏ i in t, f i 
y) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem contDiff_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n fun y => ∏ i ∈ t, f i y :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt

@[fun_prop]
/-
**ContDiff.pow** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type uE} [inst_1 
: NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {n : WithTop ℕ∞} {𝔸 : Type 
u_3} [inst_3 : NormedRing 𝔸] [inst_4 : NormedAlgebra 𝕜 𝔸]   {f : E → 𝔸}, ContDif
f 𝕜 n f → ∀ (m : ℕ), ContDiff 𝕜 n fun x => f x ^ m
参数：m : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContDiff.pow {f : E → 𝔸} (hf : ContDiff 𝕜 n f) : ∀ m : ℕ, ContDiff 𝕜 n fun x => f x ^ m
  | 0 => by simpa using contDiff_const
  | m + 1 => by simpa [pow_succ] using (hf.pow m).mul hf

@[fun_prop]
/-
**ContDiffWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.pow {f : E -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : N
at) : ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffWithinAt`：ContDiff.comp_contDiffWithinAt {g : F ->
 G} {f : E -> F} (h : ContDiff 𝕜 n g) (hf : ContDiffWithinAt 𝕜 n f t x) : ContDi
ffWithinAt 𝕜 n (g ∘ …
· 使用定理 `ContDiff.pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : T
ype uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {n : WithTo
p …
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem ContDiffWithinAt.pow {f : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
    ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x :=
  (contDiff_id.pow m).comp_contDiffWithinAt hf

@[fun_prop]
nonrec theorem ContDiffAt.pow {f : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : ℕ) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m

@[fun_prop]
/-
**ContDiffOn.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.pow {f : E -> 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : Nat) : ContDiff
On 𝕜 n (fun y => f y ^ m) s
参数：hf : ContDiffOn 𝕜 n f s；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.pow`：ContDiffWithinAt.pow {f : E -> 𝔸} (hf : ContDiffWi
thinAt 𝕜 n f s x) (m : Nat) : ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x
-/
theorem ContDiffOn.pow {f : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : ℕ) :
    ContDiffOn 𝕜 n (fun y => f y ^ m) s := fun y hy => (hf y hy).pow m

@[fun_prop]
/-
**ContDiffWithinAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.div_const {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f 
s x) (c : 𝕜') : ContDiffWithinAt 𝕜 n (fun x => f x / c) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；c : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ContDiffWithinAt.mul`：ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
-/
theorem ContDiffWithinAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') :
    ContDiffWithinAt 𝕜 n (fun x => f x / c) s x := by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const

@[fun_prop]
nonrec theorem ContDiffAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c

@[fun_prop]
/-
**ContDiffOn.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.div_const {f : E -> 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') 
: ContDiffOn 𝕜 n (fun x => f x / c) s
参数：hf : ContDiffOn 𝕜 n f s；c : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.div_const`：ContDiffWithinAt.div_const {f : E -> 𝕜'} {n}
 (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') : ContDiffWithinAt 𝕜 n (fun x => f x
 / c) s x
-/
theorem ContDiffOn.div_const {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') :
    ContDiffOn 𝕜 n (fun x => f x / c) s := fun x hx => (hf x hx).div_const c

@[fun_prop]
/-
**ContDiff.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') : Cont
Diff 𝕜 n fun x => f x / c
参数：hf : ContDiff 𝕜 n f；c : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem ContDiff.div_const {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') :
    ContDiff 𝕜 n fun x => f x / c := by simpa only [div_eq_mul_inv] using hf.mul contDiff_const


end MulProd

/-! ### Scalar multiplication -/

section SMul

variable {𝕜' : Type*} [NormedRing 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

-- The scalar multiplication is smooth.
@[fun_prop]
/-
**contDiff_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_smul : ContDiff 𝕜 n fun p : 𝕜' × F => p.1 • p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.contDiff`：IsBoundedBilinearMap.contDiff (hb : IsBou
ndedBilinearMap 𝕜 b) : ContDiff 𝕜 n b
· 使用定理 `isBoundedBilinearMap_smul`：isBoundedBilinearMap_smul {E : Type*} [Semino
rmedAddCommGroup E] [Module 𝕜 E] [Module A E] [IsBoundedSMul A E] [IsScalarTower
 𝕜 A E] : IsBou…
-/
theorem contDiff_smul : ContDiff 𝕜 n fun p : 𝕜' × F => p.1 • p.2 :=
  isBoundedBilinearMap_smul.contDiff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
@[to_fun (attr := fun_prop)]
/-
**ContDiffWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.smul {s : Set E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDif
fWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (f
 • g) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiff_smul`：contDiff_smul : ContDiff 𝕜 n fun p : 𝕜' × F => p.1 • p.2
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ

--- 原说明 ---
The scalar multiplication of two `C^n` functions within a set at a point is `C^n
` within this
set at this point.
-/
theorem ContDiffWithinAt.smul {s : Set E} {f : E → 𝕜'} {g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (f • g) s x :=
  contDiff_smul.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
@[to_fun (attr := fun_prop)]
/-
**ContDiffAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffAt 𝕜 n f x) (hg :
 ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (f • g) x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.smul`：ContDiffWithinAt.smul {s : Set E} {f : E -> 𝕜'} {
g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) 
: ContDiffW…

--- 原说明 ---
The scalar multiplication of two `C^n` functions at a point is `C^n` at this poi
nt.
-/
theorem ContDiffAt.smul {f : E → 𝕜'} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (f • g) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
@[to_fun (attr := fun_prop)]
/-
**ContDiff.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDiff 𝕜 n f) (hg : ContD
iff 𝕜 n g) : ContDiff 𝕜 n (f • g)
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_smul`：contDiff_smul : ContDiff 𝕜 n fun p : 𝕜' × F => p.1 • p.2
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)

--- 原说明 ---
The scalar multiplication of two `C^n` functions is `C^n`.
-/
theorem ContDiff.smul {f : E → 𝕜'} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (f • g) :=
  contDiff_smul.comp (hf.prodMk hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
@[to_fun (attr := fun_prop)]
/-
**ContDiffOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.smul {s : Set E} {f : E -> 𝕜'} {g : E -> F} (hf : ContDiffOn 𝕜 
n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (f • g) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.smul`：ContDiffWithinAt.smul {s : Set E} {f : E -> 𝕜'} {
g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) 
: ContDiffW…

--- 原说明 ---
The scalar multiplication of two `C^n` functions on a domain is `C^n`.
-/
theorem ContDiffOn.smul {s : Set E} {f : E → 𝕜'} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (f • g) s := fun x hx =>
  (hf x hx).smul (hg x hx)

end SMul

/-! ### Constant scalar multiplication

TODO: generalize results in this section -- if `c` is a unit (or `R` is a group), then one can
drop `ContDiff*` assumptions in some lemmas about `iteratedFDeriv` and `iteratedFDerivWithin`.
-/

section ConstSMul

variable {R A : Type*} [DistribSMul R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  [NormedRing A] [NormedAlgebra 𝕜 A] [Module A F] [IsScalarTower 𝕜 A F] [IsBoundedSMul A F]

/-- Scalar multiplication is smooth (as a function of the vector variable). -/
@[fun_prop]
/-
**contDiff_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : F => c • p
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f

--- 原说明 ---
Scalar multiplication is smooth (as a function of the vector variable).
-/
theorem contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : F => c • p :=
  (c • ContinuousLinearMap.id 𝕜 F).contDiff

/-- Scalar multiplication is smooth (as a function of the scalar variable). -/
@[fun_prop]
/-
**contDiff_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_smul_const (v : F) : ContDiff 𝕜 n fun a : A => a • v
参数：v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
Scalar multiplication is smooth (as a function of the scalar variable).
-/
theorem contDiff_smul_const (v : F) : ContDiff 𝕜 n fun a : A => a • v :=
  ((ContinuousLinearMap.id 𝕜 A).smulRight v).contDiff

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
@[fun_prop]
/-
**ContDiffWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.const_smul {s : Set E} {f : E -> F} {x : E} (c : R) (hf :
 ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun y => c • f y) s x
参数：c : R；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_const_smul`：contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : 
F => c • p

--- 原说明 ---
The scalar multiplication of a constant and a `C^n` function within a set at a p
oint is `C^n`
within this set at this point.
-/
theorem ContDiffWithinAt.const_smul {s : Set E} {f : E → F} {x : E} (c : R)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun y => c • f y) s x :=
  (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf

/-- The scalar multiplication of `C^n` function within a set at a point and a constant and is `C^n`
within this set at this point. -/
@[fun_prop]
/-
**ContDiffWithinAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.smul_const {s : Set E} {f : E -> A} {x : E} (hf : ContDif
fWithinAt 𝕜 n f s x) (v : F) : ContDiffWithinAt 𝕜 n (fun y => f y • v) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；v : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_smul_const`：contDiff_smul_const (v : F) : ContDiff 𝕜 n fun a : 
A => a • v

--- 原说明 ---
The scalar multiplication of `C^n` function within a set at a point and a consta
nt and is `C^n`
within this set at this point.
-/
theorem ContDiffWithinAt.smul_const {s : Set E} {f : E → A} {x : E}
    (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) : ContDiffWithinAt 𝕜 n (fun y => f y • v) s x :=
  (contDiff_smul_const v).contDiffAt.comp_contDiffWithinAt x hf

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
@[fun_prop]
/-
**ContDiffAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.const_smul {f : E -> F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f 
x) : ContDiffAt 𝕜 n (fun y => c • f y) x
参数：c : R；hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.const_smul`：ContDiffWithinAt.const_smul {s : Set E} {f 
: E -> F} {x : E} (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜
 n (fun y => c • …

--- 原说明 ---
The scalar multiplication of a constant and a `C^n` function at a point is `C^n`
 at this
point.
-/
theorem ContDiffAt.const_smul {f : E → F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun y => c • f y) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c

/-- The scalar multiplication of a `C^n` function at a point and a constant is `C^n` at this
point. -/
@[fun_prop]
/-
**ContDiffAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.smul_const {f : E -> A} {x : E} (hf : ContDiffAt 𝕜 n f x) (v : 
F) : ContDiffAt 𝕜 n (fun y => f y • v) x
参数：hf : ContDiffAt 𝕜 n f x；v : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.smul_const`：ContDiffWithinAt.smul_const {s : Set E} {f 
: E -> A} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) : ContDiffWithinAt 𝕜
 n (fun y => f y …

--- 原说明 ---
The scalar multiplication of a `C^n` function at a point and a constant is `C^n`
 at this
point.
-/
theorem ContDiffAt.smul_const {f : E → A} {x : E} (hf : ContDiffAt 𝕜 n f x) (v : F) :
    ContDiffAt 𝕜 n (fun y => f y • v) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul_const v

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
@[fun_prop]
/-
**ContDiff.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.const_smul {f : E -> F} (c : R) (hf : ContDiff 𝕜 n f) : ContDiff 
𝕜 n fun y => c • f y
参数：c : R；hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_const_smul`：contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : 
F => c • p

--- 原说明 ---
The scalar multiplication of a constant and a `C^n` function is `C^n`.
-/
theorem ContDiff.const_smul {f : E → F} (c : R) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun y => c • f y :=
  (contDiff_const_smul c).comp hf

/-- The scalar multiplication of a `C^n` function and a constant is `C^n`. -/
@[fun_prop]
/-
**ContDiff.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.smul_const {f : E -> A} (hf : ContDiff 𝕜 n f) (v : F) : ContDiff 
𝕜 n fun y => f y • v
参数：hf : ContDiff 𝕜 n f；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_smul_const`：contDiff_smul_const (v : F) : ContDiff 𝕜 n fun a : 
A => a • v

--- 原说明 ---
The scalar multiplication of a `C^n` function and a constant is `C^n`.
-/
theorem ContDiff.smul_const {f : E → A} (hf : ContDiff 𝕜 n f) (v : F) :
    ContDiff 𝕜 n fun y => f y • v :=
  (contDiff_smul_const v).comp hf

/-- The scalar multiplication of a constant and a `C^n` function on a domain is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.const_smul {s : Set E} {f : E -> F} (c : R) (hf : ContDiffOn 𝕜 
n f s) : ContDiffOn 𝕜 n (fun y => c • f y) s
参数：c : R；hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.const_smul`：ContDiffWithinAt.const_smul {s : Set E} {f 
: E -> F} {x : E} (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜
 n (fun y => c • …

--- 原说明 ---
The scalar multiplication of a constant and a `C^n` function on a domain is `C^n
`.
-/
theorem ContDiffOn.const_smul {s : Set E} {f : E → F} (c : R) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun y => c • f y) s := fun x hx => (hf x hx).const_smul c

/-- The scalar multiplication of a `C^n` function on a domain and a constant is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.smul_const {s : Set E} {f : E -> A} (hf : ContDiffOn 𝕜 n f s) (
v : F) : ContDiffOn 𝕜 n (fun y => f y • v) s
参数：hf : ContDiffOn 𝕜 n f s；v : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.smul_const`：ContDiffWithinAt.smul_const {s : Set E} {f 
: E -> A} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) : ContDiffWithinAt 𝕜
 n (fun y => f y …

--- 原说明 ---
The scalar multiplication of a `C^n` function on a domain and a constant is `C^n
`.
-/
theorem ContDiffOn.smul_const {s : Set E} {f : E → A} (hf : ContDiffOn 𝕜 n f s) (v : F) :
    ContDiffOn 𝕜 n (fun y => f y • v) s := fun x hx => (hf x hx).smul_const v

variable {i : ℕ} {a : R} {v : F}
/-
**iteratedFDerivWithin_const_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_const_smul_apply (hf : ContDiffWithinAt 𝕜 i f s x) (h
u : UniqueDiffOn 𝕜 s) (hx : x in s) : iteratedFDerivWithin 𝕜 i (a • f) s x = a •
 iteratedFDerivWithin 𝕜 i f s x
参数：hf : ContDiffWithinAt 𝕜 i f s x；hu : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`：ContinuousLinearMap.
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffWithi
nAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iteratedFDerivWithin_const_smul_apply (hf : ContDiffWithinAt 𝕜 i f s x)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (a • f) s x = a • iteratedFDerivWithin 𝕜 i f s x :=
  (a • (1 : F →L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl
/-
**iteratedFDerivWithin_smul_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_smul_const_apply {f : E -> A} (hf : ContDiffWithinAt 
𝕜 i f s x) (hu : UniqueDiffOn 𝕜 s) (hx : x in s) : iteratedFDerivWithin 𝕜 i (fun
 y => f y • v) s x = ((ContinuousLinearMap.id 𝕜 A).smulRight v).compContinuousMu
ltilinearMap (iteratedFDerivWithin 𝕜 i f s x)
参数：hf : ContDiffWithinAt 𝕜 i f s x；hu : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`：ContinuousLinearMap.
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffWithi
nAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iteratedFDerivWithin_smul_const_apply {f : E → A} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (fun y ↦ f y • v) s x =
      ((ContinuousLinearMap.id 𝕜 A).smulRight v).compContinuousMultilinearMap
        (iteratedFDerivWithin 𝕜 i f s x) :=
  (ContinuousLinearMap.id 𝕜 A).smulRight v |>.iteratedFDerivWithin_comp_left hf hu hx le_rfl
/-
**iteratedFDeriv_const_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_const_smul_apply (hf : ContDiffAt 𝕜 i f x) : iteratedFDeriv
 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x
参数：hf : ContDiffAt 𝕜 i f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.iteratedFDeriv_comp_left`：ContinuousLinearMap.iterat
edFDeriv_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) {i : 
Nat} (hi : i <= n) : iteratedFDeri…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iteratedFDeriv_const_smul_apply (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x :=
  (a • (1 : F →L[𝕜] F)).iteratedFDeriv_comp_left hf le_rfl
/-
**iteratedFDeriv_const_smul_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_const_smul_apply' (hf : ContDiffAt 𝕜 i f x) : iteratedFDeri
v 𝕜 i (fun x => a • f x) x = a • iteratedFDeriv 𝕜 i f x
参数：hf : ContDiffAt 𝕜 i f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedFDeriv_const_smul_apply`：iteratedFDeriv_const_smul_apply (hf : C
ontDiffAt 𝕜 i f x) : iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x
-/
theorem iteratedFDeriv_const_smul_apply' (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (fun x ↦ a • f x) x = a • iteratedFDeriv 𝕜 i f x :=
  iteratedFDeriv_const_smul_apply hf
/-
**iteratedFDeriv_smul_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_smul_const_apply {f : E -> A} (hf : ContDiffAt 𝕜 i f x) : i
teratedFDeriv 𝕜 i (fun y => f y • v) x = ((ContinuousLinearMap.id 𝕜 A).smulRight
 v).compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x)
参数：hf : ContDiffAt 𝕜 i f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.iteratedFDeriv_comp_left`：ContinuousLinearMap.iterat
edFDeriv_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) {i : 
Nat} (hi : i <= n) : iteratedFDeri…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iteratedFDeriv_smul_const_apply {f : E → A} (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (fun y ↦ f y • v) x =
      ((ContinuousLinearMap.id 𝕜 A).smulRight v).compContinuousMultilinearMap
        (iteratedFDeriv 𝕜 i f x) :=
  (ContinuousLinearMap.id 𝕜 A).smulRight v |>.iteratedFDeriv_comp_left hf le_rfl
/-
**iteratedFDeriv_comp_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_comp_const_smul (a : 𝕜) (hf : ContDiff 𝕜 i f) : iteratedFDe
riv 𝕜 i (fun z => f (a • z)) = fun x => a ^ i • iteratedFDeriv 𝕜 i f (a • x)
参数：a : 𝕜；hf : ContDiff 𝕜 i f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `iteratedFDeriv_succ_eq_comp_left`：iteratedFDeriv_succ_eq_comp_left {n : 
Nat} : iteratedFDeriv 𝕜 (n + 1) f = (continuousMultilinearCurryLeftEquiv 𝕜 (fun 
_ : Fin (n + 1) => E) …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `fderiv_fun_const_smul`：fderiv_fun_const_smul (h : DifferentiableAt 𝕜 f x
) (c : R) : fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
（共 45 条，此处仅展示前 30 条）
-/
theorem iteratedFDeriv_comp_const_smul (a : 𝕜) (hf : ContDiff 𝕜 i f) :
    iteratedFDeriv 𝕜 i (fun z ↦ f (a • z)) = fun x ↦ a ^ i • iteratedFDeriv 𝕜 i f (a • x) := by
  induction i with
  | zero => ext; simp
  | succ i hi =>
    ext v
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, self_le_add_right, hf.of_le, hi,
      comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply, smul_apply]
    rw [fderiv_fun_const_smul, fderiv_comp_smul, smul_smul, ← pow_succ]
    · simp
    rw [← Function.comp_def (g := (a • ·))]
    apply DifferentiableAt.comp
    · exact hf.contDiffAt.differentiableAt_iteratedFDeriv (Nat.cast_lt.2 i.lt_succ_self)
    · exact differentiableAt_id.const_smul _

end ConstSMul

/-! ### Cartesian product of two functions -/

section prodMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
/-
**ContDiffWithinAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.prodMap' {s : Set E} {t : Set E'} {f : E -> F} {g : E' ->
 F'} {p : E × E'} (hf : ContDiffWithinAt 𝕜 n f s p.1) (hg : ContDiffWithinAt 𝕜 n
 g t p.2) : ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) p
参数：hf : ContDiffWithinAt 𝕜 n f s p.1；hg : ContDiffWithinAt 𝕜 n g t p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `contDiffWithinAt_fst`：contDiffWithinAt_fst {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.fst : E × F -> E) s p
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
· 使用定理 `contDiffWithinAt_snd`：contDiffWithinAt_snd {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.snd : E × F -> F) s p
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t

--- 原说明 ---
The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point.
-/
theorem ContDiffWithinAt.prodMap' {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {p : E × E'}
    (hf : ContDiffWithinAt 𝕜 n f s p.1) (hg : ContDiffWithinAt 𝕜 n g t p.2) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) p :=
  (hf.comp p contDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp p contDiffWithinAt_snd (prod_subset_preimage_snd _ _))

@[fun_prop]
/-
**ContDiffWithinAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.prodMap {s : Set E} {t : Set E'} {f : E -> F} {g : E' -> 
F'} {x : E} {y : E'} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 
n g t y) : ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y)
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.prodMap'`：ContDiffWithinAt.prodMap' {s : Set E} {t : Se
t E'} {f : E -> F} {g : E' -> F'} {p : E × E'} (hf : ContDiffWithinAt 𝕜 n f s p.
1) (hg : ContDi…
-/
theorem ContDiffWithinAt.prodMap {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g t y) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y) :=
  ContDiffWithinAt.prodMap' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
@[fun_prop]
/-
**ContDiffOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
 {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'
} {f : E -> F} {g : E' -> F'} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g t
) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t)
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.prodMk`：ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> 
G} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x :
 E => (…
· 使用定理 `ContDiffOn.comp`：ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f
 : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s 
t) : …
· 使用定理 `contDiffOn_fst`：contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.
fst : E × F -> E) s
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
· 使用定理 `contDiffOn_snd`：contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.
snd : E × F -> F) s
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t

--- 原说明 ---
The product map of two `C^n` functions on a set is `C^n` on the product set.
-/
theorem ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g t) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t) :=
  (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
/-
**ContDiffAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.prodMap {f : E -> F} {g : E' -> F'} {x : E} {y : E'} (hf : Cont
DiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y)
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffAt.eq_1`：∀ (𝕜 : Type u) [inst : NontriviallyNormedField 𝕜] {E : 
Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type 
uF} […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `ContDiffWithinAt.prodMap`：ContDiffWithinAt.prodMap {s : Set E} {t : Set 
E'} {f : E -> F} {g : E' -> F'} {x : E} {y : E'} (hf : ContDiffWithinAt 𝕜 n f s 
x) (hg : ContD…

--- 原说明 ---
The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point.
-/
theorem ContDiffAt.prodMap {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y) := by
  rw [ContDiffAt] at *
  simpa only [univ_prod_univ] using hf.prodMap hg

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
/-
**ContDiffAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.prodMap' {f : E -> F} {g : E' -> F'} {p : E × E'} (hf : ContDif
fAt 𝕜 n f p.1) (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p
参数：hf : ContDiffAt 𝕜 n f p.1；hg : ContDiffAt 𝕜 n g p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.prodMap`：ContDiffAt.prodMap {f : E -> F} {g : E' -> F'} {x : 
E} {y : E'} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n
 (Prod.m…

--- 原说明 ---
The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point.
-/
theorem ContDiffAt.prodMap' {f : E → F} {g : E' → F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
    (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p :=
  hf.prodMap hg

/-- The product map of two `C^n` functions is `C^n`. -/
@[fun_prop]
/-
**ContDiff.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.prodMap {f : E -> F} {g : E' -> F'} (hf : ContDiff 𝕜 n f) (hg : C
ontDiff 𝕜 n g) : ContDiff 𝕜 n (Prod.map f g)
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.prodMap`：ContDiffAt.prodMap {f : E -> F} {g : E' -> F'} {x : 
E} {y : E'} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n
 (Prod.m…

--- 原说明 ---
The product map of two `C^n` functions is `C^n`.
-/
theorem ContDiff.prodMap {f : E → F} {g : E' → F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (Prod.map f g) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prodMap (hg y)

@[fun_prop]
/-
**contDiff_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prodMk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀)
参数：f₀ : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiff_prodMk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀) :=
  contDiff_id.prodMk contDiff_const

@[fun_prop]
/-
**contDiff_prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prodMk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f)
参数：e₀ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.prodMk`：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDif
f 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiff_prodMk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f) :=
  contDiff_const.prodMk contDiff_id

end prodMap

/-!
### Inversion in a complete normed algebra (or more generally with summable geometric series)
-/

section AlgebraInverse

variable (𝕜)
variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element, as it is analytic. -/
@[fun_prop]
/-
**contDiffAt_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_ringInverse [HasSummableGeomSeries R] (x : Rˣ) : ContDiffAt 𝕜 n
 Ring.inverse (x : R)
参数：x : Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiffOn`：AnalyticOnNhd.contDiffOn (h : AnalyticOnNhd 𝕜 
f s) (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s
· 使用引理 `analyticOnNhd_inverse`：analyticOnNhd_inverse [HasSummableGeomSeries A] :
 AnalyticOnNhd 𝕜 Ring.inverse {x : A | IsUnit x}
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Units.isOpen`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSer
ies R], IsOpen {x | IsUnit x}
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, 
at each
invertible element, as it is analytic.
-/
theorem contDiffAt_ringInverse [HasSummableGeomSeries R] (x : Rˣ) :
    ContDiffAt 𝕜 n Ring.inverse (x : R) := by
  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
    Units.isOpen.uniqueDiffOn x x.isUnit
  exact this.contDiffAt (Units.isOpen.mem_nhds x.isUnit)

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

@[fun_prop]
/-
**contDiffAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_inv {x : 𝕜'} (hx : x != 0) {n} : ContDiffAt 𝕜 n Inv.inv x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `contDiffAt_ringInverse`：contDiffAt_ringInverse [HasSummableGeomSeries R]
 (x : Rˣ) : ContDiffAt 𝕜 n Ring.inverse (x : R)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
-/
theorem contDiffAt_inv {x : 𝕜'} (hx : x ≠ 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
  simpa only [Ring.inverse_eq_inv'] using! contDiffAt_ringInverse 𝕜 (Units.mk0 x hx)

@[fun_prop]
/-
**contDiffOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' -> 𝕜') {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiffAt_inv`：contDiffAt_inv {x : 𝕜'} (hx : x != 0) {n} : ContDiffAt 𝕜
 n Inv.inv x
-/
theorem contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' → 𝕜') {0}ᶜ := fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt

variable {𝕜}

@[to_fun (attr := fun_prop)]
/-
**ContDiffWithinAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.inv {f : E -> 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (
hx : f x != 0) : ContDiffWithinAt 𝕜 n f⁻¹ s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `contDiffAt_inv`：contDiffAt_inv {x : 𝕜'} (hx : x != 0) {n} : ContDiffAt 𝕜
 n Inv.inv x
-/
theorem ContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt 𝕜 n f⁻¹ s x :=
  (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf

@[to_fun (attr := fun_prop)]
/-
**ContDiffOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.inv {f : E -> 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : forall x in s,
 f x != 0) : ContDiffOn 𝕜 n f⁻¹ s
参数：hf : ContDiffOn 𝕜 n f s；h : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.inv`：ContDiffWithinAt.inv {f : E -> 𝕜'} {n} (hf : ContD
iffWithinAt 𝕜 n f s x) (hx : f x != 0) : ContDiffWithinAt 𝕜 n f⁻¹ s x
· 使用定理 `ContDiffOn.contDiffWithinAt`：ContDiffOn.contDiffWithinAt (h : ContDiffOn
 𝕜 n f s) (hx : x in s) : ContDiffWithinAt 𝕜 n f s x
-/
theorem ContDiffOn.inv {f : E → 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn 𝕜 n f⁻¹ s := fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.inv {f : E → 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
    ContDiffAt 𝕜 n f⁻¹ x :=
  hf.inv hx

@[to_fun (attr := fun_prop)]
/-
**ContDiff.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.inv {f : E -> 𝕜'} (hf : ContDiff 𝕜 n f) (h : forall x, f x != 0) 
: ContDiff 𝕜 n f⁻¹
参数：hf : ContDiff 𝕜 n f；h : forall x, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {
n : …
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.inv {f : E → 𝕜'} (hf : ContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
    ContDiff 𝕜 n f⁻¹ := by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)

-- TODO: generalize to `f g : E → 𝕜'`
@[to_fun (attr := fun_prop)]
/-
**ContDiffWithinAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.div {f g : E -> 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x) 
(hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x != 0) : ContDiffWithinAt 𝕜 n (f / g)
 s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x；hx : g x != 0
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ContDiffWithinAt.mul`：ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `ContDiffWithinAt.fun_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {s : Set E} {…
-/
theorem ContDiffWithinAt.div {f g : E → 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x ≠ 0) :
    ContDiffWithinAt 𝕜 n (f / g) s x := by
  change ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x
  simpa only [div_eq_mul_inv] using hf.mul (hg.fun_inv hx)

@[to_fun (attr := fun_prop)]
/-
**ContDiffOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.div {f g : E -> 𝕜} {n} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiff
On 𝕜 n g s) (h₀ : forall x in s, g x != 0) : ContDiffOn 𝕜 n (f / g) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s；h₀ : forall x in s, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.div`：ContDiffWithinAt.div {f g : E -> 𝕜} {n} (hf : Cont
DiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x != 0) : Cont
DiffWithin…
-/
theorem ContDiffOn.div {f g : E → 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn 𝕜 n (f / g) s := fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)

@[to_fun (attr := fun_prop)]
nonrec theorem ContDiffAt.div {f g : E → 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x ≠ 0) : ContDiffAt 𝕜 n (f / g) x :=
  hf.div hg hx

@[to_fun (attr := fun_prop)]
/-
**ContDiff.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.div {f g : E -> 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g
) (h0 : forall x, g x != 0) : ContDiff 𝕜 n (f / g)
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g；h0 : forall x, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.div`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {
f g …
-/
theorem ContDiff.div {f g : E → 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (h0 : ∀ x, g x ≠ 0) : ContDiff 𝕜 n (f / g) := by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)

end AlgebraInverse

/-! ### Inversion of continuous linear maps between Banach spaces -/

section MapInverse

open ContinuousLinearMap

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
@[fun_prop]
/-
**contDiffAt_map_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) : ContDiffAt 𝕜 n 
inverse (e : E ->L[𝕜] F)
参数：e : E ≃L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.inverse_eq_ringInverse`：inverse_eq_ringInverse (e : 
M ≃L[R] M₂) (f : M ->L[R] M₂) : inverse f = ((e.symm : M₂ ->L[R] M).comp f)⁻¹ʳ ∘
L e.symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiff.clm_comp`：ContDiff.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E -
>L[𝕜] F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g 
x).comp…
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.coe_symm_comp_coe`：coe_symm_comp_coe (e : M₁ ≃SL[σ
₁₂] M₂) : (e.symm : M₂ ->SL[σ₂₁] M₁).comp (e : M₁ ->SL[σ₁₂] M₂) = ContinuousLine
arMap.id R₁ M₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `contDiffAt_ringInverse`：contDiffAt_ringInverse [HasSummableGeomSeries R]
 (x : Rˣ) : ContDiffAt 𝕜 n Ring.inverse (x : R)
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E

--- 原说明 ---
At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the op
eration of
inversion is `C^n`, for all `n`.
-/
theorem contDiffAt_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) :
    ContDiffAt 𝕜 n inverse (e : E →L[𝕜] F) := by
  nontriviality E
  -- first, we use the lemma `inverse_eq_ringInverse` to rewrite in terms of `Ring.inverse` in the
  -- ring `E →L[𝕜] E`
  let O₁ : (E →L[𝕜] E) → F →L[𝕜] E := fun f => f.comp (e.symm : F →L[𝕜] E)
  let O₂ : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have : ContinuousLinearMap.inverse = O₁ ∘ Ring.inverse ∘ O₂ := funext (inverse_eq_ringInverse e)
  rw [this]
  -- `O₁` and `O₂` are `ContDiff`,
  -- so we reduce to proving that `Ring.inverse` is `ContDiff`
  have h₁ : ContDiff 𝕜 n O₁ := contDiff_id.clm_comp contDiff_const
  have h₂ : ContDiff 𝕜 n O₂ := contDiff_const.clm_comp contDiff_id
  refine h₁.contDiffAt.comp _ (ContDiffAt.comp _ ?_ h₂.contDiffAt)
  convert! contDiffAt_ringInverse 𝕜 (1 : (E →L[𝕜] E)ˣ)
  simp [O₂, one_def]

/-- At an invertible map `e : M →L[R] M₂` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
/-
**ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse [CompleteSpace E] 
{e : E ->L[𝕜] F} (he : e.IsInvertible) : ContDiffAt 𝕜 n inverse e
参数：he : e.IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffAt_map_inverse`：contDiffAt_map_inverse [CompleteSpace E] (e : E 
≃L[𝕜] F) : ContDiffAt 𝕜 n inverse (e : E ->L[𝕜] F)

--- 原说明 ---
At an invertible map `e : M →L[R] M₂` between Banach spaces, the operation of
inversion is `C^n`, for all `n`.
-/
theorem ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse [CompleteSpace E] {e : E →L[𝕜] F}
    (he : e.IsInvertible) : ContDiffAt 𝕜 n inverse e := by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

end MapInverse

section FunctionInverse

open ContinuousLinearMap

/-- If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**OpenPartialHomeomorph.contDiffAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.contDiffAt_symm [CompleteSpace E] (f : OpenPartialHo
meomorph E F) {f₀' : E ≃L[𝕜] F} {a : F} (ha : a in f.target) (hf₀' : HasFDerivAt
 f (f₀' : E ->L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffA
t 𝕜 n f.symm a
参数：f : OpenPartialHomeomorph E F；ha : a in f.target；hf₀' : HasFDerivAt f (f₀' : 
E ->L[𝕜] F) (f.symm a)；hf : ContDiffAt 𝕜 n f (f.symm a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.contDiffAt`：AnalyticAt.contDiffAt [CompleteSpace F] (h : Anal
yticAt 𝕜 f x) : ContDiffAt 𝕜 n f x
· 使用定理 `OpenPartialHomeomorph.analyticAt_symm`：OpenPartialHomeomorph.analyticAt_
symm (f : OpenPartialHomeomorph E F) {a : F} {i : E ≃L[𝕜] F} (h0 : a in f.target
) (h : AnalyticAt 𝕜 f (f.sy…
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `ENat.nat_induction`：nat_induction {motive : Nat∞ -> Prop} (a : Nat∞) (ze
ro : motive 0) (succ : forall n : Nat, motive n -> motive n.succ) (top : (forall
 n : Nat…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffAt_zero`：contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ exists u in 𝓝 x,
 ContinuousOn f u
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffAt_succ_iff_hasFDerivAt`：contDiffAt_succ_iff_hasFDerivAt {n : Na
t} : ContDiffAt 𝕜 (n + 1) f x ↔ exists f' : E -> E ->L[𝕜] F, (exists u in 𝓝 x, f
orall x in u, HasFDer…
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `ContinuousLinearEquiv.nhds`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage_symm`：isOpen_inter_preimage_
symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s)
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem OpenPartialHomeomorph.contDiffAt_symm [CompleteSpace E] (f : OpenPartialHomeomorph E F)
    {f₀' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
    (hf₀' : HasFDerivAt f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a := by
  match n with
  | ω =>
    apply AnalyticAt.contDiffAt
    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
  | (n : ℕ∞) =>
    -- We prove this by induction on `n`
    induction n using ENat.nat_induction with
    | zero =>
      apply contDiffAt_zero.2
      exact ⟨f.target, IsOpen.mem_nhds f.open_target ha, f.continuousOn_invFun⟩
    | succ n IH =>
      obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hf
      apply contDiffAt_succ_iff_hasFDerivAt.2
      -- For showing `n.succ` times continuous differentiability (the main inductive step), it
      -- suffices to produce the derivative and show that it is `n` times continuously
      -- differentiable
      have eq_f₀' : f' (f.symm a) = f₀' := (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'
      -- This follows by a bootstrapping formula expressing the derivative as a
      -- function of `f` itself
      refine ⟨inverse ∘ f' ∘ f.symm, ?_, ?_⟩
      · -- We first check that the derivative of `f` is that formula
        have h_nhds : { y : E | ∃ e : E ≃L[𝕜] F, ↑e = f' y } ∈ 𝓝 (f.symm a) := by
          have hf₀' := f₀'.nhds
          rw [← eq_f₀'] at hf₀'
          exact hf'.continuousAt.preimage_mem_nhds hf₀'
        obtain ⟨t, htu, ht, htf⟩ := mem_nhds_iff.mp (Filter.inter_mem hu h_nhds)
        use f.target ∩ f.symm ⁻¹' t
        refine ⟨IsOpen.mem_nhds ?_ ?_, ?_⟩
        · exact f.isOpen_inter_preimage_symm ht
        · exact mem_inter ha (mem_preimage.mpr htf)
        intro x hx
        obtain ⟨hxu, e, he⟩ := htu hx.2
        have h_deriv : HasFDerivAt f (e : E →L[𝕜] F) (f.symm x) := by
          rw [he]
          exact hff' (f.symm x) hxu
        convert! f.hasFDerivAt_symm hx.1 h_deriv
        simp [← he]
      · -- Then we check that the formula, being a composition of `ContDiff` pieces, is
        -- itself `ContDiff`
        have h_deriv₁ : ContDiffAt 𝕜 n inverse (f' (f.symm a)) := by
          rw [eq_f₀']
          exact contDiffAt_map_inverse _
        have h_deriv₂ : ContDiffAt 𝕜 n f.symm a := by
          refine IH (hf.of_le ?_)
          norm_cast
          exact Nat.le_succ n
        exact (h_deriv₁.comp _ hf').comp _ h_deriv₂
    | top Itop => exact contDiffAt_infty.mpr fun n ↦ Itop n (contDiffAt_infty.mp hf n)

/-- If `f` is an `n` times continuously differentiable homeomorphism,
and if the derivative of `f` at each point is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**Homeomorph.contDiff_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.contDiff_symm [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E -> E ≃L[𝕜
] F} (hf₀' : forall a, HasFDerivAt f (f₀' a : E ->L[𝕜] F) a) (hf : ContDiff 𝕜 n 
(f : E -> F)) : ContDiff 𝕜 n (f.symm : F -> E)
参数：f : E ≃ₜ F；hf₀' : forall a, HasFDerivAt f (f₀' a : E ->L[𝕜] F) a；hf : ContDif
f 𝕜 n (f : E -> F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `OpenPartialHomeomorph.contDiffAt_symm`：OpenPartialHomeomorph.contDiffAt_
symm [CompleteSpace E] (f : OpenPartialHomeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
 (ha : a in f.target) (hf₀'…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
If `f` is an `n` times continuously differentiable homeomorphism,
and if the derivative of `f` at each point is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem Homeomorph.contDiff_symm [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E → E ≃L[𝕜] F}
    (hf₀' : ∀ a, HasFDerivAt f (f₀' a : E →L[𝕜] F) a) (hf : ContDiff 𝕜 n (f : E → F)) :
    ContDiff 𝕜 n (f.symm : F → E) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ x) (hf₀' _) hf.contDiffAt

/-- Let `f` be a local homeomorphism of a nontrivially normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**OpenPartialHomeomorph.contDiffAt_symm_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.contDiffAt_symm_deriv [CompleteSpace 𝕜] (f : OpenPar
tialHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (h₀ : f₀' != 0) (ha : a in f.target) (hf₀' : Has
DerivAt f f₀' (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.
symm a
参数：f : OpenPartialHomeomorph 𝕜 𝕜；h₀ : f₀' != 0；ha : a in f.target；hf₀' : HasDeri
vAt f f₀' (f.symm a)；hf : ContDiffAt 𝕜 n f (f.symm a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `OpenPartialHomeomorph.contDiffAt_symm`：OpenPartialHomeomorph.contDiffAt_
symm [CompleteSpace E] (f : OpenPartialHomeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
 (ha : a in f.target) (hf₀'…
· 使用定理 `HasDerivAt.hasFDerivAt_equiv`：HasDerivAt.hasFDerivAt_equiv {f : 𝕜 -> 𝕜} 
{f' x : 𝕜} (hf : HasDerivAt f f' x) (hf' : f' != 0) : HasFDerivAt f (ContinuousL
inearEquiv.unitsEq…

--- 原说明 ---
Let `f` be a local homeomorphism of a nontrivially normed field, let `a` be a po
int in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if th
e derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at
 the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem OpenPartialHomeomorph.contDiffAt_symm_deriv [CompleteSpace 𝕜]
    (f : OpenPartialHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target)
    (hf₀' : HasDerivAt f f₀' (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a :=
  f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf

/-- Let `f` be an `n` times continuously differentiable homeomorphism of a nontrivially normed
field.  Suppose that the derivative of `f` is never equal to zero. Then `f.symm` is `n` times
continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**Homeomorph.contDiff_symm_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.contDiff_symm_deriv [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 -> 𝕜
} (h₀ : forall x, f' x != 0) (hf' : forall x, HasDerivAt f (f' x) x) (hf : ContD
iff 𝕜 n (f : 𝕜 -> 𝕜)) : ContDiff 𝕜 n (f.symm : 𝕜 -> 𝕜)
参数：f : 𝕜 ≃ₜ 𝕜；h₀ : forall x, f' x != 0；hf' : forall x, HasDerivAt f (f' x) x；hf 
: ContDiff 𝕜 n (f : 𝕜 -> 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `OpenPartialHomeomorph.contDiffAt_symm_deriv`：OpenPartialHomeomorph.contD
iffAt_symm_deriv [CompleteSpace 𝕜] (f : OpenPartialHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (
h₀ : f₀' != 0) (ha : a in f.targe…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x

--- 原说明 ---
Let `f` be an `n` times continuously differentiable homeomorphism of a nontrivia
lly normed
field.  Suppose that the derivative of `f` is never equal to zero. Then `f.symm`
 is `n` times
continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem Homeomorph.contDiff_symm_deriv [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 → 𝕜}
    (h₀ : ∀ x, f' x ≠ 0) (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : ContDiff 𝕜 n (f : 𝕜 → 𝕜)) :
    ContDiff 𝕜 n (f.symm : 𝕜 → 𝕜) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toOpenPartialHomeomorph.contDiffAt_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.contDiffAt

namespace OpenPartialHomeomorph

variable (𝕜)

/-- Restrict an open partial homeomorphism to the subsets of the source and target
that consist of points `x ∈ f.source`, `y = f x ∈ f.target`
such that `f` is `C^n` at `x` and `f.symm` is `C^n` at `y`.

Note that `n` is a natural number or `ω`, but not `∞`,
because the set of points of `C^∞`-smoothness of `f` is not guaranteed to be open. -/
@[simps! apply symm_apply source target]
/-
**OpenPartialHomeomorph.restrContDiff** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：restrContDiff (f : OpenPartialHomeomorph E F) (n : Nat∞ω) (hn : n != ∞) : 
OpenPartialHomeomorph E F
参数：f : OpenPartialHomeomorph E F；n : Nat∞ω；hn : n != ∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an open partial homeomorphism to the subsets of the source and target
that consist of points `x ∈ f.source`, `y = f x ∈ f.target`
such that `f` is `C^n` at `x` and `f.symm` is `C^n` at `y`.

Note that `n` is a natural number or `ω`, but not `∞`,
because the set of points of `C^∞`-smoothness of `f` is not guaranteed to be ope
n.
-/
def restrContDiff (f : OpenPartialHomeomorph E F) (n : ℕ∞ω) (hn : n ≠ ∞) :
    OpenPartialHomeomorph E F :=
  haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx ↦ by
    simp [hx, and_comm]
  H.restr <| isOpen_iff_mem_nhds.2 fun _ ⟨hxs, hxf, hxf'⟩ ↦
    inter_mem (f.open_source.mem_nhds hxs) <| (hxf.eventually hn).and <|
    f.continuousAt hxs (hxf'.eventually hn)
/-
**OpenPartialHomeomorph.contDiffOn_restrContDiff_source** 是 Mathlib 中的一个引理，位于命名空
间 `OpenPartialHomeomorph`。
形式化陈述：contDiffOn_restrContDiff_source (f : OpenPartialHomeomorph E F) {n : Nat∞ω
} (hn : n != ∞) : ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n hn).source
参数：f : OpenPartialHomeomorph E F；hn : n != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma contDiffOn_restrContDiff_source (f : OpenPartialHomeomorph E F) {n : ℕ∞ω}
    (hn : n ≠ ∞) : ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n hn).source :=
  fun _x hx ↦ hx.2.1.contDiffWithinAt
/-
**OpenPartialHomeomorph.contDiffOn_restrContDiff_target** 是 Mathlib 中的一个引理，位于命名空
间 `OpenPartialHomeomorph`。
形式化陈述：contDiffOn_restrContDiff_target (f : OpenPartialHomeomorph E F) {n : Nat∞ω
} (hn : n != ∞) : ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n hn).target
参数：f : OpenPartialHomeomorph E F；hn : n != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma contDiffOn_restrContDiff_target (f : OpenPartialHomeomorph E F) {n : ℕ∞ω}
    (hn : n ≠ ∞) : ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n hn).target :=
  fun _x hx ↦ hx.2.1.contDiffWithinAt

end OpenPartialHomeomorph

end FunctionInverse

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/


variable (𝕜)
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
variable {p' : E → FormalMultilinearSeries 𝕜' E F}

/-
**HasFTaylorSeriesUpToOn.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.restrictScalars {n : Nat∞ω} (h : HasFTaylorSeriesUp
ToOn n f p' s) : HasFTaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) 
s where zero_eq x hx
参数：h : HasFTaylorSeriesUpToOn n f p' s。
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
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `ContinuousMultilinearMap.instIsScalarTower`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousMultilinearMap.continuous_restrictScalars`：continuous_restrict
Scalars : Continuous (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F -> Con
tinuousMultilinearMap 𝕜' E F)
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
-/
theorem HasFTaylorSeriesUpToOn.restrictScalars {n : ℕ∞ω}
    (h : HasFTaylorSeriesUpToOn n f p' s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜 :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)
/-
**ContDiffWithinAt.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) : Cont
DiffWithinAt 𝕜 n f s x
参数：h : ContDiffWithinAt 𝕜' n f s x。
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
· 使用定理 `HasFTaylorSeriesUpToOn.restrictScalars`：HasFTaylorSeriesUpToOn.restrictS
calars {n : Nat∞ω} (h : HasFTaylorSeriesUpToOn n f p' s) : HasFTaylorSeriesUpToO
n n f (fun x => (p' x).restr…
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOn.restrictScalars`：AnalyticOn.restrictScalars (hf : AnalyticOn 
𝕜' f s) : AnalyticOn 𝕜 f s
· 使用定理 `ContinuousMultilinearMap.instIsScalarTower`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) :
    ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω =>
    obtain ⟨u, u_mem, p', hp', Hp'⟩ := h
    refine ⟨u, u_mem, _, hp'.restrictScalars _, fun i ↦ ?_⟩
    change AnalyticOn 𝕜 (fun x ↦ ContinuousMultilinearMap.restrictScalarsLinear 𝕜 (p' x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (Hp' i).restrictScalars (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : ℕ∞) =>
    intro m hm
    rcases h m hm with ⟨u, u_mem, p', hp'⟩
    exact ⟨u, u_mem, _, hp'.restrictScalars _⟩
/-
**ContDiffOn.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s
参数：h : ContDiffOn 𝕜' n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.restrict_scalars`：ContDiffWithinAt.restrict_scalars (h 
: ContDiffWithinAt 𝕜' n f s x) : ContDiffWithinAt 𝕜 n f s x
-/
theorem ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s := fun x hx =>
  (h x hx).restrict_scalars _
/-
**ContDiffAt.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x
参数：h : ContDiffAt 𝕜' n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.restrict_scalars`：ContDiffWithinAt.restrict_scalars (h 
: ContDiffWithinAt 𝕜' n f s x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
-/
theorem ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x :=
  contDiffWithinAt_univ.1 <| h.contDiffWithinAt.restrict_scalars _
/-
**ContDiff.restrict_scalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f
参数：h : ContDiff 𝕜' n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.restrict_scalars`：ContDiffAt.restrict_scalars (h : ContDiffAt
 𝕜' n f x) : ContDiffAt 𝕜 n f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _

end RestrictScalars

