/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Analyticity of Harmonic Functions

If `f : ℂ → ℝ` is harmonic at `x`, we show that `∂f/∂1 - I • ∂f/∂I` is complex-analytic at `x`. If
`f` is harmonic on an open ball, then it is the real part of a function `F : ℂ → ℂ` that is
holomorphic on the ball.  This implies in particular that harmonic functions are real-analytic.
-/

public section

open Complex InnerProductSpace Metric Set Topology

variable
  {f : ℂ → ℝ} {x : ℂ}

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex differentiable at `x`.
-/
/-
**HarmonicAt.differentiableAt_complex_partial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HarmonicAt.differentiableAt_complex_partial (hf : HarmonicAt f x) : Differ
entiableAt Complex (fun z => fderiv Real f z 1 - I * fderiv Real f z I) x
参数：hf : HarmonicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_complex_iff_differentiableAt_real`：differentiableAt_com
plex_iff_differentiableAt_real : DifferentiableAt Complex f x ↔ DifferentiableAt
 Real f x ∧ fderiv Real f x I = I • fder…
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用定理 `DifferentiableAt.clm_apply`：DifferentiableAt.clm_apply (hc : Differentia
bleAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) : DifferentiableAt 𝕜 (fun y => (c y) 
(u y)) x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.differentiableAt_one`：ContDiffAt.differentiableAt_one (h : Co
ntDiffAt 𝕜 1 f x) : DifferentiableAt 𝕜 f x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContDiffAt.fderiv_succ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {
G : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 :…
· 使用定理 `ContDiffAt.fun_comp`：ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g 
(f x)) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => g (f x)) x
· 使用定理 `ContDiffAt.snd`：ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).2) x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `DifferentiableAt.smul`：DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c 
x) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (c • f) x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `fderiv_sub`：fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : Differentiabl
eAt 𝕜 g x) : fderiv 𝕜 (f - g) x = fderiv 𝕜 f x - fderiv 𝕜 g x
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `fderiv_const_smul`：fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R
) : fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x
· 使用定理 `fderiv_comp`：fderiv_comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) 
(hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fd
e…
（共 106 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex different
iable at `x`.
-/
theorem HarmonicAt.differentiableAt_complex_partial (hf : HarmonicAt f x) :
    DifferentiableAt ℂ (fun z ↦ fderiv ℝ f z 1 - I * fderiv ℝ f z I) x := by
  have : (fun z ↦ fderiv ℝ f z 1 - I * fderiv ℝ f z I) =
      (ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)) := by
    ext; simp
  rw [this]
  have h₁f := hf.1
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨by fun_prop, ?_⟩
  rw [fderiv_sub (by fun_prop) (by fun_prop), fderiv_const_smul (by fun_prop)]
  repeat rw [fderiv_comp]; all_goals try fun_prop
  simp only [ContinuousLinearMap.fderiv, sub_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply,
    smul_apply, smul_eq_mul]
  ring_nf
  rw [fderiv_clm_apply (by fun_prop) (by fun_prop), fderiv_clm_apply (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, I_sq, neg_mul, one_mul, sub_neg_eq_add]
  rw [add_comm, sub_eq_add_neg]
  congr 1
  · norm_cast
    apply h₁f.isSymmSndFDerivAt (by simp)
  · have h₂f := hf.2.eq_of_nhds
    simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply,
      add_eq_zero_iff_eq_neg] at h₂f
    simp [h₂f]

/--
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex analytic at `x`.
-/
/-
**HarmonicAt.analyticAt_complex_partial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HarmonicAt.analyticAt_complex_partial (hf : HarmonicAt f x) : AnalyticAt C
omplex (fun z => fderiv Real f z 1 - I * fderiv Real f z I) x
参数：hf : HarmonicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `DifferentiableOn.analyticAt`：∀ {E : Type u} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E}   {z : ℂ}
, DifferentiableO…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HarmonicAt.differentiableAt_complex_partial`：HarmonicAt.differentiableAt
_complex_partial (hf : HarmonicAt f x) : DifferentiableAt Complex (fun z => fder
iv Real f z 1 - I * fderiv Real f…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `InnerProductSpace.isOpen_setOfPred_harmonicAt`：isOpen_setOfPred_harmonic
At : IsOpen { x : E | HarmonicAt f x }

--- 原说明 ---
If `f : ℂ → ℝ` is harmonic at `x`, then `∂f/∂1 - I • ∂f/∂I` is complex analytic 
at `x`.
-/
theorem HarmonicAt.analyticAt_complex_partial (hf : HarmonicAt f x) :
    AnalyticAt ℂ (fun z ↦ fderiv ℝ f z 1 - I * fderiv ℝ f z I) x :=
  DifferentiableOn.analyticAt (s := { x | HarmonicAt f x })
    (fun _ hy ↦ (HarmonicAt.differentiableAt_complex_partial hy).differentiableWithinAt)
    ((isOpen_setOfPred_harmonicAt f).mem_nhds hf)

/-
If a function `f : ℂ → ℝ` is harmonic on an open ball, then `f` is the real part of a function
`F : ℂ → ℂ` that is holomorphic on the ball.
-/
/-
**InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : Compl
ex} {R : Real} (hf : HarmonicOnNhd f (ball z R)) : exists F : Complex -> Complex
, (AnalyticOnNhd Complex F (ball z R)) ∧ ((ball z R).EqOn (fun z => (F z).re) f)
参数：hf : HarmonicOnNhd f (ball z R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HarmonicAt.differentiableAt_complex_partial`：HarmonicAt.differentiableAt
_complex_partial (hf : HarmonicAt f x) : DifferentiableAt Complex (fun z => fder
iv Real f z 1 - I * fderiv Real f…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.IsExactOn.with_val_at`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {s : Set ℂ},   Complex.IsExactOn f 
s → ∀ (x₀ : ℂ) (y :…
· 使用定理 `DifferentiableOn.isExactOn_ball`：∀ {E : Type u_1} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℂ E] {c : ℂ} {r : ℝ} {f : ℂ → E} [CompleteSpace E]
,   DifferentiableOn …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableOn.restrictScalars`：DifferentiableOn.restrictScalars (h : 
DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Convex.eqOn_of_fderivWithin_eq`：eqOn_of_fderivWithin_eq (hs : Convex Rea
l s) (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDi
ffOn 𝕜 s) (hf' : s.E…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `Differentiable.comp_differentiableOn`：Differentiable.comp_differentiable
On {g : F -> G} (hg : Differentiable 𝕜 g) (hf : DifferentiableOn 𝕜 f s) : Differ
entiableOn 𝕜 (g ∘ f) s
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f : ℂ → ℝ` is harmonic on an open ball, then `f` is the real part
 of a function
`F : ℂ → ℂ` that is holomorphic on the ball.
-/
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : ℂ} {R : ℝ}
    (hf : HarmonicOnNhd f (ball z R)) :
    ∃ F : ℂ → ℂ, (AnalyticOnNhd ℂ F (ball z R)) ∧ ((ball z R).EqOn (fun z ↦ (F z).re) f) := by
  by_cases hR : R ≤ 0
  · simp [ball_eq_empty.2 hR]
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : DifferentiableOn ℂ g (ball z R) :=
    fun x hx ↦ (HarmonicAt.differentiableAt_complex_partial (hf x hx)).differentiableWithinAt
  obtain ⟨F, hF⟩ := hg.isExactOn_ball.with_val_at z (f z)
  have h₁F : DifferentiableOn ℂ F (ball z R) :=
    fun x hx ↦ (hF.2 x hx).differentiableAt.differentiableWithinAt
  have h₂F : DifferentiableOn ℝ F (ball z R) := h₁F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
  use F, h₁F.analyticOnNhd isOpen_ball
  rw [(by aesop : (fun z ↦ (F z).re) = Complex.reCLM ∘ F)]
  intro x hx
  apply (convex_ball z R).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := z)
  · exact reCLM.differentiable.comp_differentiableOn h₂F
  · exact fun y hy ↦ (ContDiffAt.differentiableAt (hf y hy).1 two_ne_zero).differentiableWithinAt
  · exact isOpen_ball.uniqueDiffOn
  · intro y hy
    have h₄F := (hF.2 y hy).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy)
      (reCLM.differentiableAt.comp y h₅F), fderivWithin_eq_fderiv
      (isOpen_ball.uniqueDiffWithinAt hy) ((hf y hy).1.differentiableAt two_ne_zero), fderiv_comp y
      (by fun_prop) h₅F, ContinuousLinearMap.fderiv, h₄F.fderiv_restrictScalars (𝕜 := ℝ)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
    rw [map_add, map_smul, map_smul]
    simp [HasDerivAt.deriv (hF.2 y hy), g]
  all_goals simp_all

@[deprecated (since := "2026-03-03")]
alias harmonic_is_realOfHolomorphic :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq

/--
If a function `f : ℂ → ℝ` is harmonic, then `f` is the real part of a holomorphic function.
-/
/-
**InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq {f : Compl
ex -> Real} (hf : HarmonicOnNhd f univ) : exists F : Complex -> Complex, (Analyt
icOnNhd Complex F univ) ∧ ((fun z => (F z).re) = f)
参数：hf : HarmonicOnNhd f univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `HarmonicAt.differentiableAt_complex_partial`：HarmonicAt.differentiableAt
_complex_partial (hf : HarmonicAt f x) : DifferentiableAt Complex (fun z => fder
iv Real f z 1 - I * fderiv Real f…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.IsExactOn.with_val_at`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {s : Set ℂ},   Complex.IsExactOn f 
s → ∀ (x₀ : ℂ) (y :…
· 使用定理 `Differentiable.isExactOn_univ`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} [CompleteSpace E],   Differentiable
 ℂ f → Complex.IsEx…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Differentiable.restrictScalars`：Differentiable.restrictScalars (h : Diff
erentiable 𝕜' f) : Differentiable 𝕜 f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.reCLM_apply`：∀ (z : ℂ), Complex.reCLM z = z.re
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Convex.eqOn_of_fderivWithin_eq`：eqOn_of_fderivWithin_eq (hs : Convex Rea
l s) (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDi
ffOn 𝕜 s) (hf' : s.E…
（共 86 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f : ℂ → ℝ` is harmonic, then `f` is the real part of a holomorphi
c function.
-/
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f univ) :
    ∃ F : ℂ → ℂ, (AnalyticOnNhd ℂ F univ) ∧ ((fun z ↦ (F z).re) = f) := by
  let g := ofRealCLM ∘ (fderiv ℝ f · 1) - I • ofRealCLM ∘ (fderiv ℝ f · I)
  have hg : Differentiable ℂ g :=
    fun x ↦ (HarmonicAt.differentiableAt_complex_partial (hf x (mem_univ x)))
  obtain ⟨F, hF⟩ := hg.isExactOn_univ.with_val_at 0 (f 0)
  have h₁F : ∀ z₁, HasDerivAt F (g z₁) z₁ := by simp_all
  have h₂F : Differentiable ℂ F := fun x ↦ (h₁F x).differentiableAt
  have h₃F : Differentiable ℝ F := h₂F.restrictScalars (𝕜 := ℝ)
  use F, (h₂F.differentiableOn).analyticOnNhd isOpen_univ
  ext x
  rw [← Complex.reCLM_apply, ← Function.comp_apply (f := reCLM)]
  refine (convex_univ).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := 0) (by fun_prop) ?hd ?_ ?heq ?_ ?_ ?_
  case hd => exact hf.contDiffOn.differentiableOn two_ne_zero
  case heq =>
    intro y hy
    simp only [fderivWithin_univ]
    rw [fderiv_comp y (by fun_prop) (by fun_prop)]
    ext x
    trans fderiv ℝ f y (x.re • (1 : ℂ) + x.im • (I : ℂ))
    · simp only [map_smul, map_add]
      simp [(h₁F y).hasFDerivAt.restrictScalars ℝ |>.fderiv, g]
    · simp
  all_goals simp_all

@[deprecated (since := "2026-03-03")]
alias InnerProductSpace.harmonic_is_realOfHolomorphic_univ :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq

/-
Harmonic functions are real analytic.
TODO: Prove this for harmonic functions on an arbitrary f.d. inner product space (not just on `ℂ`).
-/
/-
**HarmonicAt.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HarmonicAt.analyticAt (hf : HarmonicAt f x) : AnalyticAt Real f x
参数：hf : HarmonicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `InnerProductSpace.isOpen_setOfPred_harmonicAt`：isOpen_setOfPred_harmonic
At : IsOpen { x : E | HarmonicAt f x }
· 使用定理 `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`：InnerPr
oductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : Complex} {R : Real
} (hf : HarmonicOnNhd f (ball z R)) : exists F : Comp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `analyticAt_congr`：analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x 
↔ AnalyticAt 𝕜 g x
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticAt.restrictScalars`：AnalyticAt.restrictScalars (hf : AnalyticAt 
𝕜' f x) : AnalyticAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε

--- 原说明 ---
Harmonic functions are real analytic.
TODO: Prove this for harmonic functions on an arbitrary f.d. inner product space
 (not just on `ℂ`).
-/
theorem HarmonicAt.analyticAt (hf : HarmonicAt f x) : AnalyticAt ℝ f x := by
  obtain ⟨ε, h₁ε, h₂ε⟩ := isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := f)) x hf
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun _ hy ↦ h₂ε hy)
  rw [analyticAt_congr (Filter.eventually_of_mem (ball_mem_nhds x h₁ε) (fun y hy ↦ h₂F.symm hy))]
  exact (reCLM.analyticAt (F x)).comp (h₁F x (mem_ball_self h₁ε)).restrictScalars
