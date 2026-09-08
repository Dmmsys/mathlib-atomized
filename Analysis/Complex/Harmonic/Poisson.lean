/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.Complex.Poisson

/-!
# Poisson Integral Formula

This file establishes several versions of the **Poisson Integral Formula** for harmonic functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.

TODO: Extend this formula to vector-valued harmonic functions
-/

public section

open Complex InnerProductSpace Metric Real Topology

variable
  {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

namespace InnerProductSpace

/-
**InnerProductSpace.continuousOn_herglotz_riesz** 是 Mathlib 中的一个引理，位于命名空间 `Inner
ProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousOn_herglotz_riesz (_ : w ∈ ball c R) :
    ContinuousOn (fun x ↦ ((x - c + (w - c)) / (x - c - (w - c))).re)
      {z | ‖z - c‖ ∈ Set.Ioc ‖w - c‖ R} := by
  have : ∀ x ∈ {z | ‖z - c‖ ∈ Set.Ioc ‖w - c‖ R}, x - c - (w - c) ≠ 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
/-
**InnerProductSpace.HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul** 是 
Mathlib 中的一个定理，位于命名空间 `InnerProductSpace.HarmonicOnNhd`。
形式化陈述：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicOnNhd f (Metr
ic.closedBall c R) →     w ∈ Metric.ball c R → Real.circleAverage (Complex.re ∘ 
herglotzRieszKernel c w • f) c R = f w
参数：Metric.closedBall c R；Complex.re ∘ herglotzRieszKernel c w • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `IsCompact.exists_thickening_subset_open`：∀ {α : Type u} [inst : PseudoEM
etricSpace α] {s t : Set α},   IsCompact s → IsOpen t → s ⊆ t → ∃ δ, 0 < δ ∧ Met
ric.thickening δ s ⊆ t
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `InnerProductSpace.isOpen_setOfPred_harmonicAt`：isOpen_setOfPred_harmonic
At : IsOpen { x : E | HarmonicAt f x }
· 使用定理 `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`：InnerPr
oductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : Complex} {R : Real
} (hf : HarmonicOnNhd f (ball z R)) : exists F : Comp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickening_closedBall`：thickening_closedBall (hε : 0 < ε) (hδ : 0 <= δ) 
(x : E) : thickening ε (closedBall x δ) = ball x (ε + δ)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.pos_of_mem_ball`：pos_of_mem_ball (hy : y in ball x ε) : 0 < ε
· 使用定理 `AnalyticAt.differentiableWithinAt`：AnalyticAt.differentiableWithinAt (h 
: AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `herglotzRieszKernel_def`：herglotzRieszKernel_def (c w z : Complex) : her
glotzRieszKernel c w z = ((z - c) + (w - c)) / ((z - c) - (w - c))
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用引理 `Metric.sphere_subset_ball`：sphere_subset_ball {r R : Real} (h : r < R) :
 sphere x r subseteq ball x R
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
**Poisson integral formula** for harmonic functions on arbitrary disks in the co
mplex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
theorem HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt f) (by aesop)
  rw [thickening_closedBall h₁e (pos_of_mem_ball hw).le] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c R)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (re ∘ herglotzRieszKernel c w • f)
      (reCLM ∘ (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z))
      (sphere c R) := by
    intro x hx
    simp [h₂F (sphere_subset_ball (lt_add_of_pos_left R h₁e) hx), herglotzRieszKernel_def]
  rw [← abs_of_pos (pos_of_mem_ball hw)] at h₄F
  rw [circleAverage_congr_sphere h₄F, reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage_re_herglotzRieszKernel_smul' hw]
  · apply h₂F
    grind [mem_ball]
  -- CircleIntegrable (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z) c R
  apply (ContinuousOn.fun_smul _ _).circleIntegrable'
  · apply (continuousOn_herglotz_riesz hw).mono
    grind [mem_ball, dist_eq_norm, mem_sphere_iff_norm, (pos_of_mem_ball hw)]
  · apply (h₁F.mono _).continuousOn (𝕜 := ℂ)
    grind [mem_sphere, mem_ball, (pos_of_mem_ball hw)]

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
/-
**InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul**
 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace.HarmonicContOnCl`。
形式化陈述：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicContOnCl f (M
etric.ball c R) →     w ∈ Metric.ball c R → Real.circleAverage (Complex.re ∘ her
glotzRieszKernel c w • f) c R = f w
参数：Metric.ball c R；Complex.re ∘ herglotzRieszKernel c w • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Real.ContinuousOn.eq_of_eqOn_Ioo`：∀ {f : ℝ → ℝ} {c r R : ℝ}, ContinuousO
n f (Set.Ioc r R) → r < R → Set.EqOn f (fun x => c) (Set.Ioo r R) → f R = c
· 使用定理 `Real.ContinuousOn.circleAverage`：∀ {E : Type u_1} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {f : ℂ → E} {s : Set ℝ} {c : ℂ},   Continuous
On f {z | ‖z - c‖ ∈ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `herglotzRieszKernel_fun_def`：herglotzRieszKernel_fun_def (c w : Complex)
 : herglotzRieszKernel c w = fun z => ((z - c) + (w - c)) / ((z - c) - (w - c))
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `_private.Mathlib.Analysis.Complex.Harmonic.Poisson.0.InnerProductSpace.c
ontinuousOn_herglotz_riesz`：∀ {c w : ℂ} {R : ℝ},   w ∈ Metric.ball c R →     Con
tinuousOn (fun x => ((x - c + (w - c)) / (x - c - (w - c))).re) {z | ‖z - c‖ ∈ S
et.Ioc ‖…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smu
l`：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicOnNhd f (Metric.
closedBall c R) →     w ∈ Metric.ball c R → Real.circleAverage …
· 使用定理 `InnerProductSpace.HarmonicOnNhd.mono`：∀ {E : Type u_1} [inst : NormedAdd
CommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]  
 {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Poisson integral formula** for harmonic functions on arbitrary disks in the co
mplex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
theorem HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · apply ContinuousOn.circleAverage
    · rw [herglotzRieszKernel_fun_def]
      apply (continuousOn_herglotz_riesz hw).smul (hf.2.mono _)
      grind [closure_ball c (pos_of_mem_ball hw).ne', mem_closedBall_iff_norm]
    · grind [norm_nonneg (w - c)]
  · grind [mem_ball_iff_norm]
  · intro r hr
    rw [HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
      (hf.1.mono (closedBall_subset_ball hr.2)) (by grind [mem_ball_iff_norm])]

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the Poisson kernel of integration.
-/
/-
**InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul** 是 Mathlib 中
的一个定理，位于命名空间 `InnerProductSpace.HarmonicOnNhd`。
形式化陈述：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicOnNhd f (Metr
ic.closedBall c R) →     w ∈ Metric.ball c R → Real.circleAverage (poissonKernel
 c w • f) c R = f w
参数：Metric.closedBall c R；poissonKernel c w • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smu
l`：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicOnNhd f (Metric.
closedBall c R) →     w ∈ Metric.ball c R → Real.circleAverage …
· 使用定理 `Real.circleAverage_congr_sphere`：circleAverage_congr_sphere {f₁ f₂ : Com
plex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleA
verage f₂ c R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Poisson integral formula** for harmonic functions on arbitrary disks in the co
mplex plane,
formulated with the Poisson kernel of integration.
-/
theorem HarmonicOnNhd.circleAverage_poissonKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ ↦ by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the Poisson kernel of integration.
-/
/-
**InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul** 是 Mathli
b 中的一个定理，位于命名空间 `InnerProductSpace.HarmonicContOnCl`。
形式化陈述：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicContOnCl f (M
etric.ball c R) →     w ∈ Metric.ball c R → Real.circleAverage (poissonKernel c 
w • f) c R = f w
参数：Metric.ball c R；poissonKernel c w • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_
smul`：∀ {f : ℂ → ℝ} {c w : ℂ} {R : ℝ},   InnerProductSpace.HarmonicContOnCl f (M
etric.ball c R) →     w ∈ Metric.ball c R → Real.circleAverage (Co…
· 使用定理 `Real.circleAverage_congr_sphere`：circleAverage_congr_sphere {f₁ f₂ : Com
plex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleA
verage f₂ c R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Poisson integral formula** for harmonic functions on arbitrary disks in the co
mplex plane,
formulated with the Poisson kernel of integration.
-/
theorem HarmonicContOnCl.circleAverage_poissonKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ ↦ by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

end InnerProductSpace

