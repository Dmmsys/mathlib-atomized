/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Yi Yuan
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl

/-!
# The Mean Value Property of Vector-Valued Harmonic Functions

This file establishes the mean value property for harmonic functions `f : ℂ → F`, where `F` is an
arbitrary complete real normed vector space. This generalizes the mean value property for
real-valued harmonic functions.

Completeness of `F` cannot be dropped: `circleAverage` is defined in terms of the Bochner integral,
which is junk (zero) whenever the target space is incomplete.

The proof reduces to the real-valued case. Circle averages commute with continuous linear maps, and
composition with continuous linear maps preserves harmonicity. Thus, `g (circleAverage f c R)`
equals `circleAverage (g ∘ f) c R = g (f c)` for every continuous linear functional `g : F →L[ℝ] ℝ`.
Since continuous linear functionals separate the points of a normed space (Hahn-Banach, in the form
of `SeparatingDual.eq_iff_forall_dual_eq`), this suffices.
-/

public section

open InnerProductSpace Metric Real

namespace InnerProductSpace

/-!
## Compatibility of `HarmonicContOnCl` with Linear Maps
-/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/--
Compositions of continuous ℝ-linear maps with functions that are harmonic on a set and continuous
on its closure are again harmonic on the set and continuous on its closure.
-/
/-
**InnerProductSpace.HarmonicContOnCl.comp_CLM** 是 Mathlib 中的一个定理，位于命名空间 `InnerPr
oductSpace.HarmonicContOnCl`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : FiniteDimensional ℝ E]   {F : Type u_2} [inst_3 : NormedAddCommG
roup F] [inst_4 : NormedSpace ℝ F] {G : Type u_3}   [inst_5 : NormedAddCommGroup
 G] [inst_6 : NormedSpace ℝ G] {f : E → F} {s : Set E},   InnerProductSpace.Harm
onicContOnCl f s → ∀ (l : F →L[ℝ] G), InnerProductSpace.HarmonicContOnCl (⇑l ∘ f
) s
参数：l : F →L[ℝ] G；⇑l ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.comp_CLM`：∀ {E : Type u_1} [inst : Norme
dAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ 
E]   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.harmonicOnNhd`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimens
ional ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …

--- 原说明 ---
Compositions of continuous ℝ-linear maps with functions that are harmonic on a s
et and continuous
on its closure are again harmonic on the set and continuous on its closure.
-/
theorem HarmonicContOnCl.comp_CLM {f : E → F} {s : Set E} (h : HarmonicContOnCl f s)
    (l : F →L[ℝ] G) : HarmonicContOnCl (l ∘ f) s :=
  ⟨h.1.comp_CLM l, l.continuous.comp_continuousOn h.2⟩

end

/-!
## The Mean Value Property
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {f : ℂ → F} {c : ℂ} {R : ℝ}

/--
The Mean Value Property of harmonic functions: If f : ℂ → F is harmonic in a neighborhood of a
closed disc of radius R and center c, then the circle average circleAverage f c R equals
f c.
-/
/-
**InnerProductSpace.HarmonicOnNhd.circleAverage_eq** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductSpace.HarmonicOnNhd`。
形式化陈述：∀ {F : Type u_1} [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] 
[CompleteSpace F] {f : ℂ → F} {c : ℂ} {R : ℝ},   InnerProductSpace.HarmonicOnNhd
 f (Metric.closedBall c |R|) → Real.circleAverage f c R = f c
参数：Metric.closedBall c |R|。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `ContinuousOn.circleIntegrable'`：ContinuousOn.circleIntegrable' {f : Comp
lex -> E} {c : Complex} {R : Real} (hf : ContinuousOn f (sphere c |R|)) : Circle
Integrable f c R
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `InnerProductSpace.HarmonicOnNhd.continuousOn`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensiona
l ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparatingDual.eq_iff_forall_dual_eq`：eq_iff_forall_dual_eq {x y : V} : 
x = y ↔ forall g : StrongDual R V, g x = g y
· 使用定理 `instSeparatingDualRealOfIsTopologicalAddGroupOfContinuousSMulOfLocallyCo
nvexSpaceOfT1Space`：∀ {E : Type u_1} [inst : TopologicalSpace E] [inst_1 : AddCo
mmGroup E] [IsTopologicalAddGroup E]   [inst_3 : _root_.Module ℝ E] [ContinuousS
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.circleAverage_comp_comm`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {F : Type u_2} [inst_2 : NormedAd
dCommGroup F]   [inst_3 : NormedS…
· 使用定理 `IsCompact.exists_thickening_subset_open`：∀ {α : Type u} [inst : PseudoEM
etricSpace α] {s t : Set α},   IsCompact s → IsOpen t → s ⊆ t → ∃ δ, 0 < δ ∧ Met
ric.thickening δ s ⊆ t
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `InnerProductSpace.isOpen_setOfPred_harmonicAt`：isOpen_setOfPred_harmonic
At : IsOpen { x : E | HarmonicAt f x }
· 使用定理 `InnerProductSpace.HarmonicOnNhd.comp_CLM`：∀ {E : Type u_1} [inst : Norme
dAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ 
E]   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`：InnerPr
oductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : Complex} {R : Real
} (hf : HarmonicOnNhd f (ball z R)) : exists F : Comp…
· 使用定理 `thickening_closedBall`：thickening_closedBall (hε : 0 < ε) (hδ : 0 <= δ) 
(x : E) : thickening ε (closedBall x δ) = ball x (ε + δ)
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `AnalyticAt.differentiableWithinAt`：AnalyticAt.differentiableWithinAt (h 
: AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `Metric.sphere_subset_ball`：sphere_subset_ball {r R : Real} (h : r < R) :
 sphere x r subseteq ball x R
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The Mean Value Property of harmonic functions: If f : ℂ → F is harmonic in a nei
ghborhood of a
closed disc of radius R and center c, then the circle average circleAverage f c 
R equals
f c.
-/
theorem HarmonicOnNhd.circleAverage_eq (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt (g ∘ f)) (hf.comp_CLM g)
  rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c |R|)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (Complex.reCLM ∘ F) (⇑g ∘ f) (sphere c |R|) :=
    fun x hx ↦ h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
  rw [← circleAverage_congr_sphere h₄F, Complex.reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage]
  · apply h₂F
    simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
  · apply (h₁F.continuousOn.mono (fun _ _ ↦ by simp_all [dist_eq_norm])).circleIntegrable'

/--
The Mean Value Property of harmonic functions: If f : ℂ → F is harmonic on a disc of radius
|R| and center c and continuous on its closure, then the circle average circleAverage f c R
equals f c.
-/
/-
**InnerProductSpace.HarmonicContOnCl.circleAverage_eq** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductSpace.HarmonicContOnCl`。
形式化陈述：∀ {F : Type u_1} [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] 
[CompleteSpace F] {f : ℂ → F} {c : ℂ} {R : ℝ},   InnerProductSpace.HarmonicContO
nCl f (Metric.ball c |R|) → Real.circleAverage f c R = f c
参数：Metric.ball c |R|。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `ContinuousOn.circleIntegrable'`：ContinuousOn.circleIntegrable' {f : Comp
lex -> E} {c : Complex} {R : Real} (hf : ContinuousOn f (sphere c |R|)) : Circle
Integrable f c R
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn_ball`：continuousOn_ball 
{x : E} {r : Real} (h : HarmonicContOnCl f (ball x r)) : ContinuousOn f (closedB
all x r)
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparatingDual.eq_iff_forall_dual_eq`：eq_iff_forall_dual_eq {x y : V} : 
x = y ↔ forall g : StrongDual R V, g x = g y
· 使用定理 `instSeparatingDualRealOfIsTopologicalAddGroupOfContinuousSMulOfLocallyCo
nvexSpaceOfT1Space`：∀ {E : Type u_1} [inst : TopologicalSpace E] [inst_1 : AddCo
mmGroup E] [IsTopologicalAddGroup E]   [inst_3 : _root_.Module ℝ E] [ContinuousS
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.circleAverage_comp_comm`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {F : Type u_2} [inst_2 : NormedAd
dCommGroup F]   [inst_3 : NormedS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.circleAverage_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleA
verage f c 0 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.ContinuousOn.circleAverage`：∀ {E : Type u_1} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {f : ℂ → E} {s : Set ℝ} {c : ℂ},   Continuous
On f {z | ‖z - c‖ ∈ s…
· 使用定理 `InnerProductSpace.HarmonicContOnCl.continuousOn`：∀ {E : Type u_1} [inst 
: NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensi
onal ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `InnerProductSpace.HarmonicContOnCl.comp_CLM`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional
 ℝ E]   {F : Type u_2} [inst_3 : …
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mem_closedBall_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup
 E] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r ↔ ‖b - a‖ ≤ r
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The Mean Value Property of harmonic functions: If f : ℂ → F is harmonic on a dis
c of radius
|R| and center c and continuous on its closure, then the circle average circleAv
erage f c R
equals f c.
-/
theorem HarmonicContOnCl.circleAverage_eq (hf : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  by_cases hR : R = 0
  · simp_all
  have H : ContinuousOn (circleAverage (g ∘ f) c) (Set.Ioc 0 |R|) := by
    refine ((hf.comp_CLM g).2.mono ?_).circleAverage (fun z hz ↦ hz.1.le)
    intro x hx
    rw [closure_ball _ (by aesop), mem_closedBall_iff_norm]
    exact hx.2
  rw [← circleAverage_abs_radius]
  apply H.eq_of_eqOn_Ioo (by aesop)
  intro r hr
  apply HarmonicOnNhd.circleAverage_eq
  apply (hf.comp_CLM g).1.mono
  rw [abs_of_pos hr.1]
  exact closedBall_subset_ball hr.2

end InnerProductSpace

@[deprecated InnerProductSpace.HarmonicOnNhd.circleAverage_eq (since := "2026-08-04")]
alias HarmonicOnNhd.circleAverage_eq := InnerProductSpace.HarmonicOnNhd.circleAverage_eq

@[deprecated InnerProductSpace.HarmonicContOnCl.circleAverage_eq (since := "2026-08-04")]
alias HarmonicContOnCl.circleAverage_eq := InnerProductSpace.HarmonicContOnCl.circleAverage_eq

