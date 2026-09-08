/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.Homotopy.Affine

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Poincaré lemma for 1-forms

In this file we prove Poincaré lemma for 1-forms for convex sets.
Namely, we show that a closed 1-form on a convex subset of a normed space is exact.

We also prove that the integrals of a closed 1-form
along 2 curves that are joined by a `C²`-smooth homotopy are equal.
In the future, this will allow us to prove Poincaré lemma for simply connected open sets
and, more generally, for simply connected locally convex sets.

## Implementation notes

In this file, we represent a 1-form as `ω : E → E →L[𝕜] F`, where `𝕜` is `ℝ` or `ℂ`,
not as `ω : E → E [⋀^Fin 1]→L[𝕜] F`.
A 1-form represented this way is closed
iff its Fréchet derivative `dω : E → E →L[𝕜] E →L[𝕜] F` is symmetric, `dω a x y = dω a y x`.
-/

public section

open scoped unitInterval Interval Pointwise Topology
open AffineMap Filter Function MeasureTheory Set

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousMap.Homotopy

variable [NormedSpace ℝ E] [NormedSpace ℝ F] {a b c d : E}
    {γ₁ : Path a b} {γ₂ : Path c d} {s : Set (I × I)} {t : Set E}

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
_off_countable_real** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))) (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  -- The overall plan of the proof is to pullback the 1-form to the unit square along the homotopy,
  -- prove that it's a closed 1-form, then apply the divergence theorem.
  -- Let `U` be the interior of the unit square
  -- Warning: throughout the proof, we sometimes have `0` or `1` in product spaces,
  -- not only in `I` or `ℝ`, so, e.g., `Icc 0 1` may refer to the unit square
  -- in `ℝ × ℝ`.
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hinterior : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq]
    simp [Prod.mk_zero_zero, Prod.mk_one_one]
  have hunique : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hU_subset : U ⊆ Icc 0 1 := hinterior ▸ interior_subset
  have hclosure : closure U = Icc 0 1 := by
    simp [hU, closure_prod_eq, Prod.mk_zero_zero, Prod.mk_one_one]
  -- Extend the homotopy `φ` to a continuous map  `ψ : ℝ × ℝ → E`
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2 with hψ
  have hψφ : ∀ a b : I, ψ (a, b) = φ (a, b) := by simp [ψ]
  have hψ_cont : Continuous ψ := by fun_prop
  have hψUt : MapsTo ψ U t := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    lift a to I using Ioo_subset_Icc_self ha
    lift b to I using Ioo_subset_Icc_self hb
    simpa [hψφ] using hφt a ha b hb
  -- Let `dψ` be its derivative.
  set dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fderivWithin ℝ ψ (Icc 0 1)
  -- Let `s'` be the set `s` interpreted as a set in `ℝ × ℝ`
  set s' : Set (ℝ × ℝ) := Prod.map (↑) (↑) '' s with hs'
  have hmem_s' (x y : I) : (↑x, ↑y) ∈ s' ↔ (x, y) ∈ s := by
    rw [hs', ← Prod.map_apply, Injective.mem_set_image]
    apply Injective.prodMap <;> apply Subtype.val_injective
  have hs'c : s'.Countable := hs.image _
  have hdψ : ∀ a ∈ U, HasFDerivAt ψ (dψ a) a := by
    rintro a haU
    refine hcontdiff.differentiableOn (by decide) a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Let `d2ψ` be its second derivative
  set d2ψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] E := fderivWithin ℝ dψ (Icc 0 1)
  have hd2ψ : ∀ a ∈ U, HasFDerivAt dψ (d2ψ a) a := by
    rintro a haU
    refine hcontdiff.fderivWithin hunique (by decide) |>.differentiableOn_one a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Note that `d2ψ` is symmetric
  have hd2ψ_symm : ∀ a ∈ Icc 0 1, ∀ x y, d2ψ a x y = d2ψ a y x := by
    intro a ha
    exact (hcontdiff a ha).isSymmSndFDerivWithinAt (by simp) hunique
      (by simp [hinterior, hclosure, ha]) ha
  -- Consider `η a = ω (ψ a) ∘L dψ a`.
  set η : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ω (ψ a) ∘L dψ a
  -- Put `f a = η a (0, 1)`, `g a = -η a (1, 0)`.
  set f : ℝ × ℝ → F := fun a ↦ η a (0, 1)
  have hf : ∀ a ∈ Icc 0 1, f a = ω (ψ a) (derivWithin (ψ ∘ (a.1, ·)) I a.2) := by
    intro a ha
    simp only [f, η, dψ, ContinuousLinearMap.comp_apply]
    congr 1
    have : HasDerivWithinAt (a.1, ·) (0, 1) I a.2 :=
      .prodMk (hasDerivWithinAt_const ..) (hasDerivWithinAt_id ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ha.1.1, ht.1⟩, ⟨ha.2.1, ht.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.2, ha.2.2⟩
  set g : ℝ × ℝ → F := fun a ↦ -η a (1, 0)
  have hg : ∀ a ∈ Icc 0 1, g a = ω (ψ a) (-derivWithin (ψ ∘ (·, a.2)) I a.1) := by
    intro a ha
    simp only [g, η, dψ, ContinuousLinearMap.comp_apply, map_neg]
    congr 2
    have : HasDerivWithinAt (·, a.2) (1, 0) I a.1 :=
      .prodMk (hasDerivWithinAt_id ..) (hasDerivWithinAt_const ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ht.1, ha.1.2⟩, ⟨ht.2, ha.2.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.1, ha.2.1⟩
  -- Then our goal is to prove that the integral of `η`
  -- along the boundary of the unit square is zero.
  suffices (((∫ x in 0..1, g (x, 1)) - ∫ x in 0..1, g (x, 0)) +
      ∫ y in 0..1, f (1, y)) - ∫ y in 0..1, f (0, y) = 0 by
    have hfi (s : I) :
        ∫ t in 0..1, f (s, t) = ∫ᶜ x in ⟨φ.curry s, rfl, rfl⟩, ω x := by
      simp only [curveIntegral_def, curveIntegralFun_def]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro t ht
      simp [Path.extend, hf (s, t), Prod.le_def, s.2.1, s.2.2, ht.1, ht.2, Function.comp_def, hψ]
    have hf₀ : ∫ t in 0..1, f (0, t) = ∫ᶜ x in γ₁, ω x := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 0
    have hf₁ : ∫ t in 0..1, f (1, t) = curveIntegral ω γ₂ := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 1
    have hgi (t : I) : ∫ᶜ x in φ.evalAt t, ω x = -∫ s in 0..1, g (s, t) := by
      simp only [curveIntegral_def, curveIntegralFun_def, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro s hs
      simp only [hs, Path.extend_apply, φ.evalAt_apply]
      simp [hg (s, t), Prod.le_def, hs.1, hs.2, t.2.1, t.2.2, Function.comp_def, hψ]
    rw [← hf₀, ← hf₁, hgi, hgi]
    linear_combination (norm := {dsimp; abel}) -this
  -- Write a formula for the derivative of `η`.
  set dη : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] F := fun a ↦
    .compL ℝ (ℝ × ℝ) E F (ω (ψ a)) ∘L d2ψ a + (dω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hdη : ∀ a ∈ U \ s', HasFDerivAt η (dη a) a := by
    rintro a ⟨haU, has⟩
    refine HasFDerivWithinAt.comp_hasFDerivAt (t := t) a ?_ ?_ ?_ |>.clm_comp (hd2ψ a haU)
    · rcases a with ⟨x, y⟩
      lift x to I using Ioo_subset_Icc_self haU.1
      lift y to I using Ioo_subset_Icc_self haU.2
      apply hω
      · simpa using haU.1
      · simpa using haU.2
      · simpa [hmem_s'] using has
    · exact hdψ a haU
    · filter_upwards [hUopen.mem_nhds haU] using hψUt
  have hdη_symm : ∀ a ∈ U \ s', ∀ u v, dη a u v = dη a v u := by
    rintro ⟨a, b⟩ ⟨hU, hs'⟩ u v
    lift a to I using Ioo_subset_Icc_self hU.1
    lift b to I using Ioo_subset_Icc_self hU.2
    have hdψ_mem (u) : dψ (a, b) u ∈ tangentConeAt ℝ t (φ (a, b)) := by
      refine tangentConeAt_mono hψUt.image_subset ?_
      rw [← hψφ]
      refine (hdψ _ hU).hasFDerivWithinAt.mapsTo_tangent_cone ?_
      simp [tangentConeAt_of_mem_nhds (hUopen.mem_nhds hU)]
    have := hdω_symm a hU.1 b hU.2 (by simpa [hmem_s'] using hs') _ (hdψ_mem u) _ (hdψ_mem v)
    simp [dη, hψφ, this, hd2ψ_symm _ (hU_subset hU)]
  -- It gives formulas for the derivatives of `f` and `g`
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  have hf' : ∀ a ∈ U \ s', HasFDerivAt f (f' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a (hdη a ha)
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)
  have hg' : ∀ a ∈ U \ s', HasFDerivAt g (g' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp a (hdη a ha) |>.neg
  -- Note that the divergence of `(f, g)` is a.e. zero.
  have hf'g' : (fun a ↦ f' a (1, 0) + g' a (0, 1)) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    rw [Icc_prod_eq, Measure.volume_eq_prod,
      Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo), hs'c.ae_notMem _]
      with a hU hs
    simp [f', g', hdη_symm a ⟨hU, hs⟩ (0, 1)]
  suffices ∫ a : ℝ × ℝ in Icc 0 1, f' a (1, 0) + g' a (0, 1) = 0 by
    have hηc : ContinuousOn η (Icc 0 1) := by
      refine .clm_comp (hωc.comp hψ_cont.continuousOn ?_) ?_
      · rw [← hclosure]
        refine MapsTo.closure (fun a ha ↦ ?_) hψ_cont
        lift a to I × I using ⟨Ioo_subset_Icc_self ha.1, Ioo_subset_Icc_self ha.2⟩
        simpa [ψ] using hφt a.1 ha.1 a.2 ha.2
      · exact hcontdiff.continuousOn_fderivWithin hunique (by decide)
    rwa [integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le] at this
    · exact zero_le_one
    · exact s'
    · exact hs'c
    · fun_prop
    · fun_prop
    · exact hf'
    · exact hg'
    · rw [integrableOn_congr_fun_ae hf'g']
      apply integrableOn_zero
  simp [integral_congr_ae hf'g']

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero. We may ignore the behavior on a countable set.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
/-
**ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
_off_countable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopy`。
形式化陈述：curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable {ω :
 E -> E ->L[𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotop
y γ₂) (hs : s.Countable) (hφt : forall a in Ioo 0 1, forall b in Ioo 0 1, φ (a, 
b) in t) (hω : forall a in Ioo (0 : I) 1, forall b in Ioo (0 : I) 1, (a, b) ∉ s 
-> HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))) (hωc : ContinuousOn ω (clo
sure t)) (hdω_symm : forall a in Ioo (0 : I) 1, forall b in Ioo (0 : I) 1, (a, b
) ∉ s -> forall u in tange
参数：φ : (γ₁ : C(I, E)).Homotopy γ₂；hs : s.Countable；hφt : forall a in Ioo 0 1, fo
rall b in Ioo 0 1, φ (a, b) in t；hω : forall a in Ioo (0 : I) 1, forall b in Ioo
 (0 : I) 1, (a, b) ∉ s -> HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))；hωc 
: ContinuousOn ω (closure t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `curveIntegral_restrictScalars`：curveIntegral_restrictScalars : ∫ᶜ x in γ
, (ω x).restrictScalars 𝕝 = ∫ᶜ x in γ, ω x
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare.0.Continu
ousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_coun
table_real`：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_
1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ E]   [inst_3 : NormedS…
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…

--- 原说明 ---
The curve integral of a closed 1-form along the boundary of the image of a unit 
square
under a smooth map is zero. We may ignore the behavior on a countable set.

This theorem is stated in terms of a `C^2` homotopy between two paths.
-/
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b)))
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  simp only [← curveIntegral_restrictScalars (𝕜 := 𝕜) (𝕝 := ℝ)]
  set e := ContinuousLinearMap.restrictScalarsL 𝕜 E F ℝ ℝ
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real hs hφt
    (dω := fun x ↦ e ∘L dω x)
    (fun a ha b hb hs ↦ e.hasFDerivAt.comp_hasFDerivWithinAt _ (hω a ha b hb hs))
    (e.continuous.comp_continuousOn hωc) hdω_symm hcontdiff

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
/-
**ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopy`。
形式化陈述：curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt {ω : E -> E ->L[𝕜]
 F} {dω : E -> E ->L[Real] E ->L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotopy γ₂) (hφt : f
orall a in Ioo 0 1, forall b in Ioo 0 1, φ (a, b) in t) (hω : forall x in t, Has
FDerivWithinAt ω (dω x) t x) (hωc : ContinuousOn ω (closure t)) (hdω_symm : fora
ll x in t, forall u in tangentConeAt Real t x, forall v in tangentConeAt Real t 
x, dω x u v = dω x v u) (hcontdiff : ContDiffOn Real 2 (fun xy : Real × Real => 
Set.IccExtend zero_le_one 
参数：φ : (γ₁ : C(I, E)).Homotopy γ₂；hφt : forall a in Ioo 0 1, forall b in Ioo 0 1
, φ (a, b) in t；hω : forall x in t, HasFDerivWithinAt ω (dω x) t x；hωc : Continu
ousOn ω (closure t)；hdω_symm : forall x in t, forall u in tangentConeAt Real t x
, forall v in tangentConeAt Real t x, dω x u v = dω x v u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWi
thinAt_off_countable`：curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_of
f_countable {ω : E -> E ->L[𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F} (φ : (γ₁ : 
C(…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The curve integral of a closed 1-form along the boundary of the image of a unit 
square
under a smooth map is zero.

This theorem is stated in terms of a `C^2` homotopy between two paths.
-/
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x, dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable (s := ∅) (by simp)
    hφt (fun a ha b hb _ ↦ hω _ <| hφt a ha b hb) hωc
    (fun a ha b hb _ ↦ hdω_symm _ <| hφt a ha b hb) hcontdiff

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero, a version stated in terms of `DiffContOnC1`.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
/-
**ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl** 是 
Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopy`。
形式化陈述：curveIntegral_add_curveIntegral_eq_of_diffContOnCl {ω : E -> E ->L[𝕜] F} (
φ : (γ₁ : C(I, E)).Homotopy γ₂) (hφt : forall a in Ioo 0 1, forall b in Ioo 0 1,
 φ (a, b) in t) (hω : DiffContOnCl Real ω t) (hdω_symm : forall x in t, forall u
 in tangentConeAt Real t x, forall v in tangentConeAt Real t x, fderivWithin Rea
l ω t x u v = fderivWithin Real ω t x v u) (hcontdiff : ContDiffOn Real 2 (fun x
y : Real × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) : 
∫ᶜ x in γ₁, ω x + ∫ᶜ x in 
参数：φ : (γ₁ : C(I, E)).Homotopy γ₂；hφt : forall a in Ioo 0 1, forall b in Ioo 0 1
, φ (a, b) in t；hω : DiffContOnCl Real ω t；hdω_symm : forall x in t, forall u in
 tangentConeAt Real t x, forall v in tangentConeAt Real t x, fderivWithin Real ω
 t x u v = fderivWithin Real ω t x v u；hcontdiff : ContDiffOn Real 2 (fun xy : R
eal × Real => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWi
thinAt`：curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt {ω : E -> E ->L[
𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotop…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…

--- 原说明 ---
The curve integral of a closed 1-form along the boundary of the image of a unit 
square
under a smooth map is zero, a version stated in terms of `DiffContOnC1`.

This theorem is stated in terms of a `C^2` homotopy between two paths.
-/
theorem curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    {ω : E → E →L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    hφt (fun t ht ↦ (hω.differentiableOn t ht).hasFDerivWithinAt) hω.continuousOn
    hdω_symm hcontdiff

end ContinuousMap.Homotopy

namespace Convex

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
  {a b c : E} {s : Set E} {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `ω` is a closed `1`-form on a convex set,
then `∫ᶜ x in Path.segment a b, ω x + ∫ᶜ x in Path.segment b c, ω x = ∫ᶜ x in Path.segment a c, ω x`
for all `a b c ∈ s`.

This is the key lemma used to establish that closed a `1`-form on  a convex set
has a primitive.
-/
/-
**Convex.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric** 是 Mathlib
 中的一个定理，位于命名空间 `Convex`。
形式化陈述：curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric (hs : Convex R
eal s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x) (hdω : forall a in s
, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real s a, dω a x
 y = dω a y x) (ha : a in s) (hb : b in s) (hc : c in s) : (∫ᶜ x in .segment a b
, ω x) + ∫ᶜ x in .segment b c, ω x = ∫ᶜ x in .segment a c, ω x
参数：hs : Convex Real s；hω : forall x in s, HasFDerivWithinAt ω (dω x) s x；hdω : f
orall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real
 s a, dω a x y = dω a y x；ha : a in s；hb : b in s；hc : c in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Convex.lineMap_mem`：Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : 
x in s) (hy : y in s) {t : 𝕜} (ht : t in Icc 0 1) : AffineMap.lineMap x y t in s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWi
thinAt`：curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt {ω : E -> E ->L[
𝕜] F} {dω : E -> E ->L[Real] E ->L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotop…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousMap.HomotopyLike.toContinuousMapClass`：∀ {X : outParam (Type u
_3)} {Y : outParam (Type u_4)} {inst : TopologicalSpace X} {inst_1 : Topological
Space Y}   {F : Type u_5} {f₀ f₁ : ou…
· 使用定理 `ContinuousMap.Homotopy.instHomotopyLike`：∀ {X : Type u} {Y : Type v} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)},   Cont
inuousMap.HomotopyLike (f₀.Ho…
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `ω` is a closed `1`-form on a convex set,
then `∫ᶜ x in Path.segment a b, ω x + ∫ᶜ x in Path.segment b c, ω x = ∫ᶜ x in Pa
th.segment a c, ω x`
for all `a b c ∈ s`.

This is the key lemma used to establish that closed a `1`-form on  a convex set
has a primitive.
-/
theorem curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric (hs : Convex ℝ s)
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    (∫ᶜ x in .segment a b, ω x) + ∫ᶜ x in .segment b c, ω x = ∫ᶜ x in .segment a c, ω x := by
  set φ := ContinuousMap.Homotopy.affine (Path.segment a b : C(I, E)) (Path.segment a c)
  have hφs : range φ ⊆ s := by
    rw [range_subset_iff]
    intro x
    simp [φ, ha, hb, hc, hs.lineMap_mem]
  have := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := range φ) (ω := ω)
    (dω := dω) ?_ ?_ ?_ ?_ ?_
  · convert! this using 2
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_one a b) (lineMap_apply_one a c), curveIntegral_cast]
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_zero a b) (lineMap_apply_zero a c)]
      simp
  · intros
    apply mem_range_self
  · exact fun x hx ↦ (hω x (hφs hx)).mono hφs
  · rw [(isCompact_range <| map_continuous _).isClosed.closure_eq]
    exact fun x hx ↦ (hω x <| hφs hx).continuousWithinAt.mono hφs
  · intro x hx u hu v hv
    apply hdω <;> grw [← hφs] <;> assumption
  · have : EqOn (fun x : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend x.1) x.2)
        (fun x ↦ lineMap (lineMap a b x.2) (lineMap a c x.2) x.1) (Icc 0 1) := by
      rw [Icc_prod_eq]
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to I using hx
      lift y to I using hy
      simp [φ]
    exact .congr (by fun_prop) this

variable [CompleteSpace F]

/-- If `ω` is a closed `1`-form on a convex set `s`,
then the function given by `F b = ∫ᶜ x in Path.segment a b, ω x` is a primitive of `ω` on `s`,
i.e., `dF = ω`.
-/
/-
**Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric*
* 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric (hs
 : Convex Real s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x) (hdω : fo
rall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real 
s a, dω a x y = dω a y x) (ha : a in s) (hb : b in s) : HasFDerivWithinAt (∫ᶜ x 
in .segment a ·, ω x) (ω b) s b
参数：hs : Convex Real s；hω : forall x in s, HasFDerivWithinAt ω (dω x) s x；hdω : f
orall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real
 s a, dω a x y = dω a y x；ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type u_…
· 使用定理 `HasFDerivWithinAt.curveIntegral_segment_source`：HasFDerivWithinAt.curveI
ntegral_segment_source (hs : Convex Real s) (hω : ContinuousOn ω s) (ha : a in s
) : HasFDerivWithinAt (∫ᶜ x in .segm…
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `HasFDerivWithinAt.congr'`：HasFDerivWithinAt.congr' (h : HasFDerivWithinA
t f f' s x) (hs : EqOn f₁ f s) (hx : x in s) : HasFDerivWithinAt f₁ f' s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric`：curv
eIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric (hs : Convex Real s) (hω
 : forall x in s, HasFDerivWithinAt ω (dω x) s x) (hdω :…

--- 原说明 ---
If `ω` is a closed `1`-form on a convex set `s`,
then the function given by `F b = ∫ᶜ x in Path.segment a b, ω x` is a primitive 
of `ω` on `s`,
i.e., `dF = ω`.
-/
theorem hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric (hs : Convex ℝ s)
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) :
    HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω b) s b := by
  suffices HasFDerivWithinAt (∫ᶜ x in .segment a b, ω x + ∫ᶜ x in .segment b ·, ω x) (ω b) s b from
    this.congr' (fun _ h ↦
      (hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
  refine .const_add _ <| ?_
  refine HasFDerivWithinAt.curveIntegral_segment_source hs ?_ hb
  exact fun x hx ↦ (hω x hx).continuousWithinAt

/-- If `ω` is a closed `1`-form on a convex set `s`, then it admits a primitive,
a version stated in terms of `HasFDerivWithinAt`. -/
/-
**Convex.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric** 是 Math
lib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric (hs : Conve
x Real s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x) (hdω : forall a i
n s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real s a, dω 
a x y = dω a y x) : exists f, forall a in s, HasFDerivWithinAt f (ω a) s a
参数：hs : Convex Real s；hω : forall x in s, HasFDerivWithinAt ω (dω x) s x；hdω : f
orall a in s, forall x in tangentConeAt Real s a, forall y in tangentConeAt Real
 s a, dω a x y = dω a y x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symm
etric`：hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric (h
s : Convex Real s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) …

--- 原说明 ---
If `ω` is a closed `1`-form on a convex set `s`, then it admits a primitive,
a version stated in terms of `HasFDerivWithinAt`.
-/
theorem exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (hs : Convex ℝ s) (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (curveIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

/-- If `ω` is a closed `1`-form on a convex set `s`, then it admits a primitive,
a version stated in terms of `fderivWithin`. -/
/-
**Convex.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric** 是 Mathlib 中
的一个定理，位于命名空间 `Convex`。
形式化陈述：exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric (hs : Convex Rea
l s) (hω : DifferentiableOn Real ω s) (hdω : forall a in s, forall x in tangentC
oneAt Real s a, forall y in tangentConeAt Real s a, fderivWithin Real ω s a x y 
= fderivWithin Real ω s a y x) : exists f, forall a in s, HasFDerivWithinAt f (ω
 a) s a
参数：hs : Convex Real s；hω : DifferentiableOn Real ω s；hdω : forall a in s, forall
 x in tangentConeAt Real s a, forall y in tangentConeAt Real s a, fderivWithin R
eal ω s a x y = fderivWithin Real ω s a y x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Convex.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric`：e
xists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric (hs : Convex Real 
s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x) (hd…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x

--- 原说明 ---
If `ω` is a closed `1`-form on a convex set `s`, then it admits a primitive,
a version stated in terms of `fderivWithin`.
-/
theorem exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric
    (hs : Convex ℝ s) (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a,
      fderivWithin ℝ ω s a x y = fderivWithin ℝ ω s a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a :=
  hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha ↦ (hω a ha).hasFDerivWithinAt) hdω

/-- If `ω` is a closed `1`-form on an open convex set `s`, then it admits a primitive,
a version stated in terms of `fderiv`. -/
/-
**Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric** 是 Mathlib 中的一个定理，位于命名空间
 `Convex`。
形式化陈述：exists_forall_hasFDerivAt_of_fderiv_symmetric (hs : Convex Real s) (hso : 
IsOpen s) (hω : DifferentiableOn Real ω s) (hdω : forall a in s, forall x y, fde
riv Real ω a x y = fderiv Real ω a y x) : exists f, forall a in s, HasFDerivAt f
 (ω a) a
参数：hs : Convex Real s；hso : IsOpen s；hω : DifferentiableOn Real ω s；hdω : forall
 a in s, forall x y, fderiv Real ω a x y = fderiv Real ω a y x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Convex.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric`：exists
_forall_hasFDerivWithinAt_of_fderivWithin_symmetric (hs : Convex Real s) (hω : D
ifferentiableOn Real ω s) (hdω : forall a in s, forall…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_eq_fderiv`：fderivWithin_eq_fderiv [ContinuousAdd E] [Contin
uousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (hs : UniqueDif
fWithinAt 𝕜 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `HasFDerivWithinAt.hasFDerivAt`：HasFDerivWithinAt.hasFDerivAt (h : HasFDe
rivWithinAt f f' s x) (hs : s in 𝓝 x) : HasFDerivAt f f' x

--- 原说明 ---
If `ω` is a closed `1`-form on an open convex set `s`, then it admits a primitiv
e,
a version stated in terms of `fderiv`.
-/
theorem exists_forall_hasFDerivAt_of_fderiv_symmetric (hs : Convex ℝ s) (hso : IsOpen s)
    (hω : DifferentiableOn ℝ ω s) (hdω : ∀ a ∈ s, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivAt f (ω a) a := by
  obtain ⟨f, hf⟩ : ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ ↦ ?_
    rw [fderivWithin_eq_fderiv, hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)]
  exact ⟨f, fun a ha ↦ (hf a ha).hasFDerivAt (hso.mem_nhds ha)⟩

end Convex

namespace Convex

variable [CompleteSpace E] {f : 𝕜 → E} {s : Set 𝕜}

/-- If `f : 𝕜 → E`, `𝕜 = ℝ` or `𝕜 = ℂ`, is differentiable on a convex set `s`,
then it admits a primitive. -/
/-
**Convex.exists_forall_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：exists_forall_hasDerivWithinAt (hs : Convex Real s) (hf : DifferentiableOn
 𝕜 f s) : exists g : 𝕜 -> E, forall a in s, HasDerivWithinAt g (f a) s a
参数：hs : Convex Real s；hf : DifferentiableOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric`：e
xists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric (hs : Convex Real 
s) (hω : forall x in s, HasFDerivWithinAt ω (dω x) s x) (hd…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasFDerivAtFilter.restrictScalars`：HasFDerivAtFilter.restrictScalars {L}
 (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter f (f'.restrictScalars 𝕜) L
· 使用定理 `HasFDerivAt.comp_hasDerivWithinAt`：HasFDerivAt.comp_hasDerivWithinAt (hl
 : HasFDerivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
l ∘ f) (l' f') s x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.restrictScalars.congr_simp`：∀ {A : Type u_1} {M₁ : T
ype u_2} {M₂ : Type u_3} (R : Type u_4) [inst : Semiring A] [inst_1 : Semiring R
]   [inst_2 : AddCommMonoid M₁] [ins…
· 使用定理 `ContinuousLinearMap.toSpanSingleton.congr_simp`：∀ (R₁ : Type u_1) [inst 
: Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommM
onoid M₁]   [inst_3 : _root_.Module …
· 使用定理 `ContinuousLinearMap.smulRightL_apply_apply`：∀ (𝕜 : Type u_1) (E : Type u
_4) (Fₗ : Type u_7) [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCom
mGroup Fₗ]   [inst_2 : Nontrivia…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : 𝕜 → E`, `𝕜 = ℝ` or `𝕜 = ℂ`, is differentiable on a convex set `s`,
then it admits a primitive.
-/
theorem exists_forall_hasDerivWithinAt (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s) :
    ∃ g : 𝕜 → E, ∀ a ∈ s, HasDerivWithinAt g (f a) s a := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  apply hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  · intro a ha
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1).hasFDerivAt
      |>.comp_hasDerivWithinAt a (hf a ha).hasDerivWithinAt |>.restrictScalars ℝ
  · rintro a ha x - y -
    simpa using smul_comm ..

end Convex

