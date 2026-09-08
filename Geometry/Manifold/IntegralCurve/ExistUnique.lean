/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Geometry.Manifold.IntegralCurve.Transform
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Notation

/-!
# Existence and uniqueness of integral curves

## Main results

* `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`: Existence of local integral curves for a
  $C^1$ vector field. This follows from the existence theorem for solutions to ODEs
  (`exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt`).
* `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`: Uniqueness of local integral curves for a
  $C^1$ vector field. This follows from the uniqueness theorem for solutions to ODEs
  (`ODE_solution_unique_of_mem_set_Ioo`). This requires the manifold to be Hausdorff (`T2Space`).

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a TODO.

We state simpler versions of the theorem for boundaryless manifolds as corollaries.

## TODO

* The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
  Lee. May require submanifolds.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field, local existence, uniqueness
-/

public section

open scoped Topology

open Function Manifold Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} (t₀ : ℝ) {x₀ : M}

set_option backward.isDefEq.respectTransparency false in
/-- Existence of local integral curves for a $C^1$ vector field at interior points of a `C^1`
manifold. -/
/-
**exists_isMIntegralCurveAt_of_contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isMIntegralCurveAt_of_contMDiffAt [CompleteSpace E] (hv : CMDiffAt 
1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) (hx : I.IsInteriorPoint x₀) : ex
ists γ : Real -> M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀
参数：hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀；hx : I.IsInterio
rPoint x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDeri
vAt₀`：exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (hf : Co
ntDiffAt Real 1 f x₀) (t₀ : Real) : exists α : Real -> E, α t₀ = x…
· 使用定理 `ContDiffAt.snd`：ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).2) x
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `range_mem_nhds_isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `continuousAt_def`：continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f
 x), f ⁻¹' A in 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用引理 `ModelWithCorners.isInteriorPoint_iff`：isInteriorPoint_iff {x : M} : I.Is
InteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eventually_mem_nhds_iff`：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s
 in 𝓝 x') ↔ s in 𝓝 x
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isMIntegralCurveAt_iff`：isMIntegralCurveAt_iff : IsMIntegralCurveAt γ v 
t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Existence of local integral curves for a $C^1$ vector field at interior points o
f a `C^1`
manifold.
-/
theorem exists_isMIntegralCurveAt_of_contMDiffAt [CompleteSpace E]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀ := by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, hf2⟩ := hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)
    |>.snd.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  simp_rw [← Real.ball_eq_Ioo, ← Metric.eventually_nhds_iff_ball] at hf2
  -- use continuity of `f` so that `f t` remains inside `interior (extChartAt I x₀).target`
  have ⟨a, ha, hf2'⟩ := Metric.eventually_nhds_iff_ball.mp hf2
  have hcont := (hf2' t₀ (Metric.mem_ball_self ha)).continuousAt
  rw [continuousAt_def, hf1] at hcont
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ 𝓝 t₀ :=
    hcont _ (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx))
  rw [← eventually_mem_nhds_iff] at hnhds
  -- obtain a neighbourhood `s` so that the above conditions both hold in `s`
  obtain ⟨s, hs, haux⟩ := (hf2.and hnhds).exists_mem
  -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
  refine ⟨(extChartAt I x₀).symm ∘ f,
    Eq.symm (by rw [Function.comp_apply, hf1, PartialEquiv.left_inv _ (mem_extChartAt_source ..)]),
    isMIntegralCurveAt_iff.mpr ⟨s, hs, ?_⟩⟩
  intro t ht
  -- collect useful terms in convenient forms
  let xₜ : M := (extChartAt I x₀).symm (f t) -- `xₜ := γ t`
  have h : HasDerivAt f (x := t) <| fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ) := (haux t ht).1
  rw [← tangentCoordChange_def] at h
  have hf3 := mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  -- express the derivative of the integral curve in the local chart
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt` on `h`
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- Existence of local integral curves for a $C^1$ vector field on a `C^1` manifold without
boundary. -/
/-
**exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless [CompleteSpace E] [B
oundarylessManifold I M] (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I 
M)) x₀) : exists γ : Real -> M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀
参数：hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isMIntegralCurveAt_of_contMDiffAt`：exists_isMIntegralCurveAt_of_c
ontMDiffAt [CompleteSpace E] (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundl
e I M)) x₀) (hx : I.IsInterior…
· 使用定理 `BoundarylessManifold.isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
Existence of local integral curves for a $C^1$ vector field on a `C^1` manifold 
without
boundary.
-/
lemma exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    [CompleteSpace E] [BoundarylessManifold I M]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀ :=
  exists_isMIntegralCurveAt_of_contMDiffAt t₀ hv BoundarylessManifold.isInteriorPoint

variable {t₀}

/-- Local integral curves are unique.

If a $C^1$ vector field `v` admits two local integral curves `γ γ' : ℝ → M` at `t₀` with
`γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval containing `t₀`. -/
/-
**isMIntegralCurveAt_eventuallyEq_of_contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_eventuallyEq_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (
γ t₀)) (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀)) (hγ : 
IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀)
 : γ =ᶠ[𝓝 t₀] γ'
参数：hγt₀ : I.IsInteriorPoint (γ t₀)；hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : Tangent
Bundle I M)) (γ t₀)；hγ : IsMIntegralCurveAt γ v t₀；hγ' : IsMIntegralCurveAt γ' v
 t₀；h : γ t₀ = γ' t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `ContDiffAt.exists_lipschitzOnWith`：ContDiffAt.exists_lipschitzOnWith {f 
: E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) : exists K, exists t in 𝓝 x, Lips
chitzOnWith K f t
· 使用定理 `ContDiffAt.snd`：ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt
 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).2) x
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `range_mem_nhds_isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_mem_nhds_iff`：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s
 in 𝓝 x') ↔ s in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousAt_def`：continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f
 x), f ⁻¹' A in 𝓝 x
· 使用引理 `IsMIntegralCurveAt.continuousAt`：IsMIntegralCurveAt.continuousAt (hγ : I
sMIntegralCurveAt γ v t₀) : ContinuousAt γ t₀
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `IsMIntegralCurveAt.eventually_hasDerivAt`：IsMIntegralCurveAt.eventually_
hasDerivAt (hγ : IsMIntegralCurveAt γ v t₀) : forallᶠ t in 𝓝 t₀, HasDerivAt ((ex
tChartAt I (γ t₀)) ∘ γ) (tange…
· 使用定理 `HasDerivAt.congr_deriv`：HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (
h' : f' = g') : HasDerivAt f g' x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_extChartAt`：continuousAt_extChartAt (x : M) : ContinuousAt 
(extChartAt I x) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ODE_solution_unique_of_eventually`：ODE_solution_unique_of_eventually (hv
 : forallᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (s t)) (hf : forallᶠ t in 𝓝 t₀, Ha
sDerivAt f (v t (f t)) …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Local integral curves are unique.

If a $C^1$ vector field `v` admits two local integral curves `γ γ' : ℝ → M` at `
t₀` with
`γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval containing `t₀`.
-/
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (γ t₀))
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  -- extract a set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : ∃ K, ∃ s ∈ 𝓝 _, LipschitzOnWith K v' s :=
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint hγt₀)).snd.exists_lipschitzOnWith
  have hlip (t : ℝ) : LipschitzOnWith K ((fun _ ↦ v') t) ((fun _ ↦ s) t) := hlip
  -- internal lemmas to reduce code duplication
  have hsrc {g} (hg : IsMIntegralCurveAt g v t₀) :
    ∀ᶠ t in 𝓝 t₀, g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝 t := eventually_mem_nhds_iff.mpr <|
      continuousAt_def.mp hg.continuousAt _ <| extChartAt_source_mem_nhds (g t₀)
  have hmem {g : ℝ → M} {t} (ht : g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝 t) :
    g t ∈ (extChartAt I (g t₀)).source := mem_preimage.mp <| mem_of_mem_nhds ht
  have hdrv {g} (hg : IsMIntegralCurveAt g v t₀) (h' : γ t₀ = g t₀) : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt ((extChartAt I (g t₀)) ∘ g) ((fun _ ↦ v') t (((extChartAt I (g t₀)) ∘ g) t)) t ∧
      ((extChartAt I (g t₀)) ∘ g) t ∈ (fun _ ↦ s) t := by
    apply Filter.Eventually.and
    · apply (hsrc hg |>.and hg.eventually_hasDerivAt).mono
      rintro t ⟨ht1, ht2⟩
      rw [hv', h']
      apply ht2.congr_deriv
      congr <;>
      rw [Function.comp_apply, PartialEquiv.left_inv _ (hmem ht1)]
    · apply ((continuousAt_extChartAt (g t₀)).comp hg.continuousAt).preimage_mem_nhds
      rw [Function.comp_apply, ← h']
      exact hs
  have heq {g} (hg : IsMIntegralCurveAt g v t₀) :
    g =ᶠ[𝓝 t₀] (extChartAt I (g t₀)).symm ∘ ↑(extChartAt I (g t₀)) ∘ g := by
    apply (hsrc hg).mono
    intro t ht
    rw [Function.comp_apply, Function.comp_apply, PartialEquiv.left_inv _ (hmem ht)]
  -- main proof
  suffices (extChartAt I (γ t₀)) ∘ γ =ᶠ[𝓝 t₀] (extChartAt I (γ' t₀)) ∘ γ' from
    (heq hγ).trans <| (this.fun_comp (extChartAt I (γ t₀)).symm).trans (h ▸ (heq hγ').symm)
  exact ODE_solution_unique_of_eventually (.of_forall hlip)
    (hdrv hγ rfl) (hdrv hγ' h) (by rw [Function.comp_apply, Function.comp_apply, h])
/-
**isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless [BoundarylessM
anifold I M] (hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀)) 
(hγ : IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = 
γ' t₀) : γ =ᶠ[𝓝 t₀] γ'
参数：hv : CMDiffAt 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀)；hγ : IsMInte
gralCurveAt γ v t₀；hγ' : IsMIntegralCurveAt γ' v t₀；h : γ t₀ = γ' t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt`：isMIntegralCurveAt_event
uallyEq_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (γ t₀)) (hv : CMDiffAt 1 (fun x
 => (⟨x, v x⟩ : TangentBundle I M)) …
· 使用定理 `BoundarylessManifold.isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
-/
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless [BoundarylessManifold I M]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' :=
  isMIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h

variable [T2Space M] {a b : ℝ}

/-- Integral curves are unique on open intervals.

If a $C^1$ vector field `v` admits two integral curves `γ γ' : ℝ → M` on some open interval
`Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'` agree on `Ioo a b`. -/
/-
**isMIntegralCurveOn_Ioo_eqOn_of_contMDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (ht₀ : t₀ in Ioo a b) (hγt : fora
ll t in Ioo a b, I.IsInteriorPoint (γ t)) (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : T
angentBundle I M))) (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hγ' : IsMIntegralCu
rveOn γ' v (Ioo a b)) (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b)
参数：ht₀ : t₀ in Ioo a b；hγt : forall t in Ioo a b, I.IsInteriorPoint (γ t)；hv : C
MDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))；hγ : IsMIntegralCurveOn γ v (I
oo a b)；hγ' : IsMIntegralCurveOn γ' v (Ioo a b)；h : γ t₀ = γ' t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_of_closure_inter_subset`：IsPreconnected.subset_of_
closure_inter_subset (hs : IsPreconnected s) (hu : IsOpen u) (h'u : (s inter u).
Nonempty) (h : closure u inter s su…
· 使用定理 `isPreconnected_Ioo`：isPreconnected_Ioo : IsPreconnected (Ioo a b)
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt`：isMIntegralCurveAt_event
uallyEq_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (γ t₀)) (hv : CMDiffAt 1 (fun x
 => (⟨x, v x⟩ : TangentBundle I M)) …
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用引理 `IsMIntegralCurveOn.isMIntegralCurveAt`：IsMIntegralCurveOn.isMIntegralCur
veAt (h : IsMIntegralCurveOn γ v s) (hs : s in 𝓝 t₀) : IsMIntegralCurveAt γ v t₀
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Set.preimage_ofPred_eq`：preimage_ofPred_eq {p : α -> Prop} {f : β -> α} 
: f ⁻¹' { a | p a } = { a | p (f a) }
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Integral curves are unique on open intervals.

If a $C^1$ vector field `v` admits two integral curves `γ γ' : ℝ → M` on some op
en interval
`Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'` agree on
 `Ioo a b`.
-/
theorem isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (ht₀ : t₀ ∈ Ioo a b)
    (hγt : ∀ t ∈ Ioo a b, I.IsInteriorPoint (γ t))
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  -- since `Ioo a b` is connected, we get `s = Ioo a b` by showing that `s` is clopen in `Ioo a b`
  -- in the subtype topology (`s` is also non-empty by assumption)
  -- here we use a slightly weaker alternative theorem
  suffices hsub : Ioo a b ⊆ s from fun t ht ↦ mem_ofPred.mp ((subset_def ▸ hsub) t ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · -- is this really the most convenient way to pass to subtype topology?
    -- TODO: shorten this when better API around subtype topology exists
    rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hγ.continuousWithinAt ht |>.continuousAt (Ioo_mem_nhds ht.1 ht.2)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hγ'.continuousWithinAt ht |>.continuousAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hmem := Ioo_mem_nhds ht₁.2.1 ht₁.2.2
    have heq : γ =ᶠ[𝓝 t₁] γ' := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
      (hγt _ ht₁.2) hv.contMDiffAt (hγ.isMIntegralCurveAt hmem) (hγ'.isMIntegralCurveAt hmem) ht₁.1
    apply (heq.and hmem).mono
    exact fun _ ht ↦ ht
/-
**isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless [BoundarylessManifol
d I M] (ht₀ : t₀ in Ioo a b) (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle 
I M))) (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (I
oo a b)) (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b)
参数：ht₀ : t₀ in Ioo a b；hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))；h
γ : IsMIntegralCurveOn γ v (Ioo a b)；hγ' : IsMIntegralCurveOn γ' v (Ioo a b)；h :
 γ t₀ = γ' t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`：isMIntegralCurveOn_Ioo_eqOn_of
_contMDiff (ht₀ : t₀ in Ioo a b) (hγt : forall t in Ioo a b, I.IsInteriorPoint (
γ t)) (hv : CMDiff 1 (fun x =>…
· 使用定理 `BoundarylessManifold.isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
-/
theorem isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (ht₀ : t₀ ∈ Ioo a b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
    ht₀ (fun _ _ ↦ BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

/-- Global integral curves are unique.

If a continuously differentiable vector field `v` admits two global integral curves
`γ γ' : ℝ → M`, and `γ t₀ = γ' t₀` for some `t₀`, then `γ` and `γ'` are equal. -/
/-
**isMIntegralCurve_eq_of_contMDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_eq_of_contMDiff (hγt : forall t, I.IsInteriorPoint (γ t))
 (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) (hγ : IsMIntegralCurv
e γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ'
参数：hγt : forall t, I.IsInteriorPoint (γ t)；hv : CMDiff 1 (fun x => (⟨x, v x⟩ : T
angentBundle I M))；hγ : IsMIntegralCurve γ v；hγ' : IsMIntegralCurve γ' v；h : γ t
₀ = γ' t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `exists_abs_lt`：exists_abs_lt [Nontrivial α] (a : α) : exists b > 0, |a| 
< b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Global integral curves are unique.

If a continuously differentiable vector field `v` admits two global integral cur
ves
`γ γ' : ℝ → M`, and `γ t₀ = γ' t₀` for some `t₀`, then `γ` and `γ'` are equal.
-/
theorem isMIntegralCurve_eq_of_contMDiff (hγt : ∀ t, I.IsInteriorPoint (γ t))
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' := by
  ext t
  obtain ⟨T, ht₀, ht⟩ : ∃ T, t ∈ Ioo (-T) T ∧ t₀ ∈ Ioo (-T) T := by
    obtain ⟨T, hT₁, hT₂⟩ := exists_abs_lt t
    obtain ⟨hT₂, hT₃⟩ := abs_lt.mp hT₂
    obtain ⟨S, hS₁, hS₂⟩ := exists_abs_lt t₀
    obtain ⟨hS₂, hS₃⟩ := abs_lt.mp hS₂
    exact ⟨T + S, by constructor <;> constructor <;> linarith⟩
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff ht (fun t _ ↦ hγt t) hv
    ((hγ.isMIntegralCurveOn _).mono (subset_univ _))
    ((hγ'.isMIntegralCurveOn _).mono (subset_univ _)) h ht₀
/-
**isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless [BoundarylessManifold I 
M] (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) (hγ : IsMIntegralCu
rve γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ'
参数：hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))；hγ : IsMIntegralCurve
 γ v；hγ' : IsMIntegralCurve γ' v；h : γ t₀ = γ' t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMIntegralCurve_eq_of_contMDiff`：isMIntegralCurve_eq_of_contMDiff (hγt 
: forall t, I.IsInteriorPoint (γ t)) (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : Tangen
tBundle I M))) (hγ : I…
· 使用定理 `BoundarylessManifold.isInteriorPoint`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
-/
theorem isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_eq_of_contMDiff (fun _ ↦ BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

/-- For a global integral curve `γ`, if it crosses itself at `a b : ℝ`, then it is periodic with
period `a - b`. -/
/-
**IsMIntegralCurve.periodic_of_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.periodic_of_eq [BoundarylessManifold I M] (hγ : IsMIntegr
alCurve γ v) (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) (heq : γ 
a = γ b) : Periodic γ (a - b)
参数：hγ : IsMIntegralCurve γ v；hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I
 M))；heq : γ a = γ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless`：isMIntegralCurve_Ioo_
eq_of_contMDiff_boundaryless [BoundarylessManifold I M] (hv : CMDiff 1 (fun x =>
 (⟨x, v x⟩ : TangentBundle I M))) (hγ :…
· 使用引理 `IsMIntegralCurve.comp_add`：IsMIntegralCurve.comp_add (hγ : IsMIntegralCu
rve γ v) (dt : Real) : IsMIntegralCurve (γ ∘ (· + dt)) v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
For a global integral curve `γ`, if it crosses itself at `a b : ℝ`, then it is p
eriodic with
period `a - b`.
-/
lemma IsMIntegralCurve.periodic_of_eq [BoundarylessManifold I M]
    (hγ : IsMIntegralCurve γ v)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (heq : γ a = γ b) : Periodic γ (a - b) := by
  apply congrFun <|
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := b) hv (hγ.comp_add _) hγ _
  rw [comp_apply, add_sub_cancel, heq]

/-- A global integral curve is injective xor periodic with positive period. -/
/-
**IsMIntegralCurve.periodic_xor_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.periodic_xor_injective [BoundarylessManifold I M] (hγ : I
sMIntegralCurve γ v) (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
 Xor (exists T > 0, Periodic γ T) (Injective γ)
参数：hγ : IsMIntegralCurve γ v；hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I
 M))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `xor_iff_iff_not`：xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b)
· 使用定理 `Function.Periodic.not_injective`：∀ {R : Type u_4} {X : Type u_5} [inst :
 AddZeroClass R] {f : R → X} {c : R},   Function.Periodic f c → c ≠ 0 → ¬Functio
n.Injective f
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), Fu
nction.Injective f = ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `IsMIntegralCurve.periodic_of_eq`：IsMIntegralCurve.periodic_of_eq [Bounda
rylessManifold I M] (hγ : IsMIntegralCurve γ v) (hv : CMDiff 1 (fun x => (⟨x, v 
x⟩ : TangentBundle I …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a

--- 原说明 ---
A global integral curve is injective xor periodic with positive period.
-/
lemma IsMIntegralCurve.periodic_xor_injective [BoundarylessManifold I M]
    (hγ : IsMIntegralCurve γ v)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    Xor (∃ T > 0, Periodic γ T) (Injective γ) := by
  rw [xor_iff_iff_not]
  refine ⟨fun ⟨T, hT, hf⟩ ↦ hf.not_injective (ne_of_gt hT), ?_⟩
  intro h
  rw [Injective] at h
  push Not at h
  obtain ⟨a, b, heq, hne⟩ := h
  refine ⟨|a - b|, ?_, ?_⟩
  · rw [gt_iff_lt, abs_pos, sub_ne_zero]
    exact hne
  · by_cases! hab : a - b < 0
    · rw [abs_of_neg hab, neg_sub]
      exact hγ.periodic_of_eq hv heq.symm
    · rw [abs_of_nonneg hab]
      exact hγ.periodic_of_eq hv heq
