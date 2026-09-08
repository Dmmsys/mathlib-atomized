/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Existence and uniqueness of solutions to ODEs

This file collects the public-facing existence and uniqueness theorems for solutions to ODEs in
normed spaces.

## Main results

* `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`: the Picard-Lindelöf theorem,
  stating the existence of a local solution to a time-dependent ODE.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`: the
  existence of a local flow that is Lipschitz continuous in the initial point.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`: the existence
  of a local flow `E × ℝ → E` that is continuous on its domain.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`: the existence
  of a local flow to a time-dependent vector field.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`: a `C¹` vector
  field admits solutions on open intervals for all nearby initial points.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`: a `C¹` vector
  field admits a local solution.
* `ContDiffAt.exists_eventually_eq_hasDerivAt`: a `C¹` vector field admits a local flow.
* `ODE_solution_unique` and variants: uniqueness statements for ODE solutions on various intervals.

## Tags

integral curve, vector field, existence, uniqueness, Picard-Lindelöf, Gronwall
-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Existence of solutions to ODEs -/

namespace IsPicardLindelof

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution whose initial point `x` may be different from the centre `x₀` of
the closed ball within which the properties of the vector field hold. -/
/-
**IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt** 是 Mathlib 中的一个定理，
位于命名空间 `IsPicardLindelof`。
形式化陈述：exists_eq_forall_mem_Icc_hasDerivWithinAt (hf : IsPicardLindelof f t₀ x₀ a
 r L K) (hx : x in closedBall x₀ r) : exists α : Real -> E, α t₀ = x ∧ forall t 
in Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `ODE.FunSpace.exists_isFixedPt_next`：exists_isFixedPt_next [CompleteSpace
 E] (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) : exists
 α : FunSpace t₀ x₀ r L,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ODE.FunSpace.compProj_val`：compProj_val {α : FunSpace t₀ x₀ r L} {t : Ic
c tmin tmax} : α.compProj t = α t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ODE.FunSpace.next_apply₀`：next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r
 L K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x
· 使用定理 `HasDerivWithinAt.congr_of_mem`：HasDerivWithinAt.congr_of_mem (h : HasDer
ivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x) (hx : x in s) : HasDerivWi
thinAt f₁ f' s x
· 使用引理 `ODE.hasDerivWithinAt_picard_Icc`：hasDerivWithinAt_picard_Icc (ht₀ : t₀ i
n Icc tmin tmax) (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : Co
ntinuousOn α (Icc tmi…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsPicardLindelof.continuousOn_uncurry`：continuousOn_uncurry (hf : IsPica
rdLindelof f t₀ x₀ a r L K) : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (clos
edBall x₀ a))
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `ODE.FunSpace.continuous_compProj`：continuous_compProj (α : FunSpace t₀ x
₀ r L) : Continuous α.compProj
· 使用引理 `ODE.FunSpace.compProj_mem_closedBall`：compProj_mem_closedBall (α : FunSp
ace t₀ x₀ r L) (h : L * max (tmax - t₀) (t₀ - tmin) <= a - r) {t : Real} : α.com
pProj t in closedBall x₀ a
· 使用定理 `IsPicardLindelof.mul_max_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r 
L K : NNReal}, Is…
· 使用引理 `ODE.FunSpace.compProj_of_mem`：compProj_of_mem {α : FunSpace t₀ x₀ r L} {
t : Real} (ht : t in Icc tmin tmax) : α.compProj t = α ⟨t, ht⟩
· 使用引理 `ODE.FunSpace.next_apply`：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L
 K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : n
ext hf hx α t…

--- 原说明 ---
**Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version 
shows the
existence of a local solution whose initial point `x` may be different from the 
centre `x₀` of
the closed ball within which the properties of the vector field hold.
-/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
/-
**IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt** 是 Mathlib 中的一个定理，
位于命名空间 `IsPicardLindelof`。
形式化陈述：exists_eq_forall_mem_Icc_hasDerivWithinAt (hf : IsPicardLindelof f t₀ x₀ a
 r L K) (hx : x in closedBall x₀ r) : exists α : Real -> E, α t₀ = x ∧ forall t 
in Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K；hx : x in closedBall x₀ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `ODE.FunSpace.exists_isFixedPt_next`：exists_isFixedPt_next [CompleteSpace
 E] (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) : exists
 α : FunSpace t₀ x₀ r L,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ODE.FunSpace.compProj_val`：compProj_val {α : FunSpace t₀ x₀ r L} {t : Ic
c tmin tmax} : α.compProj t = α t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ODE.FunSpace.next_apply₀`：next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r
 L K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x
· 使用定理 `HasDerivWithinAt.congr_of_mem`：HasDerivWithinAt.congr_of_mem (h : HasDer
ivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x) (hx : x in s) : HasDerivWi
thinAt f₁ f' s x
· 使用引理 `ODE.hasDerivWithinAt_picard_Icc`：hasDerivWithinAt_picard_Icc (ht₀ : t₀ i
n Icc tmin tmax) (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : Co
ntinuousOn α (Icc tmi…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsPicardLindelof.continuousOn_uncurry`：continuousOn_uncurry (hf : IsPica
rdLindelof f t₀ x₀ a r L K) : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (clos
edBall x₀ a))
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `ODE.FunSpace.continuous_compProj`：continuous_compProj (α : FunSpace t₀ x
₀ r L) : Continuous α.compProj
· 使用引理 `ODE.FunSpace.compProj_mem_closedBall`：compProj_mem_closedBall (α : FunSp
ace t₀ x₀ r L) (h : L * max (tmax - t₀) (t₀ - tmin) <= a - r) {t : Real} : α.com
pProj t in closedBall x₀ a
· 使用定理 `IsPicardLindelof.mul_max_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r 
L K : NNReal}, Is…
· 使用引理 `ODE.FunSpace.compProj_of_mem`：compProj_of_mem {α : FunSpace t₀ x₀ r L} {
t : Real} (ht : t in Icc tmin tmax) : α.compProj t = α ⟨t, ht⟩
· 使用引理 `ODE.FunSpace.next_apply`：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L
 K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : n
ext hf hx α t…

--- 原说明 ---
**Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form.
-/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
  exists_eq_forall_mem_Icc_hasDerivWithinAt hf (mem_closedBall_self le_rfl)

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is Lipschitz continuous in the initial point. -/
/-
**IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnW
ith** 是 Mathlib 中的一个定理，位于命名空间 `IsPicardLindelof`。
形式化陈述：exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith (hf : IsP
icardLindelof f t₀ x₀ a r L K) : exists α : E -> Real -> E, (forall x in closedB
all x₀ r, α x t₀ = x ∧ forall t in Icc tmin tmax, HasDerivWithinAt (α x) (f t (α
 x t)) (Icc tmin tmax) t) ∧ exists L' : Real>=0, forall t in Icc tmin tmax, Lips
chitzOnWith L' (α · t) (closedBall x₀ r)
参数：hf : IsPicardLindelof f t₀ x₀ a r L K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ODE.FunSpace.exists_isFixedPt_next`：exists_isFixedPt_next [CompleteSpace
 E] (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) : exists
 α : FunSpace t₀ x₀ r L,…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `ODE.FunSpace.compProj_val`：compProj_val {α : FunSpace t₀ x₀ r L} {t : Ic
c tmin tmax} : α.compProj t = α t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ODE.FunSpace.next_apply₀`：next_apply₀ (hf : IsPicardLindelof f t₀ x₀ a r
 L K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) : next hf hx α t₀ = x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ODE.FunSpace.compProj_apply`：compProj_apply {α : FunSpace t₀ x₀ r L} {t 
: Real} : α.compProj t = α (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) t)
· 使用定理 `HasDerivWithinAt.congr_of_mem`：HasDerivWithinAt.congr_of_mem (h : HasDer
ivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x) (hx : x in s) : HasDerivWi
thinAt f₁ f' s x
· 使用引理 `ODE.hasDerivWithinAt_picard_Icc`：hasDerivWithinAt_picard_Icc (ht₀ : t₀ i
n Icc tmin tmax) (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u)) (hα : Co
ntinuousOn α (Icc tmi…
· 使用引理 `IsPicardLindelof.continuousOn_uncurry`：continuousOn_uncurry (hf : IsPica
rdLindelof f t₀ x₀ a r L K) : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (clos
edBall x₀ a))
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `ODE.FunSpace.continuous_compProj`：continuous_compProj (α : FunSpace t₀ x
₀ r L) : Continuous α.compProj
· 使用引理 `ODE.FunSpace.compProj_mem_closedBall`：compProj_mem_closedBall (α : FunSp
ace t₀ x₀ r L) (h : L * max (tmax - t₀) (t₀ - tmin) <= a - r) {t : Real} : α.com
pProj t in closedBall x₀ a
· 使用定理 `IsPicardLindelof.mul_max_le`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Set.Icc tmin tmax)} {x₀ : E}   {a r 
L K : NNReal}, Is…
· 使用引理 `ODE.FunSpace.compProj_of_mem`：compProj_of_mem {α : FunSpace t₀ x₀ r L} {
t : Real} (ht : t in Icc tmin tmax) : α.compProj t = α ⟨t, ht⟩
· 使用引理 `ODE.FunSpace.next_apply`：next_apply (hf : IsPicardLindelof f t₀ x₀ a r L
 K) (hx : x in closedBall x₀ r) (α : FunSpace t₀ x₀ r L) {t : Icc tmin tmax} : n
ext hf hx α t…
· 使用引理 `ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul`：exists_foral
l_closedBall_funSpace_dist_le_mul [CompleteSpace E] (hf : IsPicardLindelof f t₀ 
x₀ a r L K) : exists L' : Real>=0, forall (x y :…
· 使用定理 `LipschitzOnWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseu
doMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : 
α → β}, (∀ x ∈ s, ∀ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ODE.FunSpace.toContinuousMap_apply_eq_apply`：toContinuousMap_apply_eq_ap
ply (α : FunSpace t₀ x₀ r L) (t : Icc tmin tmax) : α.toContinuousMap t = α t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.dist_le_iff_of_nonempty`：dist_le_iff_of_nonempty [Nonempty
 α] : dist f g <= C ↔ forall x, dist (f x) (g x) <= C
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
**Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version 
shows the
existence of a local flow and that it is Lipschitz continuous in the initial poi
nt.
-/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  classical
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dif_pos hx, dif_pos hy, FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is continuous on its domain as a (partial) map `E × ℝ → E`. -/
/-
**IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
** 是 Mathlib 中的一个定理，位于命名空间 `IsPicardLindelof`。
形式化陈述：exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn (hf : IsPica
rdLindelof f t₀ x₀ a r L K) : exists α : E × Real -> E, (forall x in closedBall 
x₀ r, α ⟨x, t₀⟩ = x ∧ forall t in Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f 
t (α ⟨x, t⟩)) (Icc tmin tmax) t) ∧ ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin t
max)
参数：hf : IsPicardLindelof f t₀ x₀ a r L K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipsch
itzOnWith`：exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith (hf 
: IsPicardLindelof f t₀ x₀ a r L K) : exists α : E -> Real -> E, (foral…
· 使用定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith`：continuousOn_prod_of_
continuousOn_lipschitzOnWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) {s : S…
· 使用定理 `HasDerivWithinAt.continuousOn`：HasDerivWithinAt.continuousOn {f f' : 𝕜 -
> F} (h : forall x in s, HasDerivWithinAt f (f' x) s x) : ContinuousOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version 
shows the
existence of a local flow and that it is continuous on its domain as a (partial)
 map `E × ℝ → E`.
-/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx ↦ HasDerivWithinAt.continuousOn (hα1 x hx).2

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow. -/
/-
**IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithin
At** 是 Mathlib 中的一个定理，位于命名空间 `IsPicardLindelof`。
形式化陈述：exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt (hf : IsPi
cardLindelof f t₀ x₀ a r L K) : exists α : E -> Real -> E, forall x in closedBal
l x₀ r, α x t₀ = x ∧ forall t in Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x
 t)) (Icc tmin tmax) t
参数：hf : IsPicardLindelof f t₀ x₀ a r L K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipsch
itzOnWith`：exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith (hf 
: IsPicardLindelof f t₀ x₀ a r L K) : exists α : E -> Real -> E, (foral…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
**Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version 
shows the
existence of a local flow.
-/
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t :=
  have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hf
  ⟨α, hα.1⟩

end IsPicardLindelof

/-! ## $C^1$ vector field -/

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {x₀ : E}

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
/-
**ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt** 
是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt (hf : Con
tDiffAt Real 1 f x₀) (t₀ : Real) : exists r > (0 : Real), exists ε > (0 : Real),
 forall x in closedBall x₀ r, exists α : Real -> E, α t₀ = x ∧ forall t in Ioo (
t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t
参数：hf : ContDiffAt Real 1 f x₀；t₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `IsPicardLindelof.of_contDiffAt_one`：of_contDiffAt_one [NormedSpace Real 
E] {f : E -> E} {x₀ : E} (hf : ContDiffAt Real 1 f x₀) : exists (ε : Real) (hε :
 0 < ε) (a r L K : Real>…
· 使用定理 `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`：exists_eq_fo
rall_mem_Icc_hasDerivWithinAt (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in
 closedBall x₀ r) : exists α : Real -> E, α t₀ =…
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then i
t admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `
α t₀ = x`, where
`x` may be different from `x₀`.
-/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨α, hα1, fun t ht ↦ ?_⟩
  exact hα2 t (Ioo_subset_Icc_self ht) |>.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
/-
**ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt** 
是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt (hf : Con
tDiffAt Real 1 f x₀) (t₀ : Real) : exists r > (0 : Real), exists ε > (0 : Real),
 forall x in closedBall x₀ r, exists α : Real -> E, α t₀ = x ∧ forall t in Ioo (
t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t
参数：hf : ContDiffAt Real 1 f x₀；t₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `IsPicardLindelof.of_contDiffAt_one`：of_contDiffAt_one [NormedSpace Real 
E] {f : E -> E} {x₀ : E} (hf : ContDiffAt Real 1 f x₀) : exists (ε : Real) (hε :
 0 < ε) (a r L K : Real>…
· 使用定理 `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`：exists_eq_fo
rall_mem_Icc_hasDerivWithinAt (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in
 closedBall x₀ r) : exists α : Real -> E, α t₀ =…
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then i
t admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `
α t₀ = x₀`.
-/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨α, hα1, ε, hε, hα2⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
/-
**ContDiffAt.exists_eventually_eq_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff
At`。
形式化陈述：exists_eventually_eq_hasDerivAt (hf : ContDiffAt Real 1 f x₀) (t₀ : Real) 
: exists α : E -> Real -> E, forallᶠ xt in 𝓝 x₀ ×ˢ 𝓝 t₀, α xt.1 t₀ = xt.1 ∧ HasD
erivAt (α xt.1) (f (α xt.1 xt.2)) xt.2
参数：hf : ContDiffAt Real 1 f x₀；t₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDeri
vAt`：exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt (hf : Cont
DiffAt Real 1 f x₀) (t₀ : Real) : exists r > (0 : Real), exists ε…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.prod_mem_prod_iff`：prod_mem_prod_iff [f.NeBot] [g.NeBot] : s ×ˢ t
 in f ×ˢ g ↔ s in f ∧ t in g
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then i
t admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` f
or all `x` within
the domain.
-/
theorem exists_eventually_eq_hasDerivAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : E → ℝ → E, ∀ᶠ xt in 𝓝 x₀ ×ˢ 𝓝 t₀,
      α xt.1 t₀ = xt.1 ∧ HasDerivAt (α xt.1) (f (α xt.1 xt.2)) xt.2 := by
  classical
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  choose α hα using H
  refine ⟨fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then α x hx else 0, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε), ?_, ?_⟩
  · rw [Filter.prod_mem_prod_iff]
    exact ⟨closedBall_mem_nhds x₀ hr, Ioo_mem_nhds (by linarith) (by linarith)⟩
  · grind

end ContDiffAt

/-! ## Uniqueness of solutions to ODEs -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g : ℝ → E} {a b t₀ : ℝ}

/-- There exists only one solution of an ODE $\dot x=v(t, x)$ in a set `s ⊆ ℝ × E` with
a given initial value provided that the RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`.

This version shows uniqueness in a closed interval `Icc a b`, where `a` is the initial time. -/
/-
**ODE_solution_unique_of_mem_Icc_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique_of_mem_Icc_right (hv : forall t in Ico a b, LipschitzO
nWith K (v t) (s t)) (hf : ContinuousOn f (Icc a b)) (hf' : forall t in Ico a b,
 HasDerivWithinAt f (v t (f t)) (Ici t) t) (hfs : forall t in Ico a b, f t in s 
t) (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ico a b, HasDerivWithinAt 
g (v t (g t)) (Ici t) t) (hgs : forall t in Ico a b, g t in s t) (ha : f a = g a
) : EqOn f g (Icc a b)
参数：hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)；hf : ContinuousOn f (
Icc a b)；hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t；hfs
 : forall t in Ico a b, f t in s t；hg : ContinuousOn g (Icc a b)；hg' : forall t 
in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t；hgs : forall t in Ico a b, 
g t in s t；ha : f a = g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `dist_le_of_trajectories_ODE_of_mem`：dist_le_of_trajectories_ODE_of_mem (
hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn f (I
cc a b)) (hf' : forall t…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_le_zero`：dist_le_zero {x y : γ} : dist x y <= 0 ↔ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
There exists only one solution of an ODE $\dot x=v(t, x)$ in a set `s ⊆ ℝ × E` w
ith
a given initial value provided that the RHS is Lipschitz continuous in `x` withi
n `s`,
and we consider only solutions included in `s`.

This version shows uniqueness in a closed interval `Icc a b`, where `a` is the i
nitial time.
-/
theorem ODE_solution_unique_of_mem_Icc_right
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) := fun t ht ↦ by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

/-- A time-reversed version of `ODE_solution_unique_of_mem_Icc_right`. Uniqueness is shown in a
closed interval `Icc a b`, where `b` is the "initial" time. -/
/-
**ODE_solution_unique_of_mem_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique_of_mem_Icc_left (hv : forall t in Ioc a b, LipschitzOn
With K (v t) (s t)) (hf : ContinuousOn f (Icc a b)) (hf' : forall t in Ioc a b, 
HasDerivWithinAt f (v t (f t)) (Iic t) t) (hfs : forall t in Ioc a b, f t in s t
) (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ioc a b, HasDerivWithinAt g
 (v t (g t)) (Iic t) t) (hgs : forall t in Ioc a b, g t in s t) (hb : f b = g b)
 : EqOn f g (Icc a b)
参数：hv : forall t in Ioc a b, LipschitzOnWith K (v t) (s t)；hf : ContinuousOn f (
Icc a b)；hf' : forall t in Ioc a b, HasDerivWithinAt f (v t (f t)) (Iic t) t；hfs
 : forall t in Ioc a b, f t in s t；hg : ContinuousOn g (Icc a b)；hg' : forall t 
in Ioc a b, HasDerivWithinAt g (v t (g t)) (Iic t) t；hgs : forall t in Ioc a b, 
g t in s t；hb : f b = g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
A time-reversed version of `ODE_solution_unique_of_mem_Icc_right`. Uniqueness is
 shown in a
closed interval `Icc a b`, where `b` is the "initial" time.
-/
theorem ODE_solution_unique_of_mem_Icc_left
    (hv : ∀ t ∈ Ioc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioc a b, HasDerivWithinAt f (v t (f t)) (Iic t) t)
    (hfs : ∀ t ∈ Ioc a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioc a b, HasDerivWithinAt g (v t (g t)) (Iic t) t)
    (hgs : ∀ t ∈ Ioc a b, g t ∈ s t)
    (hb : f b = g b) :
    EqOn f g (Icc a b) := by
  have hv' : ∀ t ∈ Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    replace ht : -t ∈ Ioc a b := by
      push _ ∈ _ at ht ⊢
      constructor <;> linarith
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht)
  have hmt1 : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ ht ↦ ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt2 : MapsTo Neg.neg (Ico (-b) (-a)) (Ioc a b) :=
    fun _ ht ↦ ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt3 (t : ℝ) : MapsTo Neg.neg (Ici t) (Iic (-t)) :=
    fun _ ht' ↦ mem_Iic.mpr <| neg_le_neg ht'
  suffices EqOn (f ∘ Neg.neg) (g ∘ Neg.neg) (Icc (-b) (-a)) by
    rw [eqOn_comp_right_iff] at this
    convert this
    simp
  apply ODE_solution_unique_of_mem_Icc_right hv'
    (hf.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hfs _ (hmt2 ht))
    (hg.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hgs _ (hmt2 ht)) (by simp [hb])
  · intro t ht
    convert!
      HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (-t) (hmt2 ht))
        (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp
  · intro t ht
    convert!
      HasFDerivWithinAt.comp_hasDerivWithinAt t (hg' (-t) (hmt2 ht))
        (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp

/-- A version of `ODE_solution_unique_of_mem_Icc_right` for uniqueness in a closed interval whose
interior contains the initial time. -/
/-
**ODE_solution_unique_of_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique_of_mem_Icc (hv : forall t in Ioo a b, LipschitzOnWith 
K (v t) (s t)) (ht : t₀ in Ioo a b) (hf : ContinuousOn f (Icc a b)) (hf' : foral
l t in Ioo a b, HasDerivAt f (v t (f t)) t) (hfs : forall t in Ioo a b, f t in s
 t) (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ioo a b, HasDerivAt g (v 
t (g t)) t) (hgs : forall t in Ioo a b, g t in s t) (heq : f t₀ = g t₀) : EqOn f
 g (Icc a b)
参数：hv : forall t in Ioo a b, LipschitzOnWith K (v t) (s t)；ht : t₀ in Ioo a b；hf
 : ContinuousOn f (Icc a b)；hf' : forall t in Ioo a b, HasDerivAt f (v t (f t)) 
t；hfs : forall t in Ioo a b, f t in s t；hg : ContinuousOn g (Icc a b)；hg' : fora
ll t in Ioo a b, HasDerivAt g (v t (g t)) t；hgs : forall t in Ioo a b, g t in s 
t；heq : f t₀ = g t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Icc_eq_Icc`：Icc_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= 
c) : Icc a b union Icc b c = Icc a c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.EqOn.union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ :
 α → β},   Set.EqOn f₁ f₂ s₁ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ (s₁ ∪ s₂)
· 使用定理 `Set.Ioc_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Ioc b a₂ ⊆ Set.Ioo b a₁
· 使用定理 `ODE_solution_unique_of_mem_Icc_left`：ODE_solution_unique_of_mem_Icc_left
 (hv : forall t in Ioc a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn f 
(Icc a b)) (hf' : forall …
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Icc_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Icc b a₂ ⊆ Set.Icc b a₁
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Set.Ico_subset_Ioo_left`：Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b su
bseteq Ioo a₁ b
· 使用定理 `ODE_solution_unique_of_mem_Icc_right`：ODE_solution_unique_of_mem_Icc_rig
ht (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn 
f (Icc a b)) (hf' : forall…
· 使用定理 `Set.Icc_subset_Icc_left`：Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b s
ubseteq Icc a₁ b

--- 原说明 ---
A version of `ODE_solution_unique_of_mem_Icc_right` for uniqueness in a closed i
nterval whose
interior contains the initial time.
-/
theorem ODE_solution_unique_of_mem_Icc
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ Ioo a b, g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ ⊆ Ioo a b := Ioc_subset_Ioo_right ht.2
    exact ODE_solution_unique_of_mem_Icc_left (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq
  · have hss : Ico t₀ b ⊆ Ioo a b := Ico_subset_Ioo_left ht.1
    exact ODE_solution_unique_of_mem_Icc_right (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq

/-- A version of `ODE_solution_unique_of_mem_Icc` for uniqueness in an open interval. -/
/-
**ODE_solution_unique_of_mem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique_of_mem_Ioo (hv : forall t in Ioo a b, LipschitzOnWith 
K (v t) (s t)) (ht : t₀ in Ioo a b) (hf : forall t in Ioo a b, HasDerivAt f (v t
 (f t)) t ∧ f t in s t) (hg : forall t in Ioo a b, HasDerivAt g (v t (g t)) t ∧ 
g t in s t) (heq : f t₀ = g t₀) : EqOn f g (Ioo a b)
参数：hv : forall t in Ioo a b, LipschitzOnWith K (v t) (s t)；ht : t₀ in Ioo a b；hf
 : forall t in Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t in s t；hg : forall t in
 Ioo a b, HasDerivAt g (v t (g t)) t ∧ g t in s t；heq : f t₀ = g t₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ODE_solution_unique_of_mem_Icc_left`：ODE_solution_unique_of_mem_Icc_left
 (hv : forall t in Ioc a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn f 
(Icc a b)) (hf' : forall …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `HasDerivAt.continuousOn`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {s 
: Set 𝕜} {f f…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ODE_solution_unique_of_mem_Icc_right`：ODE_solution_unique_of_mem_Icc_rig
ht (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn 
f (Icc a b)) (hf' : forall…
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a

--- 原说明 ---
A version of `ODE_solution_unique_of_mem_Icc` for uniqueness in an open interval
.
-/
theorem ODE_solution_unique_of_mem_Ioo
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  intro t' ht'
  rcases lt_or_ge t' t₀ with (h | h)
  · have hss : Icc t' t₀ ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t'' ht'' ↦ hv t'' ((Ioc_subset_Icc_self.trans hss) ht''))
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hf _ <| hss ht'').1)
      (fun _ ht'' ↦ (hf _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ioc_subset_Icc_self ht'').2)
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hg _ <| hss ht'').1)
      (fun _ ht'' ↦ (hg _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ioc_subset_Icc_self ht'').2) heq
      ⟨le_rfl, le_of_lt h⟩
  · have hss : Icc t₀ t' ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht.1 ht''.1, lt_of_le_of_lt ht''.2 ht'.2⟩
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t'' ht'' ↦ hv t'' ((Ico_subset_Icc_self.trans hss) ht''))
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hf _ <| hss ht'').1)
      (fun _ ht'' ↦ (hf _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ico_subset_Icc_self ht'').2)
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hg _ <| hss ht'').1)
      (fun _ ht'' ↦ (hg _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ico_subset_Icc_self ht'').2) heq
      ⟨h, le_rfl⟩

/-- Local uniqueness of ODE solutions. -/
/-
**ODE_solution_unique_of_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique_of_eventually (hv : forallᶠ t in 𝓝 t₀, LipschitzOnWith
 K (v t) (s t)) (hf : forallᶠ t in 𝓝 t₀, HasDerivAt f (v t (f t)) t ∧ f t in s t
) (hg : forallᶠ t in 𝓝 t₀, HasDerivAt g (v t (g t)) t ∧ g t in s t) (heq : f t₀ 
= g t₀) : f =ᶠ[𝓝 t₀] g
参数：hv : forallᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (s t)；hf : forallᶠ t in 𝓝 t₀,
 HasDerivAt f (v t (f t)) t ∧ f t in s t；hg : forallᶠ t in 𝓝 t₀, HasDerivAt g (v
 t (g t)) t ∧ g t in s t；heq : f t₀ = g t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用定理 `ODE_solution_unique_of_mem_Ioo`：ODE_solution_unique_of_mem_Ioo (hv : for
all t in Ioo a b, LipschitzOnWith K (v t) (s t)) (ht : t₀ in Ioo a b) (hf : fora
ll t in Ioo a b, Has…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Local uniqueness of ODE solutions.
-/
theorem ODE_solution_unique_of_eventually
    (hv : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (s t))
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hv.and (hf.and hg))
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  apply ODE_solution_unique_of_mem_Ioo (fun _ ht ↦ (h _ ht).1)
    (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_self hε)
    (fun _ ht ↦ (h _ ht).2.1) (fun _ ht ↦ (h _ ht).2.2) heq

/-- There exists only one solution of an ODE $\dot x=v(t, x)$ with
a given initial value provided that the RHS is Lipschitz continuous in `x`. -/
/-
**ODE_solution_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique (hv : forall t, LipschitzWith K (v t)) (hf : Continuou
sOn f (Icc a b)) (hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici
 t) t) (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ico a b, HasDerivWithi
nAt g (v t (g t)) (Ici t) t) (ha : f a = g a) : EqOn f g (Icc a b)
参数：hv : forall t, LipschitzWith K (v t)；hf : ContinuousOn f (Icc a b)；hf' : fora
ll t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t；hg : ContinuousOn g (I
cc a b)；hg' : forall t in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t；ha :
 f a = g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `trivial`：True
· 使用定理 `ODE_solution_unique_of_mem_Icc_right`：ODE_solution_unique_of_mem_Icc_rig
ht (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn 
f (Icc a b)) (hf' : forall…
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…

--- 原说明 ---
There exists only one solution of an ODE $\dot x=v(t, x)$ with
a given initial value provided that the RHS is Lipschitz continuous in `x`.
-/
theorem ODE_solution_unique
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ univ := fun _ _ => trivial
  ODE_solution_unique_of_mem_Icc_right (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha

/-- There exists only one global solution to an ODE $\dot x=v(t, x)$ with a given initial value
provided that the RHS is Lipschitz continuous. -/
/-
**ODE_solution_unique_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ODE_solution_unique_univ (hv : forall t, LipschitzOnWith K (v t) (s t)) (h
f : forall t, HasDerivAt f (v t (f t)) t ∧ f t in s t) (hg : forall t, HasDerivA
t g (v t (g t)) t ∧ g t in s t) (heq : f t₀ = g t₀) : f = g
参数：hv : forall t, LipschitzOnWith K (v t) (s t)；hf : forall t, HasDerivAt f (v t
 (f t)) t ∧ f t in s t；hg : forall t, HasDerivAt g (v t (g t)) t ∧ g t in s t；he
q : f t₀ = g t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ODE_solution_unique_of_mem_Ioo`：ODE_solution_unique_of_mem_Ioo (hv : for
all t in Ioo a b, LipschitzOnWith K (v t) (s t)) (ht : t₀ in Ioo a b) (hf : fora
ll t in Ioo a b, Has…

--- 原说明 ---
There exists only one global solution to an ODE $\dot x=v(t, x)$ with a given in
itial value
provided that the RHS is Lipschitz continuous.
-/
theorem ODE_solution_unique_univ
    (hv : ∀ t, LipschitzOnWith K (v t) (s t))
    (hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f = g := by
  ext t
  obtain ⟨A, B, Ht, Ht₀⟩ : ∃ A B, t ∈ Set.Ioo A B ∧ t₀ ∈ Set.Ioo A B := by
    use (min (-|t|) (-|t₀|) - 1), (max |t| |t₀| + 1)
    grind
  exact ODE_solution_unique_of_mem_Ioo
    (fun t _ => hv t) Ht₀ (fun t _ => hf t) (fun t _ => hg t) heq Ht
