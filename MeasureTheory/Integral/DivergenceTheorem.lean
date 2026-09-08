/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Divergence theorem for Bochner integral

In this file we prove the Divergence theorem for Bochner integral on a box in
`ℝⁿ⁺¹ = Fin (n + 1) → ℝ`. More precisely, we prove the following theorem.

Let `E` be a complete normed space. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is
continuous on a rectangular box `[a, b] : Set ℝⁿ⁺¹`, `a ≤ b`, differentiable on its interior with
derivative `f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹`, and the divergence `fun x ↦ ∑ i, f' x eᵢ i`
is integrable on `[a, b]`, where `eᵢ = Pi.single i 1` is the `i`-th basis vector,
then its integral is equal to the sum of integrals of `f` over the faces of `[a, b]`,
taken with appropriate signs. Moreover, the same
is true if the function is not differentiable at countably many points of the interior of `[a, b]`.

Once we prove the general theorem, we deduce corollaries for functions `ℝ → E` and pairs of
functions `(ℝ × ℝ) → E`.

## Notation

We use the following local notation to make the statement more readable. Note that the documentation
website shows the actual terms, not those abbreviated using local notations.

* `ℝⁿ`, `ℝⁿ⁺¹`, `Eⁿ⁺¹`: `Fin n → ℝ`, `Fin (n + 1) → ℝ`, `Fin (n + 1) → E`;
* `face i`: the `i`-th face of the box `[a, b]` as a closed segment in `ℝⁿ`, namely
  `[a ∘ Fin.succAbove i, b ∘ Fin.succAbove i]`;
* `e i` : `i`-th basis vector `Pi.single i 1`;
* `frontFace i`, `backFace i`: embeddings `ℝⁿ → ℝⁿ⁺¹` corresponding to the front face
  `{x | x i = b i}` and back face `{x | x i = a i}` of the box `[a, b]`, respectively.
  They are given by `Fin.insertNth i (b i)` and `Fin.insertNth i (a i)`.

## TODO

* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/

public section


open Set Finset TopologicalSpace Function BoxIntegral MeasureTheory Filter

open scoped Topology Interval

universe u

namespace MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section

variable {n : ℕ}

local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n → $t)

local macro:arg t:term:max noWs "ⁿ⁺¹" : term => `(Fin (n + 1) → $t)

local notation "e " i => Pi.single i 1

section

/-!
### Divergence theorem for functions on `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`.

In this section we use the divergence theorem for a Henstock-Kurzweil-like integral
`BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` to prove the divergence
theorem for Bochner integral. The divergence theorem for Bochner integral
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` assumes that the function
itself is continuous on a closed box, differentiable at all but countably many points of its
interior, and the divergence is integrable on the box.

This statement differs from `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt`
in several aspects.

* We use Bochner integral instead of a Henstock-Kurzweil integral. This modification is done in
  `MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁`. As a side effect
  of this change, we need to assume that the divergence is integrable.

* We don't assume differentiability on the boundary of the box. This modification is done in
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_aux₂`. To prove it, we
  choose an increasing sequence of smaller boxes that cover the interior of the original box, then
  apply the previous lemma to these smaller boxes and take the limit of both sides of the equation.

* We assume `a ≤ b` instead of `∀ i, a i < b i`. This is the last step of the proof, and it is done
  in the main theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
-/

/-- An auxiliary lemma for
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. This is exactly
`BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` reformulated for the
Bochner integral. -/
/-
**MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable_aux** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma for
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. This is exactl
y
`BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` reformulated 
for the
Bochner integral.
-/
private theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (I : Box (Fin (n + 1)))
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
    (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹)
    (hs : s.Countable) (Hc : ContinuousOn f (Box.Icc I))
    (Hd : ∀ x ∈ (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Box.Icc I)) :
    (∫ x in Box.Icc I, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in Box.Icc (I.face i), f (i.insertNth (I.upper i) x) i) -
          ∫ x in Box.Icc (I.face i), f (i.insertNth (I.lower i) x) i) := by
  wlog hE : CompleteSpace E generalizing
  · simp [integral, hE]
  simp only [← setIntegral_congr_set (Box.coe_ae_eq_Icc _)]
  have A := (Hi.mono_set Box.coe_subset_Icc).hasBoxIntegral ⊥ rfl
  have B :=
    hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I f f' (s ∩ Box.Icc I)
      (hs.mono inter_subset_left) (fun x hx => Hc _ hx.2) fun x hx =>
      Hd _ ⟨hx.1, fun h => hx.2 ⟨h, hx.1⟩⟩
  rw [continuousOn_pi] at Hc
  refine (A.unique B).trans (sum_congr rfl fun i _ => ?_)
  refine congr_arg₂ Sub.sub ?_ ?_
  · have := Box.continuousOn_face_Icc (Hc i) (Set.right_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrableOn_compact (μ := volume) (Box.isCompact_Icc _)).mono_set
      Box.coe_subset_Icc
    exact (this.hasBoxIntegral ⊥ rfl).integral_eq
  · have := Box.continuousOn_face_Icc (Hc i) (Set.left_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrableOn_compact (μ := volume) (Box.isCompact_Icc _)).mono_set
      Box.coe_subset_Icc
    exact (this.hasBoxIntegral ⊥ rfl).integral_eq

/-- An auxiliary lemma for
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Compared to the previous
lemma, here we drop the assumption of differentiability on the boundary of the box. -/
/-
**MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_aux** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma for
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Compared to th
e previous
lemma, here we drop the assumption of differentiability on the boundary of the b
ox.
-/
private theorem integral_divergence_of_hasFDerivAt_off_countable_aux₂ (I : Box (Fin (n + 1)))
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
    (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹)
    (s : Set ℝⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Box.Icc I))
    (Hd : ∀ x ∈ Box.Ioo I \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (∑ i, f' · (e i) i) (Box.Icc I)) :
    (∫ x in Box.Icc I, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in Box.Icc (I.face i), f (i.insertNth (I.upper i) x) i) -
          ∫ x in Box.Icc (I.face i), f (i.insertNth (I.lower i) x) i) := by
  /- Choose a monotone sequence `J k` of subboxes that cover the interior of `I` and prove that
    these boxes satisfy the assumptions of the previous lemma. -/
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩
  have hJ_sub' : ∀ k, Box.Icc (J k) ⊆ Box.Icc I := fun k => (hJ_sub k).trans I.Ioo_subset_Icc
  have hJ_le : ∀ k, J k ≤ I := fun k => Box.le_iff_Icc.2 (hJ_sub' k)
  have HcJ : ∀ k, ContinuousOn f (Box.Icc (J k)) := fun k => Hc.mono (hJ_sub' k)
  have HdJ : ∀ (k), ∀ x ∈ (Box.Icc (J k)) \ s, HasFDerivWithinAt f (f' x) (Box.Icc (J k)) x :=
    fun k x hx => (Hd x ⟨hJ_sub k hx.1, hx.2⟩).hasFDerivWithinAt
  have HiJ : ∀ k, IntegrableOn (∑ i, f' · (e i) i) (Box.Icc (J k)) volume := fun k =>
    Hi.mono_set (hJ_sub' k)
  -- Apply the previous lemma to `J k`.
  have HJ_eq := fun k =>
    integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (J k) f f' s hs (HcJ k) (HdJ k)
      (HiJ k)
  -- Note that the LHS of `HJ_eq k` tends to the LHS of the goal as `k → ∞`.
  have hI_tendsto :
    Tendsto (fun k => ∫ x in Box.Icc (J k), ∑ i, f' x (e i) i) atTop
      (𝓝 (∫ x in Box.Icc I, ∑ i, f' x (e i) i)) := by
    simp only [IntegrableOn, ← Measure.restrict_congr_set (Box.Ioo_ae_eq_Icc _)] at Hi ⊢
    rw [← Box.iUnion_Ioo_of_tendsto J.monotone hJl hJu] at Hi ⊢
    exact tendsto_setIntegral_of_monotone (fun k => (J k).measurableSet_Ioo)
      (Box.Ioo.comp J).monotone Hi
  -- Thus it suffices to prove the same about the RHS.
  refine tendsto_nhds_unique_of_eventuallyEq hI_tendsto ?_ (Eventually.of_forall HJ_eq)
  clear hI_tendsto
  rw [tendsto_pi_nhds] at hJl hJu
  /- We'll need to prove a similar statement about the integrals over the front sides and the
    integrals over the back sides. In order to avoid repeating ourselves, we formulate a lemma. -/
  suffices ∀ (i : Fin (n + 1)) (c : ℕ → ℝ) (d), (∀ k, c k ∈ Icc (I.lower i) (I.upper i)) →
    Tendsto c atTop (𝓝 d) →
      Tendsto (fun k => ∫ x in Box.Icc ((J k).face i), f (i.insertNth (c k) x) i) atTop
        (𝓝 <| ∫ x in Box.Icc (I.face i), f (i.insertNth d x) i) by
    rw [Box.Icc_eq_pi] at hJ_sub'
    refine tendsto_finsetSum _ fun i _ => (this _ _ _ ?_ (hJu _)).sub (this _ _ _ ?_ (hJl _))
    exacts [fun k => hJ_sub' k (J k).upper_mem_Icc _ trivial, fun k =>
      hJ_sub' k (J k).lower_mem_Icc _ trivial]
  intro i c d hc hcd
  /- First we prove that the integrals of the restriction of `f` to `{x | x i = d}` over increasing
    boxes `((J k).face i).Icc` tend to the desired limit. The proof mostly repeats the one above. -/
  have hd : d ∈ Icc (I.lower i) (I.upper i) :=
    isClosed_Icc.mem_of_tendsto hcd (Eventually.of_forall hc)
  have Hic : ∀ k, IntegrableOn (fun x => f (i.insertNth (c k) x) i) (Box.Icc (I.face i)) := fun k =>
    (Box.continuousOn_face_Icc ((continuous_apply i).comp_continuousOn Hc) (hc k)).integrableOn_Icc
  have Hid : IntegrableOn (fun x => f (i.insertNth d x) i) (Box.Icc (I.face i)) :=
    (Box.continuousOn_face_Icc ((continuous_apply i).comp_continuousOn Hc) hd).integrableOn_Icc
  have H :
    Tendsto (fun k => ∫ x in Box.Icc ((J k).face i), f (i.insertNth d x) i) atTop
      (𝓝 <| ∫ x in Box.Icc (I.face i), f (i.insertNth d x) i) := by
    have hIoo : (⋃ k, Box.Ioo ((J k).face i)) = Box.Ioo (I.face i) :=
      Box.iUnion_Ioo_of_tendsto ((Box.monotone_face i).comp J.monotone)
        (tendsto_pi_nhds.2 fun _ => hJl _) (tendsto_pi_nhds.2 fun _ => hJu _)
    simp only [IntegrableOn, ← Measure.restrict_congr_set (Box.Ioo_ae_eq_Icc _), ← hIoo] at Hid ⊢
    exact tendsto_setIntegral_of_monotone (fun k => ((J k).face i).measurableSet_Ioo)
      (Box.Ioo.monotone.comp ((Box.monotone_face i).comp J.monotone)) Hid
  /- Thus it suffices to show that the distance between the integrals of the restrictions of `f` to
    `{x | x i = c k}` and `{x | x i = d}` over `((J k).face i).Icc` tends to zero as `k → ∞`. Choose
    `ε > 0`. -/
  refine H.congr_dist (Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε εpos => ?_)
  have hvol_pos : ∀ J : Box (Fin n), 0 < ∏ j, (J.upper j - J.lower j) := fun J =>
    prod_pos fun j hj => sub_pos.2 <| J.lower_lt_upper _
  /- Choose `δ > 0` such that for any `x y ∈ I.Icc` at distance at most `δ`, the distance between
    `f x` and `f y` is at most `ε / volume (I.face i).Icc`, then the distance between the integrals
    is at most `(ε / volume (I.face i).Icc) * volume ((J k).face i).Icc ≤ ε`. -/
  rcases Metric.uniformContinuousOn_iff_le.1 (I.isCompact_Icc.uniformContinuousOn_of_continuous Hc)
      (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) (div_pos εpos (hvol_pos (I.face i)))
    with ⟨δ, δpos, hδ⟩
  refine (hcd.eventually (Metric.ball_mem_nhds _ δpos)).mono fun k hk => ?_
  have Hsub : Box.Icc ((J k).face i) ⊆ Box.Icc (I.face i) :=
    Box.le_iff_Icc.1 (Box.face_mono (hJ_le _) i)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm,
    ← integral_sub (Hid.mono_set Hsub) ((Hic _).mono_set Hsub)]
  calc
    ‖∫ x in Box.Icc ((J k).face i), f (i.insertNth d x) i - f (i.insertNth (c k) x) i‖ ≤
        (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) *
          (volume (Box.Icc ((J k).face i))).toReal := by
      refine norm_setIntegral_le_of_norm_le_const (((J k).face i).measure_Icc_lt_top _)
        fun x hx => ?_
      rw [← dist_eq_norm]
      calc
        dist (f (i.insertNth d x) i) (f (i.insertNth (c k) x) i) ≤
            dist (f (i.insertNth d x)) (f (i.insertNth (c k) x)) :=
          dist_le_pi_dist (f (i.insertNth d x)) (f (i.insertNth (c k) x)) i
        _ ≤ ε / ∏ j, ((I.face i).upper j - (I.face i).lower j) :=
          hδ _ (I.mapsTo_insertNth_face_Icc hd <| Hsub hx) _
            (I.mapsTo_insertNth_face_Icc (hc _) <| Hsub hx) ?_
      rw [Fin.dist_insertNth_insertNth, dist_self, dist_comm]
      exact max_le hk.le δpos.lt.le
    _ ≤ ε := by
      rw [Box.Icc_def, Real.volume_Icc_pi_toReal ((J k).face i).lower_le_upper,
        ← le_div_iff₀ (hvol_pos _)]
      gcongr
      exacts [hvol_pos _, fun _ _ ↦ sub_nonneg.2 (Box.lower_le_upper _ _),
        (hJ_sub' _ (J _).upper_mem_Icc).2 _, (hJ_sub' _ (J _).lower_mem_Icc).1 _]

variable (a b : Fin (n + 1) → ℝ)

local notation "face " i => Set.Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i)
local notation:max "frontFace " i:arg => Fin.insertNth i (b i)
local notation:max "backFace " i:arg => Fin.insertNth i (a i)

/-- **Divergence theorem** for Bochner integral. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is continuous on a rectangular
box `[a, b] : Set ℝⁿ⁺¹`, `a ≤ b`, is differentiable on its interior with derivative
`f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the divergence `fun x ↦ ∑ i, f' x eᵢ i` is integrable on `[a, b]`,
where `eᵢ = Pi.single i 1` is the `i`-th basis vector, then its integral is equal to the sum of
integrals of `f` over the faces of `[a, b]`, taken with appropriate signs.

Moreover, the same is true if the function is not differentiable at countably many
points of the interior of `[a, b]`.

We represent both faces `x i = a i` and `x i = b i` as the box
`face i = [a ∘ Fin.succAbove i, b ∘ Fin.succAbove i]` in `ℝⁿ`, where
`Fin.succAbove : Fin n ↪o Fin (n + 1)` is the order embedding with range `{i}ᶜ`. The restrictions
of `f : ℝⁿ⁺¹ → Eⁿ⁺¹` to these faces are given by `f ∘ backFace i` and `f ∘ frontFace i`, where
`backFace i = Fin.insertNth i (a i)` and `frontFace i = Fin.insertNth i (b i)` are embeddings
`ℝⁿ → ℝⁿ⁺¹` that take `y : ℝⁿ` and insert `a i` (resp., `b i`) as `i`-th coordinate. -/
/-
**MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_divergence_of_hasFDerivAt_off_countable (hle : a <= b) (f : Realⁿ
⁺¹ -> Eⁿ⁺¹) (f' : Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] Eⁿ⁺¹) (s : Set Realⁿ⁺¹) (hs : s.C
ountable) (Hc : ContinuousOn f (Icc a b)) (Hd : forall x in (Set.pi univ fun i =
> Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x) (Hi : IntegrableOn (fun x => ∑ i
, f' x (e i) i) (Icc a b)) : (∫ x in Icc a b, ∑ i, f' x (e i) i) = ∑ i : Fin (n 
+ 1), ((∫ x in face i, f (frontFace i x) i) - ∫ x in face i, f (backFace i x) i)
参数：hle : a <= b；f : Realⁿ⁺¹ -> Eⁿ⁺¹；f' : Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] Eⁿ⁺¹；s : S
et Realⁿ⁺¹；hs : s.Countable；Hc : ContinuousOn f (Icc a b)；Hd : forall x in (Set.
pi univ fun i => Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x；Hi : IntegrableOn 
(fun x => ∑ i, f' x (e i) i) (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.volume_pi`：volume_pi [forall i, MeasureSpace (α i)] : (vol
ume : Measure (forall i, α i)) = Measure.pi fun _ => volume
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc`：univ_pi_Ioc_ae_eq_Icc {f g 
: forall i, α i} : (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Set.univ_pi_eq_empty`：univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅
· 使用定理 `MeasureTheory.setIntegral_empty`：setIntegral_empty : ∫ x in ∅, f x ∂μ = 
0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fin.exists_succAbove_eq`：exists_succAbove_eq {x y : Fin (n + 1)} (h : x 
!= y) : exists z, y.succAbove z = x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Divergence theorem** for Bochner integral. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is continuous 
on a rectangular
box `[a, b] : Set ℝⁿ⁺¹`, `a ≤ b`, is differentiable on its interior with derivat
ive
`f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the divergence `fun x ↦ ∑ i, f' x eᵢ i` is int
egrable on `[a, b]`,
where `eᵢ = Pi.single i 1` is the `i`-th basis vector, then its integral is equa
l to the sum of
integrals of `f` over the faces of `[a, b]`, taken with appropriate signs.

Moreover, the same is true if the function is not differentiable at countably ma
ny
points of the interior of `[a, b]`.

We represent both faces `x i = a i` and `x i = b i` as the box
`face i = [a ∘ Fin.succAbove i, b ∘ Fin.succAbove i]` in `ℝⁿ`, where
`Fin.succAbove : Fin n ↪o Fin (n + 1)` is the order embedding with range `{i}ᶜ`.
 The restrictions
of `f : ℝⁿ⁺¹ → Eⁿ⁺¹` to these faces are given by `f ∘ backFace i` and `f ∘ front
Face i`, where
`backFace i = Fin.insertNth i (a i)` and `frontFace i = Fin.insertNth i (b i)` a
re embeddings
`ℝⁿ → ℝⁿ⁺¹` that take `y : ℝⁿ` and insert `a i` (resp., `b i`) as `i`-th coordin
ate.
-/
theorem integral_divergence_of_hasFDerivAt_off_countable (hle : a ≤ b)
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹)
    (s : Set ℝⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ (Set.pi univ fun i => Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in face i, f (frontFace i x) i) - ∫ x in face i, f (backFace i x) i) := by
  rcases em (∃ i, a i = b i) with (⟨i, hi⟩ | hne)
  · -- First we sort out the trivial case `∃ i, a i = b i`.
    rw [volume_pi, ← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc]
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt
    have : (pi Set.univ fun j => Ioc (a j) (b j)) = ∅ := univ_pi_eq_empty hi'
    rw [this, setIntegral_empty, sum_eq_zero]
    rintro j -
    rcases eq_or_ne i j with (rfl | hne)
    · simp [hi]
    · rcases Fin.exists_succAbove_eq hne with ⟨i, rfl⟩
      have : Icc (a ∘ j.succAbove) (b ∘ j.succAbove) =ᵐ[volume] (∅ : Set ℝⁿ) := by
        rw [ae_eq_empty, Real.volume_Icc_pi, prod_eq_zero (Finset.mem_univ i)]
        simp [hi]
      rw [setIntegral_congr_set this, setIntegral_congr_set this, setIntegral_empty,
        setIntegral_empty, sub_self]
  · -- In the non-trivial case `∀ i, a i < b i`, we apply a lemma we proved above.
    have hlt : ∀ i, a i < b i := fun i => (hle i).lt_of_ne fun hi => hne ⟨i, hi⟩
    exact integral_divergence_of_hasFDerivAt_off_countable_aux₂ ⟨a, b, hlt⟩ f f' s hs Hc Hd Hi

/-- **Divergence theorem** for a family of functions `f : Fin (n + 1) → ℝⁿ⁺¹ → E`. See also
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` for a version formulated
in terms of a vector-valued function `f : ℝⁿ⁺¹ → Eⁿ⁺¹`. -/
/-
**MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_divergence_of_hasFDerivAt_off_countable' (hle : a <= b) (f : Fin 
(n + 1) -> Realⁿ⁺¹ -> E) (f' : Fin (n + 1) -> Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] E) (s
 : Set Realⁿ⁺¹) (hs : s.Countable) (Hc : forall i, ContinuousOn (f i) (Icc a b))
 (Hd : forall x in (pi Set.univ fun i => Ioo (a i) (b i)) \ s, forall (i), HasFD
erivAt (f i) (f' i x) x) (Hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a 
b)) : (∫ x in Icc a b, ∑ i, f' i x (e i)) = ∑ i : Fin (n + 1), ((∫ x in face i, 
f i (frontFace i x)) - ∫ x
参数：hle : a <= b；f : Fin (n + 1) -> Realⁿ⁺¹ -> E；f' : Fin (n + 1) -> Realⁿ⁺¹ -> R
ealⁿ⁺¹ ->L[Real] E；s : Set Realⁿ⁺¹；hs : s.Countable；Hc : forall i, ContinuousOn 
(f i) (Icc a b)；Hd : forall x in (pi Set.univ fun i => Ioo (a i) (b i)) \ s, for
all (i), HasFDerivAt (f i) (f' i x) x；Hi : IntegrableOn (fun x => ∑ i, f' i x (e
 i)) (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`：integral
_divergence_of_hasFDerivAt_off_countable (hle : a <= b) (f : Realⁿ⁺¹ -> Eⁿ⁺¹) (f
' : Realⁿ⁺¹ -> Realⁿ⁺¹ ->L[Real] Eⁿ⁺¹) (s : Set Real…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_pi`：continuousOn_pi {ι : Type*} {X : ι -> Type*} [forall i,
 TopologicalSpace (X i)] {f : α -> forall i, X i} {s : Set α} : ContinuousOn f s
 ↔ fo…
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x

--- 原说明 ---
**Divergence theorem** for a family of functions `f : Fin (n + 1) → ℝⁿ⁺¹ → E`. S
ee also
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` for a version 
formulated
in terms of a vector-valued function `f : ℝⁿ⁺¹ → Eⁿ⁺¹`.
-/
theorem integral_divergence_of_hasFDerivAt_off_countable' (hle : a ≤ b)
    (f : Fin (n + 1) → ℝⁿ⁺¹ → E)
    (f' : Fin (n + 1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E) (s : Set ℝⁿ⁺¹)
    (hs : s.Countable) (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ (pi Set.univ fun i => Ioo (a i) (b i)) \ s, ∀ (i), HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' i x (e i)) =
      ∑ i : Fin (n + 1), ((∫ x in face i, f i (frontFace i x)) -
        ∫ x in face i, f i (backFace i x)) :=
  integral_divergence_of_hasFDerivAt_off_countable a b hle (fun x i => f i x)
    (fun x => ContinuousLinearMap.pi fun i => f' i x) s hs (continuousOn_pi.2 Hc)
    (fun x hx => hasFDerivAt_pi.2 (Hd x hx)) Hi

end

/-- An auxiliary lemma that is used to specialize the general divergence theorem to spaces that do
not have the form `Fin n → ℝ`. -/
/-
**MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_divergence_of_hasFDerivAt_off_countable_of_equiv {F : Type*} [Nor
medAddCommGroup F] [NormedSpace Real F] [Preorder F] [MeasureSpace F] [BorelSpac
e F] (eL : F ≃L[Real] Realⁿ⁺¹) (he_ord : forall x y, eL x <= eL y ↔ x <= y) (he_
vol : MeasurePreserving eL volume volume) (f : Fin (n + 1) -> F -> E) (f' : Fin 
(n + 1) -> F -> F ->L[Real] E) (s : Set F) (hs : s.Countable) (a b : F) (hle : a
 <= b) (Hc : forall i, ContinuousOn (f i) (Icc a b)) (Hd : forall x in interior 
(Icc a b) \ s, forall (i),
参数：eL : F ≃L[Real] Realⁿ⁺¹；he_ord : forall x y, eL x <= eL y ↔ x <= y；he_vol : M
easurePreserving eL volume volume；f : Fin (n + 1) -> F -> E；f' : Fin (n + 1) -> 
F -> F ->L[Real] E；s : Set F；hs : s.Countable；a b : F；hle : a <= b；Hc : forall i
, ContinuousOn (f i) (Icc a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.symm_preimage_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.setIntegral_preimage_emb`：∀ {X : Type u_
1} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1
 : NormedSpace ℝ E]   {μ : MeasureTheory.Measu…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`：integra
l_divergence_of_hasFDerivAt_off_countable' (hle : a <= b) (f : Fin (n + 1) -> Re
alⁿ⁺¹ -> E) (f' : Fin (n + 1) -> Realⁿ⁺¹ -> Realⁿ⁺¹ -…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Countable.preimage`：∀ {α : Type u} {β : Type v} {s : Set β}, s.Count
able → ∀ {f : α → β}, Function.Injective f → (f ⁻¹' s).Countable
· 使用定理 `ContinuousLinearEquiv.injective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `ContinuousLinearEquiv.continuousOn`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [i
nst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   
[inst_2 : RingHomInvPair…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `interior_pi_set`：interior_pi_set {I : Set ι} (hI : I.Finite) {s : forall
 i, Set (A i)} : interior (pi I s) = I.pi fun i => interior (s i)
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
An auxiliary lemma that is used to specialize the general divergence theorem to 
spaces that do
not have the form `Fin n → ℝ`.
-/
theorem integral_divergence_of_hasFDerivAt_off_countable_of_equiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Preorder F] [MeasureSpace F] [BorelSpace F]
    (eL : F ≃L[ℝ] ℝⁿ⁺¹) (he_ord : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
    (he_vol : MeasurePreserving eL volume volume) (f : Fin (n + 1) → F → E)
    (f' : Fin (n + 1) → F → F →L[ℝ] E) (s : Set F) (hs : s.Countable) (a b : F) (hle : a ≤ b)
    (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ interior (Icc a b) \ s, ∀ (i), HasFDerivAt (f i) (f' i x) x) (DF : F → E)
    (hDF : ∀ x, DF x = ∑ i, f' i x (eL.symm <| e i)) (Hi : IntegrableOn DF (Icc a b)) :
    ∫ x in Icc a b, DF x =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL b i) x)) -
          ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL a i) x)) :=
  have he_emb : MeasurableEmbedding eL := eL.toHomeomorph.measurableEmbedding
  have hIcc : eL ⁻¹' Icc (eL a) (eL b) = Icc a b := by
    ext1 x; simp only [Set.mem_preimage, Set.mem_Icc, he_ord]
  have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' Icc a b := by rw [← hIcc, eL.symm_preimage_preimage]
  calc
    ∫ x in Icc a b, DF x = ∫ x in Icc a b, ∑ i, f' i x (eL.symm <| e i) := by simp only [hDF]
    _ = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm <| e i) := by
      rw [← he_vol.setIntegral_preimage_emb he_emb]
      simp only [hIcc, eL.symm_apply_apply]
    _ = ∑ i : Fin (n + 1),
          ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL b i) x)) -
            ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL a i) x)) := by
      refine integral_divergence_of_hasFDerivAt_off_countable' (eL a) (eL b)
        ((he_ord _ _).2 hle) (fun i x => f i (eL.symm x))
        (fun i x => f' i (eL.symm x) ∘L (eL.symm : ℝⁿ⁺¹ →L[ℝ] F)) (eL.symm ⁻¹' s)
        (hs.preimage eL.symm.injective) ?_ ?_ ?_
      · exact fun i => (Hc i).comp eL.symm.continuousOn hIcc'.subset
      · refine fun x hx i => (Hd (eL.symm x) ⟨?_, hx.2⟩ i).comp x eL.symm.hasFDerivAt
        rw [← hIcc]
        refine preimage_interior_subset_interior_preimage eL.continuous ?_
        simpa only [Set.mem_preimage, eL.apply_symm_apply, ← pi_univ_Icc,
          interior_pi_set (@finite_univ (Fin _) _), interior_Icc] using hx.1
      · rw [← he_vol.integrableOn_comp_preimage he_emb, hIcc]
        simp [← hDF, Function.comp_def, Hi]

end

open scoped Interval

open ContinuousLinearMap (smulRight)


local macro:arg t:term:max noWs "¹" : term => `(Fin 1 → $t)
local macro:arg t:term:max noWs "²" : term => `(Fin 2 → $t)

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is continuous on the
interval and is differentiable off a countable set `s`.

See also

* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` for a version that only assumes right
  differentiability of `f`;
* `MeasureTheory.integral_eq_of_hasDerivWithinAt_off_countable` for a version that works both
  for `a ≤ b` and `b ≤ a` at the expense of using unordered intervals instead of `Set.Icc`. -/
/-
**MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq_of_hasDerivAt_off_countable_of_le [CompleteSpace E] (f f' : Re
al -> E) {a b : Real} (hle : a <= b) {s : Set Real} (hs : s.Countable) (Hc : Con
tinuousOn f (Icc a b)) (Hd : forall x in Ioo a b \ s, HasDerivAt f (f' x) x) (Hi
 : IntervalIntegrable f' volume a b) : ∫ x in a..b, f' x = f b - f a
参数：f f' : Real -> E；hle : a <= b；hs : s.Countable；Hc : ContinuousOn f (Icc a b)；
Hd : forall x in Ioo a b \ s, HasDerivAt f (f' x) x；Hi : IntervalIntegrable f' v
olume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
· 使用定理 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv`
：integral_divergence_of_hasFDerivAt_off_countable_of_equiv {F : Type*} [NormedAd
dCommGroup F] [NormedSpace Real F] [Preorder F] [MeasureSpace…
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.volume_preserving_funUnique`：volume_preserving_funUnique (
α : Type u) (β : Type v) [Unique α] [MeasureSpace β] : MeasurePreserving (Measur
ableEquiv.funUnique α β) volume…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
**Fundamental theorem of calculus, part 2**. This version assumes that `f` is co
ntinuous on the
interval and is differentiable off a countable set `s`.

See also

* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` for a version that 
only assumes right
  differentiability of `f`;
* `MeasureTheory.integral_eq_of_hasDerivWithinAt_off_countable` for a version th
at works both
  for `a ≤ b` and `b ≤ a` at the expense of using unordered intervals instead of
 `Set.Icc`.
-/
theorem integral_eq_of_hasDerivAt_off_countable_of_le [CompleteSpace E] (f f' : ℝ → E)
    {a b : ℝ} (hle : a ≤ b) {s : Set ℝ} (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f (f' x) x) (Hi : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  set e : ℝ ≃L[ℝ] ℝ¹ := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  set F' : ℝ → ℝ →L[ℝ] E := fun x => smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  calc
    ∫ x in a..b, f' x = ∫ x in Icc a b, f' x := by
      rw [intervalIntegral.integral_of_le hle, setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∑ i : Fin 1,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e a i) x)) := by
      simp only [← interior_Icc] at Hd
      refine
        integral_divergence_of_hasFDerivAt_off_countable_of_equiv e ?_ ?_ (fun _ => f)
          (fun _ => F') s hs a b hle (fun _ => Hc) (fun x hx _ => Hd x hx) _ ?_ ?_
      · exact fun x y => (OrderIso.funUnique (Fin 1) ℝ).symm.le_iff_le
      · exact (volume_preserving_funUnique (Fin 1) ℝ).symm _
      · simp [F', e]
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at Hi
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm
    _ = f b - f a := by
      simp [e, Subsingleton.elim (const (Fin 0) _) isEmptyElim, volume_pi,
        Measure.pi_of_empty fun _ : Fin 0 ↦ _]

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is continuous on the
interval and is differentiable off a countable set `s`.

See also `intervalIntegral.integral_eq_sub_of_hasDeriv_right` for a version that
only assumes right differentiability of `f`.
-/
/-
**MeasureTheory.integral_eq_of_hasDerivAt_off_countable** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_eq_of_hasDerivAt_off_countable [CompleteSpace E] (f f' : Real -> 
E) {a b : Real} {s : Set Real} (hs : s.Countable) (Hc : ContinuousOn f [[a, b]])
 (Hd : forall x in Ioo (min a b) (max a b) \ s, HasDerivAt f (f' x) x) (Hi : Int
ervalIntegrable f' volume a b) : ∫ x in a..b, f' x = f b - f a
参数：f f' : Real -> E；hs : s.Countable；Hc : ContinuousOn f [[a, b]]；Hd : forall x 
in Ioo (min a b) (max a b) \ s, HasDerivAt f (f' x) x；Hi : IntervalIntegrable f'
 volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`：integral_eq
_of_hasDerivAt_off_countable_of_le [CompleteSpace E] (f f' : Real -> E) {a b : R
eal} (hle : a <= b) {s : Set Real} (hs : s.Counta…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…

--- 原说明 ---
**Fundamental theorem of calculus, part 2**. This version assumes that `f` is co
ntinuous on the
interval and is differentiable off a countable set `s`.

See also `intervalIntegral.integral_eq_sub_of_hasDeriv_right` for a version that
only assumes right differentiability of `f`.
-/
theorem integral_eq_of_hasDerivAt_off_countable [CompleteSpace E] (f f' : ℝ → E) {a b : ℝ}
    {s : Set ℝ} (hs : s.Countable) (Hc : ContinuousOn f [[a, b]])
    (Hd : ∀ x ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' x) x)
    (Hi : IntervalIntegrable f' volume a b) : ∫ x in a..b, f' x = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
    exact integral_eq_of_hasDerivAt_off_countable_of_le f f' hab hs Hc Hd Hi
  · simp only [uIcc_of_ge hab, min_eq_right hab, max_eq_left hab] at *
    rw [intervalIntegral.integral_symm, neg_eq_iff_eq_neg, neg_sub]
    exact integral_eq_of_hasDerivAt_off_countable_of_le f f' hab hs Hc Hd Hi.symm

/-- **Divergence theorem** for functions on the plane along rectangles. It is formulated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle equals the integral of the normal derivative of `F` along the
boundary.

See also `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable` for a
version that does not assume `a ≤ b` and uses iterated interval integral instead of the integral
over `Icc a b`. -/
/-
**MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (f g : Rea
l × Real -> E) (f' g' : Real × Real -> Real × Real ->L[Real] E) (a b : Real × Re
al) (hle : a <= b) (s : Set (Real × Real)) (hs : s.Countable) (Hcf : ContinuousO
n f (Icc a b)) (Hcg : ContinuousOn g (Icc a b)) (Hdf : forall x in Ioo a.1 b.1 ×
ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x) (Hdg : forall x in Ioo a.1 b.1 ×ˢ Ioo
 a.2 b.2 \ s, HasFDerivAt g (g' x) x) (Hi : IntegrableOn (fun x => f' x (1, 0) +
 g' x (0, 1)) (Icc a b)) :
参数：f g : Real × Real -> E；f' g' : Real × Real -> Real × Real ->L[Real] E；a b : R
eal × Real；hle : a <= b；s : Set (Real × Real)；hs : s.Countable；Hcf : ContinuousO
n f (Icc a b)；Hcg : ContinuousOn g (Icc a b)；Hdf : forall x in Ioo a.1 b.1 ×ˢ Io
o a.2 b.2 \ s, HasFDerivAt f (f' x) x；Hdg : forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b
.2 \ s, HasFDerivAt g (g' x) x；Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0
, 1)) (Icc a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv`
：integral_divergence_of_hasFDerivAt_off_countable_of_equiv {F : Type*} [NormedAd
dCommGroup F] [NormedSpace Real F] [Preorder F] [MeasureSpace…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.volume_preserving_finTwoArrow`：volume_preserving_finTwoArr
ow (α : Type u) [MeasureSpace α] [SigmaFinite (volume : Measure α)] : MeasurePre
serving (@MeasurableEquiv.finTwoA…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.forall_fin_two`：∀ {p : Fin 2 → Prop}, (∀ (i : Fin 2), p i) ↔ p 0 ∧ p
 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `interior_prod_eq`：interior_prod_eq (s : Set X) (t : Set Y) : interior (s
 ×ˢ t) = interior s ×ˢ interior t
· 使用定理 `Set.Icc_prod_eq`：Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Ic
c a.2 b.2
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
**Divergence theorem** for functions on the plane along rectangles. It is formul
ated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.
2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a
 single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integ
ral of the
divergence of `F` inside the rectangle equals the integral of the normal derivat
ive of `F` along the
boundary.

See also `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable` 
for a
version that does not assume `a ≤ b` and uses iterated interval integral instead
 of the integral
over `Icc a b`.
-/
theorem integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) -
        ∫ y in a.2..b.2, f (a.1, y) :=
  let e : (ℝ × ℝ) ≃L[ℝ] ℝ² := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  calc
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
        ∑ i : Fin 2,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e a i) x)) := by
      refine integral_divergence_of_hasFDerivAt_off_countable_of_equiv e ?_ ?_ ![f, g]
        ![f', g'] s hs a b hle ?_ (fun x hx => ?_) _ ?_ Hi
      · exact fun x y => (OrderIso.finTwoArrowIso ℝ).symm.le_iff_le
      · exact (volume_preserving_finTwoArrow ℝ).symm _
      · exact Fin.forall_fin_two.2 ⟨Hcf, Hcg⟩
      · rw [Icc_prod_eq, interior_prod_eq, interior_Icc, interior_Icc] at hx
        exact Fin.forall_fin_two.2 ⟨Hdf x hx, Hdg x hx⟩
      · intro x; rw [Fin.sum_univ_two]; rfl
    _ = ((∫ y in Icc a.2 b.2, f (b.1, y)) - ∫ y in Icc a.2 b.2, f (a.1, y)) +
          ((∫ x in Icc a.1 b.1, g (x, b.2)) - ∫ x in Icc a.1 b.1, g (x, a.2)) := by
      have : ∀ (a b : ℝ¹) (f : ℝ¹ → E),
          ∫ x in Icc a b, f x = ∫ x in Icc (a 0) (b 0), f fun _ => x := fun a b f ↦ by
        convert!
          (((volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
              (MeasurableEquiv.measurableEmbedding _) f _).symm
        exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc a b).symm
      simp only [Fin.sum_univ_two, this]
      rfl
    _ = (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
            ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) := by
      simp only [intervalIntegral.integral_of_le hle.1, intervalIntegral.integral_of_le hle.2,
        setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
      abel

/-- **Divergence theorem** for functions on the plane along rectangles. It is formulated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle equals the integral of the normal derivative of `F` along the
boundary.

See also `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` for a
version that does not assume `a ≤ b` and uses iterated interval integral instead of the integral
over `Icc a b`.

See also `integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`
for a version that assumes differentiability out of a countable set. -/
/-
**MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_divergence_prod_Icc_of_hasFDerivAt_of_le (f g : Real × Real -> E)
 (f' g' : Real × Real -> Real × Real ->L[Real] E) (a b : Real × Real) (hle : a <
= b) (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b)) (Hdf : fo
rall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt f (f' x) x) (Hdg : forall x in
 Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt g (g' x) x) (Hi : IntegrableOn (fun x =
> f' x (1, 0) + g' x (0, 1)) (Icc a b)) : (∫ x in Icc a b, f' x (1, 0) + g' x (0
, 1)) = (((∫ x in a.1..b.1
参数：f g : Real × Real -> E；f' g' : Real × Real -> Real × Real ->L[Real] E；a b : R
eal × Real；hle : a <= b；Hcf : ContinuousOn f (Icc a b)；Hcg : ContinuousOn g (Icc
 a b)；Hdf : forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt f (f' x) x；Hdg :
 forall x in Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt g (g' x) x；Hi : IntegrableO
n (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_
of_le`：integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (f g : Re
al × Real -> E) (f' g' : Real × Real -> Real × Real ->L[Real] E) (a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s

--- 原说明 ---
**Divergence theorem** for functions on the plane along rectangles. It is formul
ated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.
2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a
 single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integ
ral of the
divergence of `F` inside the rectangle equals the integral of the normal derivat
ive of `F` along the
boundary.

See also `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt` for a
version that does not assume `a ≤ b` and uses iterated interval integral instead
 of the integral
over `Icc a b`.

See also `integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`
for a version that assumes differentiability out of a countable set.
-/
theorem integral_divergence_prod_Icc_of_hasFDerivAt_of_le (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :=
  integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le f g f' g' a b hle ∅
    (by simp) Hcf Hcg (by simpa only [sdiff_empty]) (by simpa only [sdiff_empty]) Hi

/-- **Divergence theorem** for functions on the plane. It is formulated in terms of two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j =1,2`, equals the integral of
the normal derivative of `F` along the boundary.

See also `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`. -/
/-
**MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral2_divergence_prod_of_hasFDerivAt_off_countable (f g : Real × Real 
-> E) (f' g' : Real × Real -> Real × Real ->L[Real] E) (a₁ a₂ b₁ b₂ : Real) (s :
 Set (Real × Real)) (hs : s.Countable) (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂
, b₂]])) (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) (Hdf : forall x in Io
o (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s, HasFDerivAt f (f' 
x) x) (Hdg : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ 
b₂) \ s, HasFDerivAt g (g'
参数：f g : Real × Real -> E；f' g' : Real × Real -> Real × Real ->L[Real] E；a₁ a₂ b
₁ b₂ : Real；s : Set (Real × Real)；hs : s.Countable；Hcf : ContinuousOn f ([[a₁, b
₁]] ×ˢ [[a₂, b₂]])；Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]])；Hdf : forall 
x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s, HasFDerivAt
 f (f' x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_prod`：setIntegral_prod (f : α × β -> E) {s : S
et α} {t : Set β} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) : ∫ z in s ×ˢ t, f z
 ∂μ.prod ν = ∫ x in …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_prod_Icc`：Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Ic
c b₁ b₂ = Icc (a₁, b₁) (a₂, b₂)
· 使用定理 `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_
of_le`：integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (f g : Re
al × Real -> E) (f' g' : Real × Real -> Real × Real ->L[Real] E) (a…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
**Divergence theorem** for functions on the plane. It is formulated in terms of 
two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a sing
le function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integ
ral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j =1,2`, eq
uals the integral of
the normal derivative of `F` along the boundary.

See also `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countabl
e_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`
.
-/
theorem integral2_divergence_prod_of_hasFDerivAt_off_countable (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a₁ a₂ b₁ b₂ : ℝ) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hdf : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
      HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
      HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) := by
  wlog h₁ : a₁ ≤ b₁ generalizing a₁ b₁
  · specialize this b₁ a₁
    rw [uIcc_comm b₁ a₁, min_comm b₁ a₁, max_comm b₁ a₁] at this
    simp only [intervalIntegral.integral_symm b₁ a₁]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_ge h₁))).trans ?_; abel
  wlog h₂ : a₂ ≤ b₂ generalizing a₂ b₂
  · specialize this b₂ a₂
    rw [uIcc_comm b₂ a₂, min_comm b₂ a₂, max_comm b₂ a₂] at this
    simp only [intervalIntegral.integral_symm b₂ a₂, intervalIntegral.integral_neg]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_ge h₂))).trans ?_; abel
  simp only [uIcc_of_le h₁, uIcc_of_le h₂, min_eq_left, max_eq_right, h₁, h₂] at Hcf Hcg Hdf Hdg Hi
  calc
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
        ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) := by
      simp only [intervalIntegral.integral_of_le, h₁, h₂,
        setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    _ = ∫ x in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f' x (1, 0) + g' x (0, 1) := (setIntegral_prod _ Hi).symm
    _ = (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
          ∫ y in a₂..b₂, f (a₁, y) := by
      rw [Icc_prod_Icc] at *
      apply integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le f g f' g'
        (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩ s <;> assumption

/-- **Divergence theorem** for functions on the plane. It is formulated in terms of two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j = 1, 2`,
equals the integral of the normal derivative of `F` along the boundary.

See also `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`.

See also `integral2_divergence_prod_of_hasFDerivAt_off_countable`
for a version that assumes differentiability outside of a countable set. -/
/-
**MeasureTheory.integral2_divergence_prod_of_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：integral2_divergence_prod_of_hasFDerivAt (f g : Real × Real -> E) (f' g' :
 Real × Real -> Real × Real ->L[Real] E) (a₁ a₂ b₁ b₂ : Real) (Hcf : ContinuousO
n f ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]])
) (Hdf : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
 HasFDerivAt f (f' x) x) (Hdg : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (
min a₂ b₂) (max a₂ b₂), HasFDerivAt g (g' x) x) (Hi : IntegrableOn (fun x => f' 
x (1, 0) + g' x (0, 1)) ([
参数：f g : Real × Real -> E；f' g' : Real × Real -> Real × Real ->L[Real] E；a₁ a₂ b
₁ b₂ : Real；Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]])；Hcg : ContinuousOn g
 ([[a₁, b₁]] ×ˢ [[a₂, b₂]])；Hdf : forall x in Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo
 (min a₂ b₂) (max a₂ b₂), HasFDerivAt f (f' x) x；Hdg : forall x in Ioo (min a₁ b
₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂), HasFDerivAt g (g' x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable`：in
tegral2_divergence_prod_of_hasFDerivAt_off_countable (f g : Real × Real -> E) (f
' g' : Real × Real -> Real × Real ->L[Real] E) (a₁ a₂ b₁ b…
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
**Divergence theorem** for functions on the plane. It is formulated in terms of 
two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a sing
le function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integ
ral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j = 1, 2`,
equals the integral of the normal derivative of `F` along the boundary.

See also `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`
.

See also `integral2_divergence_prod_of_hasFDerivAt_off_countable`
for a version that assumes differentiability outside of a countable set.
-/
theorem integral2_divergence_prod_of_hasFDerivAt (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a₁ a₂ b₁ b₂ : ℝ)
    (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hdf : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) :=
  integral2_divergence_prod_of_hasFDerivAt_off_countable f g f' g' a₁ a₂ b₁ b₂ ∅ countable_empty
    Hcf Hcg (fun x hx ↦ Hdf x hx.1) (fun x hx ↦ Hdg x hx.1) Hi

end MeasureTheory

