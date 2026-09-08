/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Fernique's theorem for rotation-invariant measures

Let `μ` be a finite measure on a second-countable normed space `E` such that the product measure
`μ.prod μ` on `E × E` is invariant by rotation of angle `-π/4`.
Then there exists a constant `C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable
with respect to `μ`.

## Sketch of the proof

The main case of the proof is for `μ` a probability measure such that there exists a positive
`a : ℝ` such that `2⁻¹ < μ {x | ‖x‖ ≤ a} < 1`. If `μ` is a probability measure and `a` does not
exist then we can show that there is a ball with finite radius of measure 1, and the result is true
for `C = 1` (for example), since `x ↦ exp (‖x‖ ^ 2)` is almost surely bounded.
We then choose such an `a`.

In order to show the existence of `C` such that `x ↦ exp (C * ‖x‖ ^ 2)` is integrable, we prove as
intermediate result that for `a, c` with `2⁻¹ < c ≤ μ {x | ‖x‖ ≤ a}`,
the integral `∫⁻ x, exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2) ∂μ` is bounded by a finite quantity
(`logRatio c` is a multiple of `log (c / (1 - c))`). We can then take `C = logRatio c * a⁻¹ ^ 2`.

We now turn to the proof of the intermediate result.

First in `measure_le_mul_measure_gt_le_of_map_rotation_eq_self` we prove that if a measure `μ` is
such that `μ.prod μ` is invariant by rotation of angle `-π/4` then
`μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖} ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2`.
The rotation invariance is used only through that inequality.

We define a sequence of thresholds `t n` inductively by `t 0 = a` and `t (n + 1) = √2 * t n + a`.
They are chosen such that the invariance by rotation gives
`μ {x | ‖x‖ ≤ a} * μ {x | t (n + 1) < ‖x‖} ≤ μ {x | t n < ‖x‖} ^ 2`.
Thanks to that inequality we can show that `μ {x | t n < ‖x‖}` decreases fast with `n`:
for `mₐ = μ {x | ‖x‖ ≤ a}`, `μ {x | t n < ‖x‖} ≤ mₐ * exp (- log (mₐ / (1 - mₐ)) * 2 ^ n)`.

We cut the space into annuli `{x | t n < ‖x‖ ≤ t n + 1}` and bound the integral separately on
each annulus. On that set the function `exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)` is bounded by
`exp (logRatio c * a⁻¹ ^ 2 * t (n + 1) ^ 2)`, which is in turn less than
`exp (2⁻¹ * log (c / (1 - c)) * 2 ^ n)` (from the definition of the threshold `t` and `logRatio c`).
The measure of the annulus is bounded by `μ {x | t n < ‖x‖}`, for which we derived an upper bound
above. The function gets exponentially large, but `μ {x | t n < ‖x‖}` decreases even faster, so the
integral is bounded by a quantity of the form `exp (- u * 2 ^ n)` for `u>0`.
Summing over all annuli (over `n`) gives a finite value for the integral.

## Main statements

* `lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self`: for `μ` a probability measure
  whose product with itself is invariant by rotation and for `a, c` with
  `2⁻¹ < c ≤ μ {x | ‖x‖ ≤ a}`, the integral `∫⁻ x, exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2) ∂μ`
  is bounded by a quantity that does not depend on `a`.
* `exists_integrable_exp_sq_of_map_rotation_eq_self`: Fernique's theorem for finite measures
  whose product is invariant by rotation.

## References

* [Xavier Fernique, *Intégrabilité des vecteurs gaussiens*][fernique1970integrabilite]
* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

## TODO

From the intermediate result `lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self`,
we can deduce bounds on all the moments of the measure `μ` as function of powers of
the first moment.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex NormedSpace Filter
open scoped ENNReal NNReal Real Topology

section Aux

/-
**StrictMono.exists_between_of_tendsto_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.exists_between_of_tendsto_atTop {β : Type*} [LinearOrder β] {t 
: Nat -> β} (ht_mono : StrictMono t) (ht_tendsto : Tendsto t atTop atTop) {x : β
} (hx : t 0 < x) : exists n, t n < x ∧ x <= t (n + 1)
参数：ht_mono : StrictMono t；ht_tendsto : Tendsto t atTop atTop；hx : t 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_iff_of_monotone`：tendsto_atTop_atTop_iff_of_m
onotone (hf : Monotone f) : Tendsto f atTop atTop ↔ forall b : β, exists a, b <=
 f a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
lemma StrictMono.exists_between_of_tendsto_atTop {β : Type*} [LinearOrder β] {t : ℕ → β}
    (ht_mono : StrictMono t) (ht_tendsto : Tendsto t atTop atTop) {x : β} (hx : t 0 < x) :
    ∃ n, t n < x ∧ x ≤ t (n + 1) := by
  have h : ∃ n, x ≤ t n := by
    simp only [tendsto_atTop_atTop_iff_of_monotone ht_mono.monotone] at ht_tendsto
    exact ht_tendsto x
  have h' m := Nat.find_min h (m := m)
  simp only [not_le] at h'
  exact ⟨Nat.find h - 1, h' _ (by simp [hx]), by simp [Nat.find_spec h, hx]⟩

end Aux

namespace ProbabilityTheory

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rotation in `E × E` with angle `θ`, as a continuous linear map. -/
noncomputable
/-
**ProbabilityTheory._root_.ContinuousLinearMap.rotation** 是 Mathlib 中的一个定义，位于命名空
间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.ContinuousLinearMap.rotation (θ : ℝ) : E × E →L[ℝ] E × E where
  toFun := fun x ↦ (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2)
  map_add' x y := by
    simp only [Prod.fst_add, smul_add, Prod.snd_add, neg_smul, Prod.mk_add_mk]
    abel_nf
  map_smul' c x := by simp [smul_comm c]
/-
**ProbabilityTheory._root_.ContinuousLinearMap.rotation_apply** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.rotation_apply (θ : ℝ) (x : E × E) :
    ContinuousLinearMap.rotation θ x
     = (Real.cos θ • x.1 + Real.sin θ • x.2, -Real.sin θ • x.1 + Real.cos θ • x.2) := rfl

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {a : ℝ}

/-- If a measure `μ` is such that `μ.prod μ` is invariant by rotation of angle `-π/4` then
`μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖} ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2`. -/
/-
**ProbabilityTheory.measure_le_mul_measure_gt_le_of_map_rotation_eq_self** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_le_mul_measure_gt_le_of_map_rotation_eq_self [SFinite μ] (h : (μ.p
rod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (a b : Real) : 
μ {x | ‖x‖ <= a} * μ {x | b < ‖x‖} <= μ {x | (b - a) / √2 < ‖x‖} ^ 2
参数：h : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；a b :
 Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.cos_neg`：cos_neg : cos (-x) = cos x
· 使用定理 `Real.cos_pi_div_four`：cos_pi_div_four : cos (π / 4) = √2 / 2
（共 157 条，此处仅展示前 30 条）

--- 原说明 ---
If a measure `μ` is such that `μ.prod μ` is invariant by rotation of angle `-π/4
` then
`μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖} ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2`.
-/
lemma measure_le_mul_measure_gt_le_of_map_rotation_eq_self [SFinite μ]
    (h : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (a b : ℝ) :
    μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖} ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by
  calc μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖}
  _ = (μ.prod μ) ({x | ‖x‖ ≤ a} ×ˢ {y | b < ‖y‖}) := by rw [Measure.prod_prod]
    -- This is the measure of two bands in the plane (draw a picture!)
  _ = (μ.prod μ) {p | ‖p.1‖ ≤ a ∧ b < ‖p.2‖} := rfl
  _ = ((μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4)))) {p | ‖p.1‖ ≤ a ∧ b < ‖p.2‖} := by
    -- We can rotate the bands since `μ.prod μ` is invariant under rotation
    rw [h]
  _ = (μ.prod μ) {p | ‖p.1 - p.2‖ / √2 ≤ a ∧ b < ‖p.1 + p.2‖ / √2} := by
    rw [Measure.map_apply (by fun_prop)]
    swap
    · refine MeasurableSet.inter ?_ ?_
      · change MeasurableSet {p : E × E | ‖p.1‖ ≤ a}
        exact measurableSet_le (by fun_prop) (by fun_prop)
      · change MeasurableSet {p : E × E | b < ‖p.2‖}
        exact measurableSet_lt (by fun_prop) (by fun_prop)
    congr 1
    simp only [Set.preimage_ofPred_eq, ContinuousLinearMap.rotation_apply, Real.cos_neg,
      Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg]
    have h_twos : ‖2⁻¹ * √2‖ = (√2)⁻¹ := by
      simp only [norm_mul, norm_inv, Real.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      nth_rw 1 [← Real.sq_sqrt (by simp : (0 : ℝ) ≤ 2)]
      rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
    congr! with p
    · rw [← sub_eq_add_neg, ← smul_sub, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
    · rw [← smul_add, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
  _ ≤ (μ.prod μ) {p | (b - a) / √2 < ‖p.1‖ ∧ (b - a) / √2 < ‖p.2‖} := by
    -- The rotated bands are contained in quadrants.
    refine measure_mono fun p ↦ ?_
    simp only [Set.mem_ofPred_eq, and_imp]
    intro hp1 hp2
    suffices (b - a) / √2 < min ‖p.1‖ ‖p.2‖ from lt_min_iff.mp this
    calc (b - a) / √2
    _ < (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
      suffices b - a < ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 by
        calc (b - a) / √2 < (‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2) / √2 := by gcongr
        _ = (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
          field_simp; rw [Real.sq_sqrt (by positivity)]; ring
      calc b - a < ‖p.1 + p.2‖ / √2 - a := by gcongr
      _ ≤ ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 := by gcongr
    _ ≤ min ‖p.1‖ ‖p.2‖ := by
      have := norm_add_sub_norm_sub_le_two_mul_min p.1 p.2
      linarith
  _ = (μ.prod μ) ({x | (b - a) / √2 < ‖x‖} ×ˢ {y | (b - a) / √2 < ‖y‖}) := rfl
  _ ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by rw [Measure.prod_prod, pow_two]

namespace Fernique

/-- A sequence of real thresholds that will be used to cut the space into annuli.
Chosen such that for a rotation invariant measure, an application of lemma
`measure_le_mul_measure_gt_le_of_map_rotation_eq_self` gives
`μ {x | ‖x‖ ≤ a} * μ {x | normThreshold a (n + 1) < ‖x‖} ≤ μ {x | normThreshold a n < ‖x‖} ^ 2`. -/
/-
**ProbabilityTheory.Fernique.normThreshold** 是 Mathlib 中的一个定义，位于命名空间 `Probabilit
yTheory.Fernique`。
形式化陈述：normThreshold (a : Real) : Nat -> Real
参数：a : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of real thresholds that will be used to cut the space into annuli.
Chosen such that for a rotation invariant measure, an application of lemma
`measure_le_mul_measure_gt_le_of_map_rotation_eq_self` gives
`μ {x | ‖x‖ ≤ a} * μ {x | normThreshold a (n + 1) < ‖x‖} ≤ μ {x | normThreshold 
a n < ‖x‖} ^ 2`.
-/
noncomputable def normThreshold (a : ℝ) : ℕ → ℝ := arithGeom √2 a a
/-
**ProbabilityTheory.Fernique.normThreshold_zero** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Fernique`。
形式化陈述：normThreshold_zero : normThreshold a 0 = a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma normThreshold_zero : normThreshold a 0 = a := rfl
/-
**ProbabilityTheory.Fernique.normThreshold_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Fernique`。
形式化陈述：normThreshold_add_one (n : Nat) : normThreshold a (n + 1) = √2 * normThres
hold a n + a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma normThreshold_add_one (n : ℕ) : normThreshold a (n + 1) = √2 * normThreshold a n + a := rfl
/-
**ProbabilityTheory.Fernique.measure_le_mul_measure_gt_normThreshold_le_of_map_r
otation_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Fernique`。
形式化陈述：measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self [SFinit
e μ] (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod 
μ) (a : Real) (n : Nat) : μ {x | ‖x‖ <= a} * μ {x | normThreshold a (n + 1) < ‖x
‖} <= μ {x | normThreshold a n < ‖x‖} ^ 2
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；a
 : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.measure_le_mul_measure_gt_le_of_map_rotation_eq_self`：
measure_le_mul_measure_gt_le_of_map_rotation_eq_self [SFinite μ] (h : (μ.prod μ)
.map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (…
-/
lemma measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self [SFinite μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (a : ℝ) (n : ℕ) :
    μ {x | ‖x‖ ≤ a} * μ {x | normThreshold a (n + 1) < ‖x‖}
      ≤ μ {x | normThreshold a n < ‖x‖} ^ 2 := by
  convert! measure_le_mul_measure_gt_le_of_map_rotation_eq_self h_rot _ _
  simp [normThreshold_add_one]
/-
**ProbabilityTheory.Fernique.lt_normThreshold_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Fernique`。
形式化陈述：lt_normThreshold_zero (ha_pos : 0 < a) : a / (1 - √2) < normThreshold a 0
参数：ha_pos : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_nonpos_of_nonneg_of_nonpos`：div_nonpos_of_nonneg_of_nonpos (ha : 0 <
= a) (hb : b <= 0) : a / b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma lt_normThreshold_zero (ha_pos : 0 < a) : a / (1 - √2) < normThreshold a 0 := by
  simp only [normThreshold_zero]
  calc a / (1 - √2)
  _ ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha_pos.le (by simp)
  _ < a := ha_pos
/-
**ProbabilityTheory.Fernique.normThreshold_strictMono** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Fernique`。
形式化陈述：normThreshold_strictMono (ha_pos : 0 < a) : StrictMono (normThreshold a)
参数：ha_pos : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `arithGeom_strictMono`：arithGeom_strictMono (ha : 1 < a) (h0 : b / (1 - a
) < u₀) : StrictMono (arithGeom a b u₀)
· 使用引理 `Real.one_lt_sqrt_two`：one_lt_sqrt_two : 1 < √2
· 使用引理 `ProbabilityTheory.Fernique.lt_normThreshold_zero`：lt_normThreshold_zero 
(ha_pos : 0 < a) : a / (1 - √2) < normThreshold a 0
-/
lemma normThreshold_strictMono (ha_pos : 0 < a) : StrictMono (normThreshold a) :=
  arithGeom_strictMono Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)
/-
**ProbabilityTheory.Fernique.tendsto_normThreshold_atTop** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.Fernique`。
形式化陈述：tendsto_normThreshold_atTop (ha_pos : 0 < a) : Tendsto (normThreshold a) a
tTop atTop
参数：ha_pos : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_arithGeom_atTop_of_one_lt`：tendsto_arithGeom_atTop_of_one_lt [Ar
chimedean R] (ha : 1 < a) (h0 : b / (1 - a) < u₀) : Tendsto (arithGeom a b u₀) a
tTop atTop
· 使用引理 `Real.one_lt_sqrt_two`：one_lt_sqrt_two : 1 < √2
· 使用引理 `ProbabilityTheory.Fernique.lt_normThreshold_zero`：lt_normThreshold_zero 
(ha_pos : 0 < a) : a / (1 - √2) < normThreshold a 0
-/
lemma tendsto_normThreshold_atTop (ha_pos : 0 < a) : Tendsto (normThreshold a) atTop atTop :=
  tendsto_arithGeom_atTop_of_one_lt Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)
/-
**ProbabilityTheory.Fernique.normThreshold_eq** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Fernique`。
形式化陈述：normThreshold_eq (n : Nat) : normThreshold a n = a * (1 + √2) * (√2 ^ (n +
 1) - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Fernique.normThreshold.eq_1`：∀ (a : ℝ), ProbabilityThe
ory.Fernique.normThreshold a = arithGeom (√2) a a
· 使用引理 `arithGeom_same_eq_mul_div`：arithGeom_same_eq_mul_div (ha : a != 1) (n : 
Nat) : arithGeom a b b n = b * (a ^ (n + 1) - 1) / (a - 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Real.inv_sqrt_two_sub_one`：inv_sqrt_two_sub_one : (√2 - 1)⁻¹ = √2 + 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 50 条，此处仅展示前 30 条）
-/
lemma normThreshold_eq (n : ℕ) : normThreshold a n = a * (1 + √2) * (√2 ^ (n + 1) - 1) := by
  rw [normThreshold, arithGeom_same_eq_mul_div (by simp), div_eq_mul_inv, Real.inv_sqrt_two_sub_one]
  ring
/-
**ProbabilityTheory.Fernique.sq_normThreshold_add_one_le** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.Fernique`。
形式化陈述：sq_normThreshold_add_one_le (n : Nat) : normThreshold a (n + 1) ^ 2 <= a ^
 2 * (1 + √2) ^ 2 * 2 ^ (n + 2)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Fernique.normThreshold_eq`：normThreshold_eq (n : Nat) 
: normThreshold a n = a * (1 + √2) * (√2 ^ (n + 1) - 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
（共 42 条，此处仅展示前 30 条）
-/
lemma sq_normThreshold_add_one_le (n : ℕ) :
    normThreshold a (n + 1) ^ 2 ≤ a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2) := by
  simp_rw [normThreshold_eq, mul_pow, mul_assoc]
  gcongr
  calc (√2 ^ (n + 2) - 1) ^ 2
  _ ≤ (√2 ^ (n + 2)) ^ 2 := by
    gcongr
    · calc 0 ≤ √2 ^ (0 + 2) - 1 := by simp
      _ ≤ √2 ^ (n + 2) - 1 := by gcongr <;> simp
    · exact sub_le_self _ (by simp)
  _ = 2 ^ (n + 2) := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
/-
**ProbabilityTheory.Fernique.measure_gt_normThreshold_le_rpow** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory.Fernique`。
形式化陈述：measure_gt_normThreshold_le_rpow [IsProbabilityMeasure μ] (h_rot : (μ.prod
 μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (ha_gt : 2⁻¹ < μ {
x | ‖x‖ <= a}) (n : Nat) : μ {x | normThreshold a n < ‖x‖} <= μ {x | ‖x‖ <= a} *
 ((1 - μ {x | ‖x‖ <= a}) / μ {x | ‖x‖ <= a}) ^ (2 ^ n)
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；h
a_gt : 2⁻¹ < μ {x | ‖x‖ <= a}；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.prob_compl_eq_one_sub`：prob_compl_eq_one_sub (hs : Measura
bleSet s) : μ sᶜ = 1 - μ s
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
（共 48 条，此处仅展示前 30 条）
-/
lemma measure_gt_normThreshold_le_rpow [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_gt : 2⁻¹ < μ {x | ‖x‖ ≤ a}) (n : ℕ) :
    μ {x | normThreshold a n < ‖x‖}
      ≤ μ {x | ‖x‖ ≤ a} * ((1 - μ {x | ‖x‖ ≤ a}) / μ {x | ‖x‖ ≤ a}) ^ (2 ^ n) := by
  let c := μ {x | ‖x‖ ≤ a}
  replace hc_gt : 2⁻¹ < c := ha_gt
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) hc_gt.le
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, normThreshold_zero]
    rw [ENNReal.mul_div_cancel hc_pos.ne' hc_lt_top.ne]
    refine le_of_eq ?_
    rw [← prob_compl_eq_one_sub (measurableSet_le (by fun_prop) (by fun_prop))]
    congr with x
    simp
  | succ n hn =>
    have h_mul_le : c * μ {x | normThreshold a (n + 1) < ‖x‖}
        ≤ μ {x | normThreshold a n < ‖x‖} ^ 2 :=
      measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self h_rot _ _
    calc μ {x | normThreshold a (n + 1) < ‖x‖}
    _ = c⁻¹ * (c * μ {x | normThreshold a (n + 1) < ‖x‖}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne, one_mul]
    _ ≤ c⁻¹ * μ {x | normThreshold a n < ‖x‖} ^ 2 := by gcongr
    _ ≤ c⁻¹ * (c * ((1 - c) / c) ^ 2 ^ n) ^ 2 := by gcongr
    _ = c * ((1 - c) / c) ^ 2 ^ (n + 1) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, pow_two, ← mul_assoc,
        ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne, one_mul, pow_add, pow_one]
/-
**ProbabilityTheory.Fernique.measure_gt_normThreshold_le_exp** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Fernique`。
形式化陈述：measure_gt_normThreshold_le_exp [IsProbabilityMeasure μ] (h_rot : (μ.prod 
μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (ha_gt : 2⁻¹ < μ {x
 | ‖x‖ <= a}) (ha_lt : μ {x | ‖x‖ <= a} < 1) (n : Nat) : μ {x | normThreshold a 
n < ‖x‖} <= μ {x | ‖x‖ <= a} * .ofReal (rexp (-Real.log (μ {x | ‖x‖ <= a} / (1 -
 μ {x | ‖x‖ <= a})).toReal * 2 ^ n))
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；h
a_gt : 2⁻¹ < μ {x | ‖x‖ <= a}；ha_lt : μ {x | ‖x‖ <= a} < 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `lt_top_of_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a < ⊤
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `div_pos_iff_of_pos_right`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 
: PartialOrder α] [PosMulReflectLT α] {a b : α} [IsStrictOrderedRing α],   0 < b
 → (0 < a / b …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
（共 55 条，此处仅展示前 30 条）
-/
lemma measure_gt_normThreshold_le_exp [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_gt : 2⁻¹ < μ {x | ‖x‖ ≤ a}) (ha_lt : μ {x | ‖x‖ ≤ a} < 1) (n : ℕ) :
    μ {x | normThreshold a n < ‖x‖}
      ≤ μ {x | ‖x‖ ≤ a} * .ofReal (rexp
        (-Real.log (μ {x | ‖x‖ ≤ a} / (1 - μ {x | ‖x‖ ≤ a})).toReal * 2 ^ n)) := by
  let c := μ {x | ‖x‖ ≤ a}
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) ha_gt.le
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have hc_ratio_pos : 0 < (c / (1 - c)).toReal := by
    rw [ENNReal.toReal_div, div_pos_iff_of_pos_right]
    · simp [ENNReal.toReal_pos_iff, hc_pos, hc_lt_top]
    · simp [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, hc_one_sub_lt_top]
  refine (measure_gt_normThreshold_le_rpow h_rot ha_gt n).trans_eq ?_
  congr
  rw [← Real.log_inv, mul_comm (Real.log _), ← Real.log_rpow (by positivity),
    Real.exp_log (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ENNReal.toReal_div, inv_div, ← ENNReal.toReal_div, ENNReal.ofReal_toReal]
  · norm_cast
  · exact ENNReal.div_ne_top (by finiteness) (lt_trans (by simp) ha_gt).ne'

/-- A quantity that appears in exponentials in the proof of Fernique's theorem. -/
/-
**ProbabilityTheory.Fernique.logRatio** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheo
ry.Fernique`。
形式化陈述：logRatio (c : Real>=0∞) : Real
参数：c : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quantity that appears in exponentials in the proof of Fernique's theorem.
-/
noncomputable def logRatio (c : ℝ≥0∞) : ℝ :=
  Real.log (c.toReal / (1 - c).toReal) / (8 * (1 + √2) ^ 2)
/-
**ProbabilityTheory.Fernique.logRatio_pos** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Fernique`。
形式化陈述：logRatio_pos {c : Real>=0∞} (hc_gt : (2 : Real>=0∞)⁻¹ < c) (hc_lt : c < 1)
 : 0 < logRatio c
参数：hc_gt : (2 : Real>=0∞)⁻¹ < c；hc_lt : c < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_lt_div_iff`：one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a <
 b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.sub_ne_top`：sub_ne_top (ha : a != ∞) : a - b != ∞
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ENNReal.sub_lt_of_lt_add`：∀ {a b c : ENNReal}, c ≤ a → a < b + c → a - c
 < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_lt_iff`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ →
 (c / b < a ↔ c < a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
（共 43 条，此处仅展示前 30 条）
-/
lemma logRatio_pos {c : ℝ≥0∞} (hc_gt : (2 : ℝ≥0∞)⁻¹ < c) (hc_lt : c < 1) : 0 < logRatio c := by
  refine div_pos (Real.log_pos ?_) (by positivity)
  rw [one_lt_div_iff]
  refine Or.inl ⟨?_, ?_⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
    finiteness
  · refine (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr ?_
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at hc_gt
/-
**ProbabilityTheory.Fernique.logRatio_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Fernique`。
形式化陈述：logRatio_nonneg {c : Real>=0∞} (hc_ge : (2 : Real>=0∞)⁻¹ <= c) (hc_le : c 
<= 1) : 0 <= logRatio c
参数：hc_ge : (2 : Real>=0∞)⁻¹ <= c；hc_le : c <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `ENNReal.one_sub_inv_two`：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ProbabilityTheory.Fernique.logRatio_pos`：logRatio_pos {c : Real>=0∞} (hc
_gt : (2 : Real>=0∞)⁻¹ < c) (hc_lt : c < 1) : 0 < logRatio c
-/
lemma logRatio_nonneg {c : ℝ≥0∞} (hc_ge : (2 : ℝ≥0∞)⁻¹ ≤ c) (hc_le : c ≤ 1) : 0 ≤ logRatio c := by
  cases hc_ge.eq_or_lt'
  · simp [logRatio, *]
  cases hc_le.eq_or_lt'
  · simp [logRatio, *]
  exact (logRatio_pos ‹_› ‹_›).le
/-
**ProbabilityTheory.Fernique.logRatio_mono** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Fernique`。
形式化陈述：logRatio_mono {c d : Real>=0∞} (hc : (2 : Real>=0∞)⁻¹ < c) (hd : d < 1) (h
 : c <= d) : logRatio c <= logRatio d
参数：hc : (2 : Real>=0∞)⁻¹ < c；hd : d < 1；h : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.sub_ne_top`：sub_ne_top (ha : a != ∞) : a - b != ∞
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
（共 46 条，此处仅展示前 30 条）
-/
lemma logRatio_mono {c d : ℝ≥0∞} (hc : (2 : ℝ≥0∞)⁻¹ < c) (hd : d < 1) (h : c ≤ d) :
    logRatio c ≤ logRatio d := by
  unfold logRatio
  gcongr
  · refine div_pos ?_ ?_
    · rw [ENNReal.toReal_pos_iff]
      exact ⟨lt_trans (by norm_num) hc, h.trans_lt (by finiteness)⟩
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
      exact ⟨h.trans_lt hd, by finiteness⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hd, true_and]
    finiteness
  · finiteness
  · finiteness
/-
**ProbabilityTheory.Fernique.logRatio_mul_normThreshold_add_one_le** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.Fernique`。
形式化陈述：logRatio_mul_normThreshold_add_one_le {c : Real>=0∞} (hc_gt : (2 : Real>=0
∞)⁻¹ < c) (hc_lt : c < 1) (n : Nat) : logRatio c * normThreshold a (n + 1) ^ 2 *
 a⁻¹ ^ 2 <= 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n
参数：hc_gt : (2 : Real>=0∞)⁻¹ < c；hc_lt : c < 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.sub_ne_top`：sub_ne_top (ha : a != ∞) : a - b != ∞
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
（共 121 条，此处仅展示前 30 条）
-/
lemma logRatio_mul_normThreshold_add_one_le {c : ℝ≥0∞}
    (hc_gt : (2 : ℝ≥0∞)⁻¹ < c) (hc_lt : c < 1) (n : ℕ) :
    logRatio c * normThreshold a (n + 1) ^ 2 * a⁻¹ ^ 2
      ≤ 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n := by
  by_cases ha : a = 0
  · simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_right, inv_pos, mul_nonneg_iff_of_pos_left]
    refine Real.log_nonneg ?_
    rw [one_le_div]
    · refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr ?_
      refine tsub_le_iff_left.mpr ?_
      rw [← two_mul]
      rw [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at hc_gt
      exact hc_gt.le
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
      finiteness
  calc logRatio c * normThreshold a (n + 1) ^ 2 * a⁻¹ ^ 2
  _ ≤ logRatio c * (a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2)) * a⁻¹ ^ 2 := by
    gcongr
    · exact (logRatio_pos hc_gt hc_lt).le
    · exact sq_normThreshold_add_one_le n
  _ = 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n := by
    unfold logRatio
    field

open Metric in
/-- Auxiliary lemma for `lintegral_exp_mul_sq_norm_le_mul`, in which we find an upper bound on an
integral by dealing separately with the contribution of each set in a sequence of annuli.
This is the bound of the integral over one of those annuli. -/
/-
**ProbabilityTheory.Fernique.lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le**
 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Fernique`。
形式化陈述：lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le [IsProbabilityMeasure μ]
 (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (
ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}) (ha_lt : μ {x | ‖x‖ <= a} < 1) (n : Nat) : ∫⁻ x 
in (closedBall 0 (normThreshold a (n + 1)) \ closedBall 0 (normThreshold a n)), 
.ofReal (rexp (logRatio (μ {x | ‖x‖ <= a}) * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ <= μ {x | ‖x
‖ <= a} * .ofReal (rexp (-2⁻¹ * Real.log (μ {x | ‖x‖ <= a} / (1 - μ {x | ‖x‖ <= 
a})).toReal * 2 ^ n))
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；h
a_gt : 2⁻¹ < μ {x | ‖x‖ <= a}；ha_lt : μ {x | ‖x‖ <= a} < 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.setLIntegral_mono`：setLIntegral_mono {s : Set α} {f g : α 
-> Real>=0∞} (hg : Measurable g) (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, 
f x ∂μ <= ∫⁻ x in s, …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ProbabilityTheory.Fernique.logRatio_pos`：logRatio_pos {c : Real>=0∞} (hc
_gt : (2 : Real>=0∞)⁻¹ < c) (hc_lt : c < 1) : 0 < logRatio c
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `lintegral_exp_mul_sq_norm_le_mul`, in which we find an uppe
r bound on an
integral by dealing separately with the contribution of each set in a sequence o
f annuli.
This is the bound of the integral over one of those annuli.
-/
lemma lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_gt : 2⁻¹ < μ {x | ‖x‖ ≤ a}) (ha_lt : μ {x | ‖x‖ ≤ a} < 1) (n : ℕ) :
    ∫⁻ x in (closedBall 0 (normThreshold a (n + 1)) \ closedBall 0 (normThreshold a n)),
        .ofReal (rexp (logRatio (μ {x | ‖x‖ ≤ a}) * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ
      ≤ μ {x | ‖x‖ ≤ a} * .ofReal (rexp
          (-2⁻¹ * Real.log (μ {x | ‖x‖ ≤ a} / (1 - μ {x | ‖x‖ ≤ a})).toReal * 2 ^ n)) :=
  let t := normThreshold a
  let c := μ {x | ‖x‖ ≤ a}
  let C := logRatio c * a⁻¹ ^ 2
  calc ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
  -- We bound the function on the set by its maximal value, at the outer boundary of the annulus
  _ ≤ ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)),
      .ofReal (rexp (C * t (n + 1) ^ 2)) ∂μ := by
    refine setLIntegral_mono (by fun_prop) fun x hx ↦ ?_
    gcongr
    · exact mul_nonneg (logRatio_pos ha_gt ha_lt).le (by positivity)
    · simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.1
  -- The integral of a constant is the constant times the measure of the set
  _ = .ofReal (rexp (C * t (n + 1) ^ 2)) * μ (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)) := by
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, C, t]
  _ ≤ .ofReal (rexp (C * t (n + 1) ^ 2)) * μ {x | t n < ‖x‖} := by
    gcongr
    intro x
    simp
  -- We obtained an upper bound on the measure of that annulus in a previous lemma
  _ ≤ .ofReal (rexp (C * t (n + 1) ^ 2))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    conv_rhs => rw [mul_assoc]
    gcongr
    exact measure_gt_normThreshold_le_exp h_rot ha_gt ha_lt n
  _ ≤ .ofReal (rexp (2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    gcongr ENNReal.ofReal (rexp ?_) * _ * _
    convert! logRatio_mul_normThreshold_add_one_le ha_gt ha_lt n (a := a) using 1
    ring
  _ = c * .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    rw [mul_comm _ c, mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
    congr
    norm_cast
    simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_div]
    ring

@[deprecated (since := "2026-06-03")]
alias lintegral_closedBall_diff_exp_logRatio_mul_sq_le :=
  lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le

set_option backward.isDefEq.respectTransparency.types false in
open Metric in
/-
**ProbabilityTheory.Fernique.lintegral_exp_mul_sq_norm_le_mul** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory.Fernique`。
形式化陈述：lintegral_exp_mul_sq_norm_le_mul [IsProbabilityMeasure μ] (h_rot : (μ.prod
 μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (ha_pos : 0 < a) {
c' : Real>=0∞} (hc' : c' <= μ {x | ‖x‖ <= a}) (hc'_gt : 2⁻¹ < c') : ∫⁻ x, .ofRea
l (rexp (logRatio c' * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ <= μ {x | ‖x‖ <= a} * (.ofReal (re
xp (logRatio c')) + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal 
* 2 ^ n)))
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；h
a_pos : 0 < a；hc' : c' <= μ {x | ‖x‖ <= a}；hc'_gt : 2⁻¹ < c'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.setLIntegral_mono`：setLIntegral_mono {s : Set α} {f g : α 
-> Real>=0∞} (hg : Measurable g) (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, 
f x ∂μ <= ∫⁻ x in s, …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用引理 `ProbabilityTheory.Fernique.logRatio_nonneg`：logRatio_nonneg {c : Real>=0
∞} (hc_ge : (2 : Real>=0∞)⁻¹ <= c) (hc_le : c <= 1) : 0 <= logRatio c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
（共 156 条，此处仅展示前 30 条）
-/
lemma lintegral_exp_mul_sq_norm_le_mul [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_pos : 0 < a)
    {c' : ℝ≥0∞} (hc' : c' ≤ μ {x | ‖x‖ ≤ a}) (hc'_gt : 2⁻¹ < c') :
    ∫⁻ x, .ofReal (rexp (logRatio c' * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ
      ≤ μ {x | ‖x‖ ≤ a} *
       (.ofReal (rexp (logRatio c'))
        + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal * 2 ^ n))) := by
  let t := normThreshold a
  let c := μ {x | ‖x‖ ≤ a}
  let C := logRatio c' * a⁻¹ ^ 2
  have hc'_le : c' ≤ 1 := hc'.trans prob_le_one
  -- We want to bound an integral
  change ∫⁻ x, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      ≤ c * (.ofReal (rexp (logRatio c'))
            + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal * 2 ^ n)))
  -- We will cut the space into a ball of radius `a` and annuli defined from the thresholds `t n`
  -- and bound the integral on each piece.
  -- First, we bound the integral on the ball of radius `a`
  have ht_int_zero : ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      ≤ μ {x | ‖x‖ ≤ a} * .ofReal (rexp (logRatio c')) := by
    calc ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
    _ ≤ ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * a ^ 2)) ∂μ := by
      refine setLIntegral_mono (by fun_prop) fun x hx ↦ ?_
      gcongr
      · exact mul_nonneg (logRatio_nonneg hc'_gt.le hc'_le) (by positivity)
      · simpa using hx
    _ = μ {x | ‖x‖ ≤ a} * .ofReal (rexp (logRatio c')) := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
      rw [mul_comm]
      simp only [inv_pow, C]
      field_simp
      congr with x
      simp
  -- We dispense with an edge case. If `μ {x | ‖x‖ ≤ a} = 1`, then the integral over
  -- the complement of the ball is zero and we are done.
  by_cases ha : μ {x | ‖x‖ ≤ a} = 1
  · simp only [ha, one_mul, ENNReal.toReal_div, neg_mul, ge_iff_le, c] at ht_int_zero ⊢
    refine le_add_right ((le_of_eq ?_).trans ht_int_zero)
    rw [← setLIntegral_univ]
    refine setLIntegral_congr ?_
    rw [← ae_iff_prob_eq_one ?_] at ha
    · rw [eventuallyEq_comm, ae_eq_univ]
      change μ {x | ¬ x ∈ closedBall 0 a} = 0
      rw [← ae_iff]
      filter_upwards [ha] with x hx using by simp [hx]
    · fun_prop
  -- So we can assume `μ {x | ‖x‖ ≤ a} < 1`, which implies `c' < 1`
  have ha_lt : μ {x | ‖x‖ ≤ a} < 1 := lt_of_le_of_ne prob_le_one ha
  have hc'_lt : c' < 1 := lt_of_le_of_lt hc' ha_lt
  -- We cut the space into a ball and a sequence of annuli between the thresholds `t n`
  have h_iUnion : (Set.univ : Set E)
      = closedBall 0 a ∪ ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion,
      Set.mem_sdiff, not_le, true_iff]
    simp_rw [and_comm (b := t _ < ‖x‖)]
    rcases le_or_gt (‖x‖) a with ha' | ha'
    · exact Or.inl ha'
    · exact Or.inr <| (normThreshold_strictMono ha_pos).exists_between_of_tendsto_atTop
        (tendsto_normThreshold_atTop ha_pos) ha'
  -- The integral over the union is at most the sum of the integrals
  rw [← setLIntegral_univ, h_iUnion]
  have : ∫⁻ x in closedBall 0 (t 0) ∪ ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n),
        .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      ≤ ∫⁻ x in closedBall 0 (t 0), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ +
        ∑' i, ∫⁻ x in closedBall 0 (t (i + 1)) \ closedBall 0 (t i),
          .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ := by
    refine (lintegral_union_le _ _ _).trans ?_
    gcongr
    exact lintegral_iUnion_le _ _
  -- Each of the integrals in the sum correspond to the terms in the goal
  refine this.trans ?_
  rw [mul_add]
  gcongr
  -- We already proved the upper bound for the ball
  · exact ht_int_zero
  rw [← ENNReal.tsum_mul_left]
  gcongr with n
  -- Now we prove the bound for each annulus, by calling a previous lemma
  refine (le_trans ?_ (lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le h_rot
    (hc'_gt.trans_le hc') ha_lt n)).trans ?_
  · gcongr
    simp only [inv_pow, C]
    field_simp
    exact logRatio_mono hc'_gt ha_lt hc'
  gcongr _ * ENNReal.ofReal (rexp ?_)
  simp only [ENNReal.toReal_div, neg_mul, neg_le_neg_iff]
  gcongr
  · refine div_pos ?_ ?_
    all_goals rw [ENNReal.toReal_pos_iff]
    · exact ⟨lt_trans (by norm_num) hc'_gt, by finiteness⟩
    · simp only [tsub_pos_iff_lt, hc'_lt, true_and]
      finiteness
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
    exact ⟨ha_lt, by finiteness⟩
  · finiteness
  · finiteness

end Fernique

open Fernique

/-- For `μ` a probability measure whose product with itself is invariant by rotation and for `a, c`
with `2⁻¹ < c ≤ μ {x | ‖x‖ ≤ a}`, the integral `∫⁻ x, exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2) ∂μ`
is bounded by a quantity that does not depend on `a`. -/
/-
**ProbabilityTheory.lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self [IsProbabilityMeasure
 μ] (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ
) {c : Real>=0∞} (hc : c <= μ {x | ‖x‖ <= a}) (hc_gt : 2⁻¹ < c) : ∫⁻ x, .ofReal 
(rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ <= .ofReal (rexp (logRatio c)) + ∑' n
, .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n))
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；h
c : c <= μ {x | ‖x‖ <= a}；hc_gt : 2⁻¹ < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
For `μ` a probability measure whose product with itself is invariant by rotation
 and for `a, c`
with `2⁻¹ < c ≤ μ {x | ‖x‖ ≤ a}`, the integral `∫⁻ x, exp (logRatio c * a⁻¹ ^ 2 
* ‖x‖ ^ 2) ∂μ`
is bounded by a quantity that does not depend on `a`.
-/
theorem lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    {c : ℝ≥0∞} (hc : c ≤ μ {x | ‖x‖ ≤ a}) (hc_gt : 2⁻¹ < c) :
    ∫⁻ x, .ofReal (rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ
      ≤ .ofReal (rexp (logRatio c))
        + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
  have ha : 0 ≤ a := by
    by_contra! h_neg
    have : {x : E | ‖x‖ ≤ a} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact h_neg.trans_le (norm_nonneg _)
    simp only [this, measure_empty, nonpos_iff_eq_zero] at hc
    simp [hc] at hc_gt
  cases ha.eq_or_lt' with
  | inl ha =>
    simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one,
      ENNReal.toReal_div, neg_mul]
    refine le_add_right ?_
    rw [← ENNReal.ofReal_one]
    gcongr
    simp only [Real.one_le_exp_iff]
    exact logRatio_nonneg hc_gt.le (hc.trans prob_le_one)
  | inr ha_pos =>
  refine (lintegral_exp_mul_sq_norm_le_mul h_rot ha_pos hc hc_gt).trans ?_
  conv_rhs => rw [← one_mul (ENNReal.ofReal _ + _)]
  gcongr
  exact prob_le_one

/-- Auxiliary lemma for `exists_integrable_exp_sq_of_map_rotation_eq_self`.
The assumptions on `a` and `μ {x | ‖x‖ ≤ a}` are not needed and will be removed in that more
general theorem. -/
/-
**ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self'** 是 Mathli
b 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：exists_integrable_exp_sq_of_map_rotation_eq_self' [IsProbabilityMeasure μ]
 (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) {
a : Real} (ha_pos : 0 < a) (ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}) (ha_lt : μ {x | ‖x‖ 
<= a} < 1) : exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ；h
a_pos : 0 < a；ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}；ha_lt : μ {x | ‖x‖ <= a} < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `lt_top_of_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a < ⊤
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.sub_lt_of_lt_add`：∀ {a b c : ENNReal}, c ≤ a → a < b + c → a - c
 < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_lt_iff`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ →
 (c / b < a ↔ c < a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `exists_integrable_exp_sq_of_map_rotation_eq_self`.
The assumptions on `a` and `μ {x | ‖x‖ ≤ a}` are not needed and will be removed 
in that more
general theorem.
-/
lemma exists_integrable_exp_sq_of_map_rotation_eq_self' [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    {a : ℝ} (ha_pos : 0 < a) (ha_gt : 2⁻¹ < μ {x | ‖x‖ ≤ a}) (ha_lt : μ {x | ‖x‖ ≤ a} < 1) :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  let c := μ {x | ‖x‖ ≤ a}
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have h_one_sub_lt_self : 1 - c < c := by
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at ha_gt
  have h_pos : 0 < logRatio c * a⁻¹ ^ 2 := mul_pos (logRatio_pos ha_gt hc_lt) (by positivity)
  refine ⟨logRatio c * a⁻¹ ^ 2, h_pos, ⟨by fun_prop, ?_⟩⟩
  simp only [HasFiniteIntegral, ← ofReal_norm, Real.norm_eq_abs, Real.abs_exp]
  -- `⊢ ∫⁻ x, ENNReal.ofReal (rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ < ∞`
  refine (lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self h_rot le_rfl ha_gt).trans_lt ?_
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
  refine Summable.tsum_ofReal_lt_top <|
    Real.summable_exp_nat_mul_of_ge ?_ (fun i ↦ mod_cast (Nat.lt_pow_self (by simp)).le)
  refine mul_neg_of_neg_of_pos (by simp) (Real.log_pos ?_)
  change 1 < (c / (1 - c)).toReal
  simp only [ENNReal.toReal_div, one_lt_div_iff, ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt,
    hc_one_sub_lt_top, and_self, true_and]
  rw [ENNReal.toReal_lt_toReal hc_one_sub_lt_top.ne hc_lt_top.ne]
  exact .inl h_one_sub_lt_self

/-- Auxiliary lemma for `exists_integrable_exp_sq_of_map_rotation_eq_self`, in which we will replace
the assumption `IsProbabilityMeasure μ` by the weaker `IsFiniteMeasure μ`. -/
/-
**ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbab
ilityMeasure** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure [
IsProbabilityMeasure μ] (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-
(π / 4))) = μ.prod μ) : exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2
)) μ
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self'`：exi
sts_integrable_exp_sq_of_map_rotation_eq_self' [IsProbabilityMeasure μ] (h_rot :
 (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4)))…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `exists_integrable_exp_sq_of_map_rotation_eq_self`, in which
 we will replace
the assumption `IsProbabilityMeasure μ` by the weaker `IsFiniteMeasure μ`.
-/
lemma exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure
    [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  -- If there exists `a > 0` such that `2⁻¹ < μ {x | ‖x‖ ≤ a} < 1`, we can call the previous lemma.
  by_cases h_meas_Ioo : ∃ a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ ≤ a} ∧ μ {x | ‖x‖ ≤ a} < 1
  · obtain ⟨a, ha_pos, ha_gt, ha_lt⟩ : ∃ a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ ≤ a} ∧ μ {x | ‖x‖ ≤ a} < 1 :=
      h_meas_Ioo
    exact exists_integrable_exp_sq_of_map_rotation_eq_self' h_rot ha_pos ha_gt ha_lt
  -- Otherwise, we can find `b > 0` such that the ball of radius `b` has full measure
  obtain ⟨b, hb⟩ : ∃ b, μ {x | ‖x‖ ≤ b} = 1 := by
    by_contra h_ne
    push Not at h_meas_Ioo h_ne
    suffices μ .univ ≤ 2⁻¹ by simp at this
    have h_le a : μ {x | ‖x‖ ≤ a} ≤ 2⁻¹ := by
      have h_of_pos a' (ha : 0 < a') : μ {x | ‖x‖ ≤ a'} ≤ 2⁻¹ := by
        by_contra h_lt
        refine h_ne a' ?_
        exact le_antisymm prob_le_one (h_meas_Ioo a' ha (not_le.mp h_lt))
      rcases le_or_gt a 0 with ha | ha
      · calc μ {x | ‖x‖ ≤ a}
        _ ≤ μ {x | ‖x‖ ≤ 1} := measure_mono fun x hx ↦ hx.trans (ha.trans (by positivity))
        _ ≤ 2⁻¹ := h_of_pos _ (by positivity)
      · exact h_of_pos a ha
    have h_univ : (Set.univ : Set E) = ⋃ a : ℕ, {x | ‖x‖ ≤ a} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact exists_nat_ge _
    rw [h_univ, Monotone.measure_iUnion]
    · simp [h_le]
    · intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans (mod_cast hab)
  -- So we can take `C = 1` and show that `x ↦ exp (‖x‖ ^ 2)` is integrable, since it is bounded.
  have hb' : ∀ᵐ x ∂μ, ‖x‖ ≤ b := by
    rwa [ae_iff_prob_eq_one]
    refine measurable_to_prop ?_
    rw [show (fun x : E ↦ ‖x‖ ≤ b) ⁻¹' {True} = {x : E | ‖x‖ ≤ b} by ext; simp]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  refine ⟨1, by positivity, ?_⟩
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ ↦ rexp (b ^ 2)) (by fun_prop)
    ?_ ?_ (integrable_const _) (integrable_const _)
  · exact ae_of_all _ fun _ ↦ by positivity
  · filter_upwards [hb'] with x hx
    simp only [one_mul]
    gcongr

/-- **Fernique's theorem** for finite measures whose product is invariant by rotation: there exists
`C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable. -/
/-
**ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：exists_integrable_exp_sq_of_map_rotation_eq_self [IsFiniteMeasure μ] (h_ro
t : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) : exist
s C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ
参数：h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.cond.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ
 : MeasureTheory.Measure Ω) (s : Set Ω), μ[|s] = (μ s)⁻¹ • μ.restrict s
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.cond_isProbabilityMeasure`：cond_isProbabilityMeasure [
IsFiniteMeasure μ] (hcs : μ s != 0) : IsProbabilityMeasure μ[|s]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.prod_smul_right`：∀ {α : Type u_1} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {β : Type u_2} {mβ : MeasurableSpace β}  
 {ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用引理 `MeasureTheory.Measure.prod_smul_left`：prod_smul_left {μ : Measure α} {R 
: Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) : (c • μ)
.prod ν = c • (μ.prod ν)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用引理 `ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self_of_is
ProbabilityMeasure`：exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbab
ilityMeasure [IsProbabilityMeasure μ] (h_rot : (μ.prod μ).map (ContinuousLinearM
…
· 使用定理 `MeasureTheory.integrable_smul_measure`：integrable_smul_measure {f : α ->
 ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) : Integrable f (c • μ) ↔ Integrab
le f μ

--- 原说明 ---
**Fernique's theorem** for finite measures whose product is invariant by rotatio
n: there exists
`C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable.
-/
theorem exists_integrable_exp_sq_of_map_rotation_eq_self [IsFiniteMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  by_cases hμ_zero : μ = 0
  · exact ⟨1, by positivity, by simp [hμ_zero]⟩
  let μ' := cond μ .univ
  have hμ'_eq : μ' = (μ .univ)⁻¹ • μ := by simp [μ', cond]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure <| by simp [hμ_zero]
  have h_rot : (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4))) = μ'.prod μ' := by
    calc (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4)))
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹)
        • (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹) • (μ.prod μ) := by rw [h_rot]
    _ = μ'.prod μ' := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  obtain ⟨C, hC_pos, hC⟩ :=
    exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure (μ := μ') h_rot
  refine ⟨C, hC_pos, ?_⟩
  rwa [hμ'_eq, integrable_smul_measure] at hC
  · simp
  · simp [hμ_zero]

end ProbabilityTheory

