/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Vitali-Carathéodory theorem

Vitali-Carathéodory theorem asserts the following. Consider an integrable function `f : α → ℝ` on
a space with a regular measure. Then there exists a function `g : α → EReal` such that `f x < g x`
everywhere, `g` is lower semicontinuous, and the integral of `g` is arbitrarily close to that of
`f`. This theorem is proved in this file, as `exists_lt_lower_semicontinuous_integral_lt`.

Symmetrically, there exists `g < f` which is upper semicontinuous, with integral arbitrarily close
to that of `f`. It follows from the previous statement applied to `-f`. It is formalized under
the name `exists_upper_semicontinuous_lt_integral_gt`.

The most classical version of Vitali-Carathéodory theorem only ensures a large inequality
`f x ≤ g x`. For applications to the fundamental theorem of calculus, though, the strict inequality
`f x < g x` is important. Therefore, we prove the stronger version with strict inequalities in this
file. There is a price to pay: we require that the measure is `σ`-finite, which is not necessary for
the classical Vitali-Carathéodory theorem. Since this is satisfied in all applications, this is
not a real problem.

## Sketch of proof

Decomposing `f` as the difference of its positive and negative parts, it suffices to show that a
positive function can be bounded from above by a lower semicontinuous function, and from below
by an upper semicontinuous function, with integrals close to that of `f`.

For the bound from above, write `f` as a series `∑' n, cₙ * indicator (sₙ)` of simple functions.
Then, approximate `sₙ` by a larger open set `uₙ` with measure very close to that of `sₙ` (this is
possible by regularity of the measure), and set `g = ∑' n, cₙ * indicator (uₙ)`. It is
lower semicontinuous as a series of lower semicontinuous functions, and its integral is arbitrarily
close to that of `f`.

For the bound from below, use finitely many terms in the series, and approximate `sₙ` from inside by
a closed set `Fₙ`. Then `∑ n < N, cₙ * indicator (Fₙ)` is bounded from above by `f`, it is
upper semicontinuous as a finite sum of upper semicontinuous functions, and its integral is
arbitrarily close to that of `f`.

The main pain point in the implementation is that one needs to jump between the spaces `ℝ`, `ℝ≥0`,
`ℝ≥0∞` and `EReal` (and be careful that addition is not well behaved on `EReal`), and between
`lintegral` and `integral`.

We first show the bound from above for simple functions and the nonnegative integral
(this is the main nontrivial mathematical point), then deduce it for general nonnegative functions,
first for the nonnegative integral and then for the Bochner integral.

Then we follow the same steps for the lower bound.

Finally, we glue them together to obtain the main statement
`exists_lt_lower_semicontinuous_integral_lt`.

## Related results

Are you looking for a result on approximation by continuous functions (not just semicontinuous)?
See result `MeasureTheory.Lp.boundedContinuousFunction_dense`, in the file
`Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`.

## References

[Rudin, *Real and Complex Analysis* (Theorem 2.24)][rudin2006real]

-/

public section


open scoped ENNReal NNReal

open MeasureTheory MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α)
  [WeaklyRegular μ]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

/-! ### Lower semicontinuous upper bound for nonnegative functions -/


/-- Given a simple function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] 
[BorelSpace α] (μ : MeasureTheory.Measure α)   [μ.WeaklyRegular] (f : MeasureThe
ory.SimpleFunc α NNReal) {ε : ENNReal},   ε ≠ 0 → ∃ g, (∀ (x : α), f x ≤ g x) ∧ 
LowerSemicontinuous g ∧ ∫⁻ (x : α), ↑(g x) ∂μ ≤ ∫⁻ (x : α), ↑(f x) ∂μ + ε
参数：μ : MeasureTheory.Measure α；f : MeasureTheory.SimpleFunc α NNReal；∀ (x : α), 
f x ≤ g x；x : α；g x；x : α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Set.indicator_le_self`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoid
 M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] (s : Set α)   (f : α → M
), s.indica…
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `lowerSemicontinuous_const`：lowerSemicontinuous_const : LowerSemicontinuo
us fun _x : α => z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.SimpleFunc.piecewise.congr_simp`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] (s s_1 : Set α) (e_s : s = s_1) (hs : Measurab
leSet s)   (f f_1 : MeasureTheory.S…
· 使用定理 `Set.indicator_zero'`：∀ {α : Type u_1} (M : Type u_3) [inst : Zero M] {s 
: Set α}, s.indicator 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.coe_indicator`：coe_indicator {α} (s : Set α) (f : α -> Real>=0) 
(a : α) : ((s.indicator f a : Real>=0) : Real>=0∞) = s.indicator (fun x => ↑(f x
)) a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
Given a simple function `f` with values in `ℝ≥0`, there exists a lower semiconti
nuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in 
terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge (f : α →ₛ ℝ≥0) {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧
      (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε := by
  induction f using MeasureTheory.SimpleFunc.induction generalizing ε with
  | @const c s hs =>
    let f := SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)
    by_cases h : ∫⁻ x, f x ∂μ = ⊤
    · refine
        ⟨fun _ => c, fun x => ?_, lowerSemicontinuous_const, by
          simp only [f, _root_.top_add, le_top, h]⟩
      simp only [SimpleFunc.coe_const, SimpleFunc.const_zero, SimpleFunc.coe_zero,
        Set.piecewise_eq_indicator, SimpleFunc.coe_piecewise]
      exact Set.indicator_le_self _ _ _
    by_cases hc : c = 0
    · refine ⟨fun _ => 0, ?_, lowerSemicontinuous_const, ?_⟩
      · classical
        simp only [hc, Set.indicator_zero', Pi.zero_apply, SimpleFunc.const_zero, imp_true_iff,
          SimpleFunc.coe_zero, Set.piecewise_eq_indicator,
          SimpleFunc.coe_piecewise, le_zero_iff]
      · simp only [lintegral_const, zero_mul, zero_le, ENNReal.coe_zero]
    have ne_top : μ s ≠ ⊤ := by
      simpa [f, hs, hc, lt_top_iff_ne_top, SimpleFunc.coe_const,
        Function.const_apply, lintegral_const, ENNReal.coe_indicator, Set.univ_inter,
        ENNReal.coe_ne_top, MeasurableSet.univ, ENNReal.mul_eq_top, SimpleFunc.const_zero,
        lintegral_indicator, ENNReal.coe_eq_zero, Ne, not_false_iff,
        SimpleFunc.coe_zero, Set.piecewise_eq_indicator, SimpleFunc.coe_piecewise,
        restrict_apply] using h
    have : μ s < μ s + ε / c := by
      have : (0 : ℝ≥0∞) < ε / c := ENNReal.div_pos_iff.2 ⟨ε0, ENNReal.coe_ne_top⟩
      simpa using ENNReal.add_lt_add_left ne_top this
    obtain ⟨u, su, u_open, μu⟩ : ∃ (u : _), u ⊇ s ∧ IsOpen u ∧ μ u < μ s + ε / c :=
      s.exists_isOpen_lt_of_lt _ this
    refine ⟨Set.indicator u fun _ => c,
      fun x => ?_, u_open.lowerSemicontinuous_indicator zero_le, ?_⟩
    · simp only [SimpleFunc.coe_const, SimpleFunc.const_zero, SimpleFunc.coe_zero,
        Set.piecewise_eq_indicator, SimpleFunc.coe_piecewise, ← Function.const_def]
      grw [su]
    · suffices (c : ℝ≥0∞) * μ u ≤ c * μ s + ε by
        simpa only [ENNReal.coe_indicator, u_open.measurableSet, lintegral_indicator,
          lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, const_zero,
          coe_piecewise, coe_const, coe_zero, Set.piecewise_eq_indicator, Function.const_apply, hs]
      calc
        (c : ℝ≥0∞) * μ u ≤ c * (μ s + ε / c) := by grw [μu]
        _ = c * μ s + ε := by
          simp_rw [mul_add]
          rw [ENNReal.mul_div_cancel _ ENNReal.coe_ne_top]
          simpa using hc
  | @add f₁ f₂ _ h₁ h₂ =>
    rcases h₁ (ENNReal.half_pos ε0).ne' with ⟨g₁, f₁_le_g₁, g₁cont, g₁int⟩
    rcases h₂ (ENNReal.half_pos ε0).ne' with ⟨g₂, f₂_le_g₂, g₂cont, g₂int⟩
    refine
      ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, ?_⟩
    simp only [SimpleFunc.coe_add, ENNReal.coe_add, Pi.add_apply]
    rw [lintegral_add_left f₁.measurable.coe_nnreal_ennreal,
      lintegral_add_left g₁cont.measurable.coe_nnreal_ennreal]
    convert! add_le_add g₁int g₂int using 1
    conv_lhs => rw [← ENNReal.add_halves ε]
    abel

open SimpleFunc in
/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.exists_le_lowerSemicontinuous_lintegral_ge** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：exists_le_lowerSemicontinuous_lintegral_ge (f : α -> Real>=0∞) (hf : Measu
rable f) {ε : Real>=0∞} (εpos : ε != 0) : exists g : α -> Real>=0∞, (forall x, f
 x <= g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) <= (∫⁻ x, f x ∂μ) + ε
参数：f : α -> Real>=0∞；hf : Measurable f；εpos : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_pos_sum_of_countable'`：exists_pos_sum_of_countable' {ε : 
Real>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0∞, (forall i
, 0 < ε' i) ∧ ∑' i, ε' i <…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge`：∀ {
α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpa
ce α] (μ : MeasureTheory.Measure α)   [μ.WeaklyRegular] (…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.tsum_eapproxDiff`：tsum_eapproxDiff (f : α -> Re
al>=0∞) (hf : Measurable f) (a : α) : (∑' n, (eapproxDiff f n a : Real>=0∞)) = f
 a
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lowerSemicontinuous_tsum`：lowerSemicontinuous_tsum {f : ι -> α -> Real>=
0∞} (h : forall i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ∑'
 i, f i x'
· 使用定理 `Continuous.comp_lowerSemicontinuous`：Continuous.comp_lowerSemicontinuous
 {g : γ -> δ} {f : α -> γ} (hg : Continuous g) (hf : LowerSemicontinuous f) (gmo
n : Monotone g) : LowerSe…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `LowerSemicontinuous.measurable`：LowerSemicontinuous.measurable [Topologi
calSpace δ] [OpensMeasurableSpace δ] {f : δ -> α} (hf : LowerSemicontinuous f) :
 Measurable f
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.tsum_add`：∀ {α : Type u_1} {f g : α → ENNReal}, ∑' (a : α), (f a
 + g a) = ∑' (a : α), f a + ∑' (a : α), g a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semic
ontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in 
terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem exists_le_lowerSemicontinuous_lintegral_ge (f : α → ℝ≥0∞) (hf : Measurable f) {ε : ℝ≥0∞}
    (εpos : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε := by
  rcases ENNReal.exists_pos_sum_of_countable' εpos ℕ with ⟨δ, δpos, hδ⟩
  have :
    ∀ n,
      ∃ g : α → ℝ≥0,
        (∀ x, eapproxDiff f n x ≤ g x) ∧
          LowerSemicontinuous g ∧
            (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, eapproxDiff f n x ∂μ) + δ n :=
    fun n =>
    SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge μ (eapproxDiff f n)
      (δpos n).ne'
  choose g f_le_g gcont hg using this
  refine ⟨fun x => ∑' n, g n x, fun x => ?_, ?_, ?_⟩
  · rw [← tsum_eapproxDiff f hf]
    exact ENNReal.tsum_le_tsum fun n => ENNReal.coe_le_coe.2 (f_le_g n x)
  · refine lowerSemicontinuous_tsum fun n => ?_
    exact
      ENNReal.continuous_coe.comp_lowerSemicontinuous (gcont n) fun x y hxy =>
        ENNReal.coe_le_coe.2 hxy
  · calc
      ∫⁻ x, ∑' n : ℕ, g n x ∂μ = ∑' n, ∫⁻ x, g n x ∂μ := by
        rw [lintegral_tsum fun n => (gcont n).measurable.coe_nnreal_ennreal.aemeasurable]
      _ ≤ ∑' n, ((∫⁻ x, eapproxDiff f n x ∂μ) + δ n) := ENNReal.tsum_le_tsum hg
      _ = ∑' n, ∫⁻ x, eapproxDiff f n x ∂μ + ∑' n, δ n := ENNReal.tsum_add
      _ ≤ (∫⁻ x : α, f x ∂μ) + ε := by
        refine add_le_add ?_ hδ.le
        rw [← lintegral_tsum]
        · simp_rw [tsum_eapproxDiff f hf, le_refl]
        · intro n; exact (SimpleFunc.measurable _).coe_nnreal_ennreal.aemeasurable

/-- Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.exists_lt_lowerSemicontinuous_lintegral_ge** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：exists_lt_lowerSemicontinuous_lintegral_ge [SigmaFinite μ] (f : α -> Real>
=0) (fmeas : Measurable f) {ε : Real>=0∞} (ε0 : ε != 0) : exists g : α -> Real>=
0∞, (forall x, (f x : Real>=0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) 
<= (∫⁻ x, f x ∂μ) + ε
参数：f : α -> Real>=0；fmeas : Measurable f；ε0 : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite`：exists_pos_lintegr
al_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : Real>=0∞} (ε0 : ε != 0
) : exists g : α -> Real>=0, (forall x, 0 …
· 使用定理 `MeasureTheory.exists_le_lowerSemicontinuous_lintegral_ge`：exists_le_lowe
rSemicontinuous_lintegral_ge (f : α -> Real>=0∞) (hf : Measurable f) {ε : Real>=
0∞} (εpos : ε != 0) : exists g : α -> Real>=0∞…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `MeasureTheory.lintegral_add_right`：lintegral_add_right (f : α -> Real>=0
∞) {g : α -> Real>=0∞} (hg : Measurable g) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ +
 ∫⁻ a, g a ∂μ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, th
ere exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of
 `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem exists_lt_lowerSemicontinuous_lintegral_ge [SigmaFinite μ] (f : α → ℝ≥0)
    (fmeas : Measurable f) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε := by
  have : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
  rcases exists_pos_lintegral_lt_of_sigmaFinite μ this with ⟨w, wpos, wmeas, wint⟩
  let f' x := ((f x + w x : ℝ≥0) : ℝ≥0∞)
  rcases exists_le_lowerSemicontinuous_lintegral_ge μ f' (fmeas.add wmeas).coe_nnreal_ennreal
      this with
    ⟨g, le_g, gcont, gint⟩
  refine ⟨g, fun x => ?_, gcont, ?_⟩
  · calc
      (f x : ℝ≥0∞) < f' x := by
        simpa only [← ENNReal.coe_lt_coe, add_zero] using add_lt_add_right (wpos x) (f x)
      _ ≤ g x := le_g x
  · calc
      (∫⁻ x : α, g x ∂μ) ≤ (∫⁻ x : α, f x + w x ∂μ) + ε / 2 := gint
      _ = ((∫⁻ x : α, f x ∂μ) + ∫⁻ x : α, w x ∂μ) + ε / 2 := by
        rw [lintegral_add_right _ wmeas.coe_nnreal_ennreal]
      _ ≤ (∫⁻ x : α, f x ∂μ) + ε / 2 + ε / 2 := by grw [wint]
      _ = (∫⁻ x : α, f x ∂μ) + ε := by rw [add_assoc, ENNReal.add_halves]

/-- Given an almost everywhere measurable function `f` with values in `ℝ≥0` in a sigma-finite space,
there exists a lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable [SigmaFinite μ]
 (f : α -> Real>=0) (fmeas : AEMeasurable f μ) {ε : Real>=0∞} (ε0 : ε != 0) : ex
ists g : α -> Real>=0∞, (forall x, (f x : Real>=0∞) < g x) ∧ LowerSemicontinuous
 g ∧ (∫⁻ x, g x ∂μ) <= (∫⁻ x, f x ∂μ) + ε
参数：f : α -> Real>=0；fmeas : AEMeasurable f μ；ε0 : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `MeasureTheory.exists_lt_lowerSemicontinuous_lintegral_ge`：exists_lt_lowe
rSemicontinuous_lintegral_ge [SigmaFinite μ] (f : α -> Real>=0) (fmeas : Measura
ble f) {ε : Real>=0∞} (ε0 : ε != 0) : exists g…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.exists_le_lowerSemicontinuous_lintegral_ge`：exists_le_lowe
rSemicontinuous_lintegral_ge (f : α -> Real>=0∞) (hf : Measurable f) {ε : Real>=
0∞} (εpos : ε != 0) : exists g : α -> Real>=0∞…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LowerSemicontinuous.add`：LowerSemicontinuous.add {f g : α -> γ} (hf : Lo
werSemicontinuous f) (hg : LowerSemicontinuous g) : LowerSemicontinuous fun z =>
 f z + g z
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `LowerSemicontinuous.measurable`：LowerSemicontinuous.measurable [Topologi
calSpace δ] [OpensMeasurableSpace δ] {f : δ -> α} (hf : LowerSemicontinuous f) :
 Measurable f
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Given an almost everywhere measurable function `f` with values in `ℝ≥0` in a sig
ma-finite space,
there exists a lower semicontinuous function `g > f` with integral arbitrarily c
lose to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable [SigmaFinite μ] (f : α → ℝ≥0)
    (fmeas : AEMeasurable f μ) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε := by
  have : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
  rcases exists_lt_lowerSemicontinuous_lintegral_ge μ (fmeas.mk f) fmeas.measurable_mk this with
    ⟨g0, f_lt_g0, g0_cont, g0_int⟩
  rcases exists_measurable_superset_of_null fmeas.ae_eq_mk with ⟨s, hs, smeas, μs⟩
  rcases exists_le_lowerSemicontinuous_lintegral_ge μ (s.indicator fun _x => ∞)
      (measurable_const.indicator smeas) this with
    ⟨g1, le_g1, g1_cont, g1_int⟩
  refine ⟨fun x => g0 x + g1 x, fun x => ?_, g0_cont.add g1_cont, ?_⟩
  · by_cases h : x ∈ s
    · have := le_g1 x
      simp only [h, Set.indicator_of_mem, top_le_iff] at this
      simp [this]
    · have : f x = fmeas.mk f x := by rw [Set.compl_subset_comm] at hs; exact hs h
      rw [this]
      exact (f_lt_g0 x).trans_le le_self_add
  · calc
      ∫⁻ x, g0 x + g1 x ∂μ = (∫⁻ x, g0 x ∂μ) + ∫⁻ x, g1 x ∂μ :=
        lintegral_add_left g0_cont.measurable _
      _ ≤ (∫⁻ x, f x ∂μ) + ε / 2 + (0 + ε / 2) := by
        refine add_le_add ?_ ?_
        · convert! g0_int using 2
          exact lintegral_congr_ae (fmeas.ae_eq_mk.fun_comp _)
        · convert! g1_int
          simp only [smeas, μs, lintegral_const, Set.univ_inter, MeasurableSet.univ,
            lintegral_indicator, mul_zero, restrict_apply]
      _ = (∫⁻ x, f x ∂μ) + ε := by simp only [add_assoc, ENNReal.add_halves, zero_add]

variable {μ}

/-- Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.exists_lt_lowerSemicontinuous_integral_gt_nnreal** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_lt_lowerSemicontinuous_integral_gt_nnreal [SigmaFinite μ] (f : α ->
 Real>=0) (fint : Integrable (fun x => (f x : Real)) μ) {ε : Real} (εpos : 0 < ε
) : exists g : α -> Real>=0∞, (forall x, (f x : Real>=0∞) < g x) ∧ LowerSemicont
inuous g ∧ (forallᵐ x ∂μ, g x < ⊤) ∧ Integrable (fun x => (g x).toReal) μ ∧ (∫ x
, (g x).toReal ∂μ) < (∫ x, ↑(f x) ∂μ) + ε
参数：f : α -> Real>=0；fint : Integrable (fun x => (f x : Real)) μ；εpos : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.real_toNNReal`：∀ {α : Type u_1} {m₀ :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.A
EStronglyMeasurable f μ → MeasureTheor…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_ofNNReal`：hasFiniteIntegral_iff_ofNN
Real {f : α -> Real>=0} : HasFiniteIntegral (fun x => (f x : Real)) μ ↔ (∫⁻ a, f
 a ∂μ) < ∞
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable
`：exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable [SigmaFinite μ] (f 
: α -> Real>=0) (fmeas : AEMeasurable f μ) {ε : Real>=0∞} (ε0 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `LowerSemicontinuous.measurable`：LowerSemicontinuous.measurable [Topologi
calSpace δ] [OpensMeasurableSpace δ] {f : δ -> α} (hf : LowerSemicontinuous f) :
 Measurable f
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, t
here exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of
 `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem exists_lt_lowerSemicontinuous_integral_gt_nnreal [SigmaFinite μ] (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧
      LowerSemicontinuous g ∧
      (∀ᵐ x ∂μ, g x < ⊤) ∧
      Integrable (fun x => (g x).toReal) μ ∧ (∫ x, (g x).toReal ∂μ) < (∫ x, ↑(f x) ∂μ) + ε := by
  have fmeas : AEMeasurable f μ := by
    convert! fint.aestronglyMeasurable.real_toNNReal.aemeasurable
    simp only [Real.toNNReal_coe]
  lift ε to ℝ≥0 using εpos.le
  obtain ⟨δ, δpos, hδε⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < ε := exists_between εpos
  have int_f_ne_top : (∫⁻ a : α, f a ∂μ) ≠ ∞ :=
    (hasFiniteIntegral_iff_ofNNReal.1 fint.hasFiniteIntegral).ne
  rcases exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable μ f fmeas
      (ENNReal.coe_ne_zero.2 δpos.ne') with
    ⟨g, f_lt_g, gcont, gint⟩
  have gint_ne : (∫⁻ x : α, g x ∂μ) ≠ ∞ := ne_top_of_le_ne_top (by simpa) gint
  have g_lt_top : ∀ᵐ x : α ∂μ, g x < ∞ := ae_lt_top gcont.measurable gint_ne
  have Ig : (∫⁻ a : α, ENNReal.ofReal (g a).toReal ∂μ) = ∫⁻ a : α, g a ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [g_lt_top] with _ hx
    simp only [hx.ne, ENNReal.ofReal_toReal, Ne, not_false_iff]
  refine ⟨g, f_lt_g, gcont, g_lt_top, ?_, ?_⟩
  · refine ⟨gcont.measurable.ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
    simp only [hasFiniteIntegral_iff_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    convert! gint_ne.lt_top using 1
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    · calc
        ENNReal.toReal (∫⁻ a : α, ENNReal.ofReal (g a).toReal ∂μ) =
            ENNReal.toReal (∫⁻ a : α, g a ∂μ) := by congr 1
        _ ≤ ENNReal.toReal ((∫⁻ a : α, f a ∂μ) + δ) := by
          apply ENNReal.toReal_mono _ gint
          simpa using int_f_ne_top
        _ = ENNReal.toReal (∫⁻ a : α, f a ∂μ) + δ := by
          rw [ENNReal.toReal_add int_f_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal]
        _ < ENNReal.toReal (∫⁻ a : α, f a ∂μ) + ε := by gcongr
        _ = (∫⁻ a : α, ENNReal.ofReal ↑(f a) ∂μ).toReal + ε := by simp
    · apply Filter.Eventually.of_forall fun x => _; simp
    · exact fmeas.coe_nnreal_real.aestronglyMeasurable
    · apply Filter.Eventually.of_forall fun x => _; simp
    · apply gcont.measurable.ennreal_toReal.aemeasurable.aestronglyMeasurable

/-! ### Upper semicontinuous lower bound for nonnegative functions -/


/-- Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.SimpleFunc.exists_upperSemicontinuous_le_lintegral_le** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] 
[BorelSpace α] {μ : MeasureTheory.Measure α}   [μ.WeaklyRegular] (f : MeasureThe
ory.SimpleFunc α NNReal),   ∫⁻ (x : α), ↑(f x) ∂μ ≠ ⊤ →     ∀ {ε : ENNReal},    
   ε ≠ 0 → ∃ g, (∀ (x : α), g x ≤ f x) ∧ UpperSemicontinuous g ∧ ∫⁻ (x : α), ↑(f
 x) ∂μ ≤ ∫⁻ (x : α), ↑(g x) ∂μ + ε
参数：f : MeasureTheory.SimpleFunc α NNReal；x : α；f x；∀ (x : α), g x ≤ f x；x : α；f 
x；x : α；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.piecewise.congr_simp`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] (s s_1 : Set α) (e_s : s = s_1) (hs : Measurab
leSet s)   (f f_1 : MeasureTheory.S…
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_same`：piecewise_same (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) : piecewise s hs f f = f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `ENNReal.coe_indicator`：coe_indicator {α} (s : Set α) (f : α -> Real>=0) 
(a : α) : ((s.indicator f a : Real>=0) : Real>=0∞) = s.indicator (fun x => ↑(f x
)) a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.div_pos_iff`：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicont
inuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in 
terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem SimpleFunc.exists_upperSemicontinuous_le_lintegral_le (f : α →ₛ ℝ≥0)
    (int_f : (∫⁻ x, f x ∂μ) ≠ ∞) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
      (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, g x ∂μ) + ε := by
  induction f using MeasureTheory.SimpleFunc.induction generalizing ε with
  | @const c s hs =>
    by_cases hc : c = 0
    · exact ⟨fun _ => 0, by simp [hc, upperSemicontinuous_const]⟩
    have μs_lt_top : μ s < ∞ := by simpa [hs, hc, ENNReal.mul_eq_top, lt_top_iff_ne_top] using int_f
    have : (0 : ℝ≥0∞) < ε / c := ENNReal.div_pos_iff.2 ⟨ε0, ENNReal.coe_ne_top⟩
    obtain ⟨F, Fs, F_closed, μF⟩ : ∃ (F : _), F ⊆ s ∧ IsClosed F ∧ μ s < μ F + ε / c :=
      hs.exists_isClosed_lt_add μs_lt_top.ne this.ne'
    refine
      ⟨Set.indicator F fun _ => c, fun x => ?_, F_closed.upperSemicontinuous_indicator zero_le,
        ?_⟩
    · simp only [SimpleFunc.coe_const, SimpleFunc.const_zero, SimpleFunc.coe_zero,
        Set.piecewise_eq_indicator, SimpleFunc.coe_piecewise, ← Function.const_def]
      grw [Fs]
    · suffices (c : ℝ≥0∞) * μ s ≤ c * μ F + ε by
        simpa only [hs, F_closed.measurableSet, SimpleFunc.coe_const, Function.const_apply,
          lintegral_const, ENNReal.coe_indicator, Set.univ_inter, MeasurableSet.univ,
          SimpleFunc.const_zero, lintegral_indicator, SimpleFunc.coe_zero,
          Set.piecewise_eq_indicator, SimpleFunc.coe_piecewise, Measure.restrict_apply]
      calc
        (c : ℝ≥0∞) * μ s ≤ c * (μ F + ε / c) := by grw [μF]
        _ = c * μ F + ε := by
          simp_rw [mul_add]
          rw [ENNReal.mul_div_cancel _ ENNReal.coe_ne_top]
          simpa using hc
  | @add f₁ f₂ _ h₁ h₂ =>
    have A : ((∫⁻ x : α, f₁ x ∂μ) + ∫⁻ x : α, f₂ x ∂μ) ≠ ⊤ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    rcases h₁ (ENNReal.add_ne_top.1 A).1 (ENNReal.half_pos ε0).ne' with
      ⟨g₁, f₁_le_g₁, g₁cont, g₁int⟩
    rcases h₂ (ENNReal.add_ne_top.1 A).2 (ENNReal.half_pos ε0).ne' with
      ⟨g₂, f₂_le_g₂, g₂cont, g₂int⟩
    refine
      ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, ?_⟩
    simp only [SimpleFunc.coe_add, ENNReal.coe_add, Pi.add_apply]
    rw [lintegral_add_left f₁.measurable.coe_nnreal_ennreal,
      lintegral_add_left g₁cont.measurable.coe_nnreal_ennreal]
    convert! add_le_add g₁int g₂int using 1
    conv_lhs => rw [← ENNReal.add_halves ε]
    abel

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.exists_upperSemicontinuous_le_lintegral_le** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：exists_upperSemicontinuous_le_lintegral_le (f : α -> Real>=0) (int_f : (∫⁻
 x, f x ∂μ) != ∞) {ε : Real>=0∞} (ε0 : ε != 0) : exists g : α -> Real>=0, (foral
l x, g x <= f x) ∧ UpperSemicontinuous g ∧ (∫⁻ x, f x ∂μ) <= (∫⁻ x, g x ∂μ) + ε
参数：f : α -> Real>=0；int_f : (∫⁻ x, f x ∂μ) != ∞；ε0 : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.biSup_add'`：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : 
ι -> Real>=0∞) : (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.lintegral_eq_nnreal`：lintegral_eq_nnreal {m : MeasurableSp
ace α} (f : α -> Real>=0∞) (μ : Measure α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0
) (_ : forall x, ↑(φ x)…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.SimpleFunc.exists_upperSemicontinuous_le_lintegral_le`：∀ {
α : Type u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpa
ce α] {μ : MeasureTheory.Measure α}   [μ.WeaklyRegular] (…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a

--- 原说明 ---
Given an integrable function `f` with values in `ℝ≥0`, there exists an upper sem
icontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in 
terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem exists_upperSemicontinuous_le_lintegral_le (f : α → ℝ≥0) (int_f : (∫⁻ x, f x ∂μ) ≠ ∞)
    {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
      (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, g x ∂μ) + ε := by
  obtain ⟨fs, fs_le_f, int_fs⟩ :
    ∃ fs : α →ₛ ℝ≥0, (∀ x, fs x ≤ f x) ∧ (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, fs x ∂μ) + ε / 2 := by
    have := ENNReal.lt_add_right int_f (ENNReal.half_pos ε0).ne'
    conv_rhs at this => rw [lintegral_eq_nnreal (fun x => (f x : ℝ≥0∞)) μ]
    rw [ENNReal.biSup_add'] at this <;> [skip; exact ⟨0, fun x => by simp⟩]
    simp only [lt_iSup_iff] at this
    rcases this with ⟨fs, fs_le_f, int_fs⟩
    refine ⟨fs, fun x => by simpa only [ENNReal.coe_le_coe] using fs_le_f x, ?_⟩
    convert! int_fs.le
    rw [← SimpleFunc.lintegral_eq_lintegral]
    simp only [SimpleFunc.coe_map, Function.comp_apply]
  have int_fs_lt_top : (∫⁻ x, fs x ∂μ) ≠ ∞ := by
    refine ne_top_of_le_ne_top int_f (lintegral_mono fun x => ?_)
    simpa only [ENNReal.coe_le_coe] using fs_le_f x
  obtain ⟨g, g_le_fs, gcont, gint⟩ :
    ∃ g : α → ℝ≥0,
      (∀ x, g x ≤ fs x) ∧ UpperSemicontinuous g ∧ (∫⁻ x, fs x ∂μ) ≤ (∫⁻ x, g x ∂μ) + ε / 2 :=
    fs.exists_upperSemicontinuous_le_lintegral_le int_fs_lt_top (ENNReal.half_pos ε0).ne'
  refine ⟨g, fun x => (g_le_fs x).trans (fs_le_f x), gcont, ?_⟩
  calc
    (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, fs x ∂μ) + ε / 2 := int_fs
    _ ≤ (∫⁻ x, g x ∂μ) + ε / 2 + ε / 2 := add_le_add gint le_rfl
    _ = (∫⁻ x, g x ∂μ) + ε := by rw [add_assoc, ENNReal.add_halves]

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
/-
**MeasureTheory.exists_upperSemicontinuous_le_integral_le** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：exists_upperSemicontinuous_le_integral_le (f : α -> Real>=0) (fint : Integ
rable (fun x => (f x : Real)) μ) {ε : Real} (εpos : 0 < ε) : exists g : α -> Rea
l>=0, (forall x, g x <= f x) ∧ UpperSemicontinuous g ∧ Integrable (fun x => (g x
 : Real)) μ ∧ (∫ x, (f x : Real) ∂μ) - ε <= ∫ x, ↑(g x) ∂μ
参数：f : α -> Real>=0；fint : Integrable (fun x => (f x : Real)) μ；εpos : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_ofNNReal`：hasFiniteIntegral_iff_ofNN
Real {f : α -> Real>=0} : HasFiniteIntegral (fun x => (f x : Real)) μ ↔ (∫⁻ a, f
 a ∂μ) < ∞
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.exists_upperSemicontinuous_le_lintegral_le`：exists_upperSe
micontinuous_le_lintegral_le (f : α -> Real>=0) (int_f : (∫⁻ x, f x ∂μ) != ∞) {ε
 : Real>=0∞} (ε0 : ε != 0) : exists g : α -> R…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `UpperSemicontinuous.measurable`：UpperSemicontinuous.measurable [Topologi
calSpace δ] [OpensMeasurableSpace δ] {f : δ -> α} (hf : UpperSemicontinuous f) :
 Measurable f
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Given an integrable function `f` with values in `ℝ≥0`, there exists an upper sem
icontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in 
terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_
integral_lt`.
-/
theorem exists_upperSemicontinuous_le_integral_le (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0,
      (∀ x, g x ≤ f x) ∧
      UpperSemicontinuous g ∧
      Integrable (fun x => (g x : ℝ)) μ ∧ (∫ x, (f x : ℝ) ∂μ) - ε ≤ ∫ x, ↑(g x) ∂μ := by
  lift ε to ℝ≥0 using εpos.le
  rw [NNReal.coe_pos, ← ENNReal.coe_pos] at εpos
  have If : (∫⁻ x, f x ∂μ) < ∞ := hasFiniteIntegral_iff_ofNNReal.1 fint.hasFiniteIntegral
  rcases exists_upperSemicontinuous_le_lintegral_le f If.ne εpos.ne' with ⟨g, gf, gcont, gint⟩
  have Ig : (∫⁻ x, g x ∂μ) < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) If
    simpa using gf x
  refine ⟨g, gf, gcont, ?_, ?_⟩
  · refine
      Integrable.mono fint gcont.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by simp [gf x]
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    · rw [sub_le_iff_le_add]
      convert! ENNReal.toReal_mono _ gint
      · simp
      · rw [ENNReal.toReal_add Ig.ne ENNReal.coe_ne_top]; simp
      · simpa using Ig.ne
    · apply Filter.Eventually.of_forall; simp
    · exact gcont.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable
    · apply Filter.Eventually.of_forall; simp
    · exact fint.aestronglyMeasurable

/-! ### Vitali-Carathéodory theorem -/


/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g > f` which is lower semicontinuous, with integral arbitrarily close
to that of `f`. This function has to be `EReal`-valued in general. -/
/-
**MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：exists_lt_lowerSemicontinuous_integral_lt [SigmaFinite μ] (f : α -> Real) 
(hf : Integrable f μ) {ε : Real} (εpos : 0 < ε) : exists g : α -> EReal, (forall
 x, (f x : EReal) < g x) ∧ LowerSemicontinuous g ∧ Integrable (fun x => EReal.to
Real (g x)) μ ∧ (forallᵐ x ∂μ, g x < ⊤) ∧ (∫ x, EReal.toReal (g x) ∂μ) < (∫ x, f
 x ∂μ) + ε
参数：f : α -> Real；hf : Integrable f μ；εpos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasureTheory.Integrable.real_toNNReal`：∀ {α : Type u_1} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f
 μ → MeasureTheory.Integrabl…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_lt_lowerSemicontinuous_integral_gt_nnreal`：exists_l
t_lowerSemicontinuous_integral_gt_nnreal [SigmaFinite μ] (f : α -> Real>=0) (fin
t : Integrable (fun x => (f x : Real)) μ) {ε : Real}…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.exists_upperSemicontinuous_le_integral_le`：exists_upperSem
icontinuous_le_integral_le (f : α -> Real>=0) (fint : Integrable (fun x => (f x 
: Real)) μ) {ε : Real} (εpos : 0 < ε) : exist…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.toReal_sub`：toReal_sub {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) 
(hy : y != ⊤) (h'y : y != ⊥) : toReal (x - y) = toReal x - toReal y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal`：coe_real_ereal_eq
_coe_toNNReal_sub_coe_toNNReal (x : Real) : (x : EReal) = Real.toNNReal x - Real
.toNNReal (-x)
· 使用定理 `EReal.sub_lt_sub_of_lt_of_le`：sub_lt_sub_of_lt_of_le {x y z t : EReal} (
h : x < y) (h' : z <= t) (hz : z != ⊥) (ht : t != ⊤) : x - t < y - z
· 使用定理 `LowerSemicontinuous.add'`：LowerSemicontinuous.add' {f g : α -> γ} (hf : 
LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hcont : forall x, Continuou
sAt (fun p : γ…
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `Continuous.comp_lowerSemicontinuous`：Continuous.comp_lowerSemicontinuous
 {g : γ -> δ} {f : α -> γ} (hg : Continuous g) (hf : LowerSemicontinuous f) (gmo
n : Monotone g) : LowerSe…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `continuous_coe_ennreal_ereal`：Continuous ENNReal.toEReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 125 条，此处仅展示前 30 条）

--- 原说明 ---
**Vitali-Carathéodory Theorem**: given an integrable real function `f`, there ex
ists an
integrable function `g > f` which is lower semicontinuous, with integral arbitra
rily close
to that of `f`. This function has to be `EReal`-valued in general.
-/
theorem exists_lt_lowerSemicontinuous_integral_lt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → EReal,
      (∀ x, (f x : EReal) < g x) ∧
      LowerSemicontinuous g ∧
      Integrable (fun x => EReal.toReal (g x)) μ ∧
      (∀ᵐ x ∂μ, g x < ⊤) ∧ (∫ x, EReal.toReal (g x) ∂μ) < (∫ x, f x ∂μ) + ε := by
  let δ : ℝ≥0 := .mk (ε / 2) (half_pos εpos).le
  have δpos : 0 < δ := half_pos εpos
  let fp : α → ℝ≥0 := fun x => Real.toNNReal (f x)
  have int_fp : Integrable (fun x => (fp x : ℝ)) μ := hf.real_toNNReal
  rcases exists_lt_lowerSemicontinuous_integral_gt_nnreal fp int_fp δpos with
    ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩
  let fm : α → ℝ≥0 := fun x => Real.toNNReal (-f x)
  have int_fm : Integrable (fun x => (fm x : ℝ)) μ := hf.neg.real_toNNReal
  rcases exists_upperSemicontinuous_le_integral_le fm int_fm δpos with
    ⟨gm, gm_le_fm, gmcont, gm_integrable, gmint⟩
  let g : α → EReal := fun x => (gp x : EReal) - gm x
  have ae_g : ∀ᵐ x ∂μ, (g x).toReal = (gp x : EReal).toReal - (gm x : EReal).toReal := by
    filter_upwards [gp_lt_top] with _ hx
    rw [EReal.toReal_sub] <;> simp [hx.ne]
  refine ⟨g, ?lt, ?lsc, ?int, ?aelt, ?intlt⟩
  case int =>
    show Integrable (fun x => EReal.toReal (g x)) μ
    rw [integrable_congr ae_g]
    convert! gp_integrable.sub gm_integrable
    simp
  case intlt =>
    show (∫ x : α, (g x).toReal ∂μ) < (∫ x : α, f x ∂μ) + ε
    exact
      calc
        (∫ x : α, (g x).toReal ∂μ) = ∫ x : α, EReal.toReal (gp x) - EReal.toReal (gm x) ∂μ :=
          integral_congr_ae ae_g
        _ = (∫ x : α, EReal.toReal (gp x) ∂μ) - ∫ x : α, ↑(gm x) ∂μ := by
          simp only [EReal.toReal_coe_ennreal, ENNReal.coe_toReal]
          exact integral_sub gp_integrable gm_integrable
        _ < (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ∫ x : α, ↑(gm x) ∂μ := by
          apply sub_lt_sub_right
          convert! gpint
          simp only [EReal.toReal_coe_ennreal]
        _ ≤ (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ((∫ x : α, ↑(fm x) ∂μ) - δ) := sub_le_sub_left gmint _
        _ = (∫ x : α, f x ∂μ) + 2 * δ := by
          simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf]; ring
        _ = (∫ x : α, f x ∂μ) + ε := by congr 1; simp [field, δ]
  case aelt =>
    show ∀ᵐ x : α ∂μ, g x < ⊤
    filter_upwards [gp_lt_top] with ?_ hx
    simp only [g, sub_eq_add_neg, Ne, (EReal.add_lt_top _ _).ne, lt_top_iff_ne_top,
      lt_top_iff_ne_top.1 hx, EReal.coe_ennreal_eq_top_iff, not_false_iff, EReal.neg_eq_top_iff,
      EReal.coe_ennreal_ne_bot]
  case lt =>
    show ∀ x, (f x : EReal) < g x
    intro x
    rw [EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (f x)]
    refine EReal.sub_lt_sub_of_lt_of_le ?_ ?_ ?_ ?_
    · simp only [EReal.coe_ennreal_lt_coe_ennreal_iff]; exact fp_lt_gp x
    · simp only [ENNReal.coe_le_coe, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact gm_le_fm x
    · simp
    · simp
  case lsc =>
    show LowerSemicontinuous g
    apply LowerSemicontinuous.add'
    · exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous gpcont fun x y hxy =>
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy
    · apply continuous_neg.comp_upperSemicontinuous_antitone _ fun x y hxy =>
          EReal.neg_le_neg_iff.2 hxy
      apply continuous_coe_ennreal_ereal.comp_upperSemicontinuous _ fun x y hxy =>
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy
      exact ENNReal.continuous_coe.comp_upperSemicontinuous gmcont fun x y hxy =>
          ENNReal.coe_le_coe.2 hxy
    · intro x
      exact EReal.continuousAt_add (by simp) (by simp)

/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g < f` which is upper semicontinuous, with integral arbitrarily close to that
of `f`. This function has to be `EReal`-valued in general. -/
/-
**MeasureTheory.exists_upperSemicontinuous_lt_integral_gt** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：exists_upperSemicontinuous_lt_integral_gt [SigmaFinite μ] (f : α -> Real) 
(hf : Integrable f μ) {ε : Real} (εpos : 0 < ε) : exists g : α -> EReal, (forall
 x, (g x : EReal) < f x) ∧ UpperSemicontinuous g ∧ Integrable (fun x => EReal.to
Real (g x)) μ ∧ (forallᵐ x ∂μ, ⊥ < g x) ∧ (∫ x, f x ∂μ) < (∫ x, EReal.toReal (g 
x) ∂μ) + ε
参数：f : α -> Real；hf : Integrable f μ；εpos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt`：exists_lt_lower
Semicontinuous_integral_lt [SigmaFinite μ] (f : α -> Real) (hf : Integrable f μ)
 {ε : Real} (εpos : 0 < ε) : exists g : α -> …
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.neg_lt_comm`：neg_lt_comm {a b : EReal} : -a < b ↔ -b < a
· 使用定理 `Continuous.comp_lowerSemicontinuous_antitone`：Continuous.comp_lowerSemic
ontinuous_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuous g) (hf : LowerSemi
continuous f) (gmon : Antitone g) …
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
· 使用定理 `EReal.instContinuousNeg`：ContinuousNeg EReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.toReal_neg_eq`：∀ {a : EReal}, (-a).toReal = -a.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
**Vitali-Carathéodory Theorem**: given an integrable real function `f`, there ex
ists an
integrable function `g < f` which is upper semicontinuous, with integral arbitra
rily close to that
of `f`. This function has to be `EReal`-valued in general.
-/
theorem exists_upperSemicontinuous_lt_integral_gt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → EReal,
      (∀ x, (g x : EReal) < f x) ∧
      UpperSemicontinuous g ∧
      Integrable (fun x => EReal.toReal (g x)) μ ∧
      (∀ᵐ x ∂μ, ⊥ < g x) ∧ (∫ x, f x ∂μ) < (∫ x, EReal.toReal (g x) ∂μ) + ε := by
  rcases exists_lt_lowerSemicontinuous_integral_lt (fun x => -f x) hf.neg εpos with
    ⟨g, g_lt_f, gcont, g_integrable, g_lt_top, gint⟩
  refine ⟨fun x => -g x, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x => EReal.neg_lt_comm.1 (by simpa only [EReal.coe_neg] using g_lt_f x)
  · exact
      continuous_neg.comp_lowerSemicontinuous_antitone gcont fun x y hxy =>
        EReal.neg_le_neg_iff.2 hxy
  · convert! g_integrable.neg
    simp
  · simpa [bot_lt_iff_ne_bot, lt_top_iff_ne_top] using g_lt_top
  · simp_rw [integral_neg, lt_neg_add_iff_add_lt] at gint
    rw [add_comm] at gint
    simpa [integral_neg] using gint

end MeasureTheory

