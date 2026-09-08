/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# `f'` is interval integrable for certain classes of functions `f`

This file proves that:
* `MonotoneOn.intervalIntegrable_deriv`: If `f` is monotone on `a..b`, then `f'` is interval
  integrable on `a..b`.
* `MonotoneOn.intervalIntegral_deriv_mem_uIcc`: If `f` is monotone on `a..b`, then the integral of
  `f'` on `a..b` is in `uIcc 0 (f b - f a)`.
* `BoundedVariationOn.intervalIntegrable_deriv`: If `f` has bounded variation on `a..b`,
  then `f'` is interval integrable on `a..b`.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`: If `f` is absolutely continuous on
  `a..b`, then `f'` is interval integrable on `a..b`.

## Tags
interval integrable, monotone, bounded variation, absolutely continuous
-/

public section

open MeasureTheory Set Filter

open scoped Topology

/-- If `f` is monotone on `[a, b]`, then `f'` is the limit of `G n` a.e. on `[a, b]`, where each
`G n` is `AEStronglyMeasurable` and the liminf of the lower Lebesgue integral of `‖G n ·‖ₑ` is at
most `f b - f a`. -/
/-
**MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le {f : Real -> Rea
l} {a b : Real} (hab : a <= b) (hf : MonotoneOn f (Icc a b)) : exists G : (Nat -
> Real -> Real), (forallᵐ x ∂volume.restrict (Icc a b), Filter.Tendsto (fun (n :
 Nat) => G n x) Filter.atTop (𝓝 (deriv f x))) ∧ (forall (n : Nat), AEStronglyMea
surable (G n) (volume.restrict (Icc a b))) ∧ liminf (fun (n : Nat) => ∫⁻ (x : Re
al) in Icc a b, ‖G n x‖ₑ) atTop <= ENNReal.ofReal (f b - f a)
参数：hab : a <= b；hf : MonotoneOn f (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `monotoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, MonotoneOn f Set.univ ↔ Monotone f
· 使用引理 `MonotoneOn.comp`：MonotoneOn.comp (hg : MonotoneOn g t) (hf : MonotoneOn 
f s) (hs : Set.MapsTo f s t) : MonotoneOn (g ∘ f) s
· 使用定理 `MonotoneOn.max`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: LinearOrder β] {f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s → 
Mono…
· 使用定理 `monotoneOn_const`：monotoneOn_const [Preorder α] [Preorder β] {c : β} {s 
: Set α} : MonotoneOn (fun _ : α => c) s
· 使用定理 `MonotoneOn.min`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: LinearOrder β] {f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s → 
Mono…
· 使用定理 `monotoneOn_id`：monotoneOn_id [Preorder α] {s : Set α} : MonotoneOn id s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用引理 `Set.EqOn.deriv`：Set.EqOn.deriv {f g : 𝕜 -> F} {s : Set 𝕜} (hfg : s.EqOn 
f g) (hs : IsOpen s) : s.EqOn (deriv f) (deriv g)
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MonotoneOn.intervalIntegrable_slope`：MonotoneOn.intervalIntegrable_slope
 {f : Real -> Real} {a b c : Real} (hf : MonotoneOn f (Icc a (b + c))) (hab : a 
<= b) (hc : 0 <= c) : Int…
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 86 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is monotone on `[a, b]`, then `f'` is the limit of `G n` a.e. on `[a, b]`
, where each
`G n` is `AEStronglyMeasurable` and the liminf of the lower Lebesgue integral of
 `‖G n ·‖ₑ` is at
most `f b - f a`.
-/
lemma MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    ∃ G : (ℕ → ℝ → ℝ), (∀ᵐ x ∂volume.restrict (Icc a b),
      Filter.Tendsto (fun (n : ℕ) ↦ G n x) Filter.atTop (𝓝 (deriv f x))) ∧
      (∀ (n : ℕ), AEStronglyMeasurable (G n) (volume.restrict (Icc a b))) ∧
      liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G n x‖ₑ) atTop ≤
        ENNReal.ofReal (f b - f a) := by
  /- Proof Sketch: Extend `f` on `[a, b]` to a function `g` on `ℝ` by defining `g x = f a` for
  `x < a` and `g x = f b` for `x > b`. `g` is globally monotone and `g'` agrees with `f'` on
  `(a, b)`. We let `G c x = slope g x (x + c)` for `c > 0`. Then `G c x` is nonnegative,
  `∫⁻ (x : ℝ) in Icc a b, ‖G c x‖ₑ ≤ f b - f a`, and `G c x` tends to `f' x` as `c` tends to `0`
  from the right. The function `fun n x ↦ G (n : ℝ)⁻¹ x` is a witness to the conclusion of the
  lemma. -/
  let g (x : ℝ) : ℝ := f (max a (min x b))
  have hg : Monotone g := monotoneOn_univ.mp <| hf.comp
    (monotoneOn_const.max <| monotoneOn_id.min monotoneOn_const) (by simpa)
  have hfg : EqOn f g (Ioo a b) := fun x ⟨hxa, hxb⟩ => congrArg f <|
    min_eq_left hxb.le |>.symm ▸ (max_eq_right hxa.le).symm
  replace hfg := hfg.deriv isOpen_Ioo
  let G (c x : ℝ) := slope g x (x + c)
  have G_integrable (n : ℕ) : Integrable (G (↑n)⁻¹) (volume.restrict (Icc a b)) := by
    have := hg.monotoneOn (Icc a (b + (n : ℝ)⁻¹)) |>.intervalIntegrable_slope hab (by simp)
    exact intervalIntegrable_iff_integrableOn_Icc_of_le hab |>.mp this
  refine ⟨fun n x ↦ G (n : ℝ)⁻¹ x, ?_, fun n ↦ G_integrable n |>.aestronglyMeasurable, ?_⟩
  · rw [← restrict_Ioo_eq_restrict_Icc, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hg.ae_differentiableAt] with x hx₁ hx₂
    rw [hfg hx₂]
    exact hx₁.hasDerivAt.tendsto_slope.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by convert! tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)); simp)
      (by simp [eventually_ne_atTop 0])
  · calc
      _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ (x : ℝ) in Icc a b, (G (n : ℝ)⁻¹) x)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (G_integrable n)]
        congr with y
        exact abs_eq_self.mpr (hg.monotoneOn univ |>.slope_nonneg trivial trivial)
      _ ≤ ENNReal.ofReal (g b - g a) := by
        refine Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall fun n ↦ ENNReal.ofReal_le_ofReal ?_)
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        convert!
          hg.monotoneOn (Icc a (b + (n : ℝ)⁻¹)) |>.intervalIntegral_slope_le hab (by simp) using 2
        simp [g]
      _ = ENNReal.ofReal (f b - f a) := by grind

/-- If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b`. -/
/-
**MonotoneOn.intervalIntegrable_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.intervalIntegrable_deriv {f : Real -> Real} {a b : Real} (hf : 
MonotoneOn f (uIcc a b)) : IntervalIntegrable (deriv f) volume a b
参数：hf : MonotoneOn f (uIcc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le`：MonotoneOn.ex
ists_tendsto_deriv_liminf_lintegral_enorm_le {f : Real -> Real} {a b : Real} (ha
b : a <= b) (hf : MonotoneOn f (Icc a b)) : exi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `MeasureTheory.integrable_of_tendsto`：integrable_of_tendsto {G : Nat -> R
eal -> Real} {f : Real -> Real} {μ : Measure Real} (hGf : forallᵐ x ∂μ, Tendsto 
(fun (n : Nat) => G n x) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b`.
-/
theorem MonotoneOn.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  wlog hab : a ≤ b generalizing a b with h
  · exact h (uIcc_comm a b ▸ hf) (by linarith) |>.symm
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G n x‖ₑ) atTop ≠ ⊤ :=
    lt_of_le_of_lt hG' ENNReal.ofReal_lt_top |>.ne_top
  have integrable_f_deriv := integrable_of_tendsto hGf hG hG'₀
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr integrable_f_deriv

/-- If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b` and the integral of
`f'` on `a..b` is in between `0` and `f b - f a`. -/
/-
**MonotoneOn.intervalIntegral_deriv_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.intervalIntegral_deriv_mem_uIcc {f : Real -> Real} {a b : Real}
 (hf : MonotoneOn f (uIcc a b)) : ∫ x in a..b, deriv f x in uIcc 0 (f b - f a)
参数：hf : MonotoneOn f (uIcc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le`：MonotoneOn.ex
ists_tendsto_deriv_liminf_lintegral_enorm_le {f : Real -> Real} {a b : Real} (ha
b : a <= b) (hf : MonotoneOn f (Icc a b)) : exi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `MeasureTheory.integrable_of_tendsto`：integrable_of_tendsto {G : Nat -> R
eal -> Real} {f : Real -> Real} {μ : Measure Real} (hGf : forallᵐ x ∂μ, Tendsto 
(fun (n : Nat) => G n x) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b` and the
 integral of
`f'` on `a..b` is in between `0` and `f b - f a`.
-/
theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    ∫ x in a..b, deriv f x ∈ uIcc 0 (f b - f a) := by
  wlog hab : a ≤ b generalizing a b with h
  · specialize h (uIcc_comm a b ▸ hf) (by linarith)
    have : f b ≤ f a := hf (by simp) (by simp) (by linarith)
    rw [intervalIntegral.integral_symm, uIcc_of_ge (by linarith)]
    refine neg_mem_Icc_iff.mpr ?_
    simp only [neg_zero, neg_sub]
    rwa [uIcc_of_le (by linarith)] at h
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G n x‖ₑ) atTop ≠ ⊤ :=
    lt_of_le_of_lt hG' ENNReal.ofReal_lt_top |>.ne_top
  have integrable_f_deriv := integrable_of_tendsto hGf hG hG'₀
  rw [MeasureTheory.ae_restrict_iff' (by simp)] at hGf
  rw [← uIcc_of_le hab] at hGf hG hG'
  have : f a ≤ f b := hf (by simp [hab]) (by simp [hab]) hab
  rw [uIcc_of_le (by linarith), mem_Icc]
  have f_deriv_nonneg {x : ℝ} (hx : x ∈ Ioo a b) : 0 ≤ deriv f x := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.left hx.right)]
    exact hf.derivWithin_nonneg
  constructor
  · apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall @f_deriv_nonneg
  · have ebound := lintegral_enorm_le_liminf_of_tendsto
      ((MeasureTheory.ae_restrict_iff' (by measurability) |>.mpr hGf))
      (fun n ↦ (hG n).aemeasurable.enorm)
    grw [hG'] at ebound
    rw [uIcc_of_le hab,
        ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm integrable_f_deriv,
        ENNReal.ofReal_le_ofReal_iff (by linarith),
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab] at ebound
    convert! ebound using 1
    refine intervalIntegral.integral_congr_uIoo ?_
    rw [uIoo_of_le hab]
    intro x hx
    exact Eq.symm <| abs_eq_self.mpr <| f_deriv_nonneg hx

/-- If `f` has bounded variation on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
/-
**BoundedVariationOn.intervalIntegrable_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BoundedVariationOn.intervalIntegrable_deriv {f : Real -> Real} {a b : Real
} (hf : BoundedVariationOn f (uIcc a b)) : IntervalIntegrable (deriv f) volume a
 b
参数：hf : BoundedVariationOn f (uIcc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`：LocallyBound
edVariationOn.exists_monotoneOn_sub_monotoneOn {f : α -> Real} {s : Set α} (h : 
LocallyBoundedVariationOn f s) : exists p q : α …
· 使用定理 `BoundedVariationOn.locallyBoundedVariationOn`：∀ {α : Type u_1} [inst : L
inearOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Se
t α},   BoundedVariationOn f s → L…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IntervalIntegrable.congr_ae`：IntervalIntegrable.congr_ae {g : Real -> ε}
 (hf : IntervalIntegrable f μ a b) (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIn
tegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.sub`：sub {f g : Real -> E} (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x - g
 x) μ a b
· 使用定理 `MonotoneOn.intervalIntegrable_deriv`：MonotoneOn.intervalIntegrable_deriv
 {f : Real -> Real} {a b : Real} (hf : MonotoneOn f (uIcc a b)) : IntervalIntegr
able (deriv f) volume a b
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MonotoneOn.ae_differentiableWithinAt_of_mem`：MonotoneOn.ae_differentiabl
eWithinAt_of_mem {f : Real -> Real} {s : Set Real} (hf : MonotoneOn f s) : foral
lᵐ x, x in s -> DifferentiableWit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Set.uIoc.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), Set.uI
oc a b = Set.Ioc (min a b) (max a b)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` has bounded variation on `uIcc a b`, then `f'` is interval integrable on 
`a..b`.
-/
theorem BoundedVariationOn.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  apply (hp.intervalIntegrable_deriv.sub hq.intervalIntegrable_deriv).congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by simp [uIoc])]
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  have hx₅ : x ∈ uIcc a b := Ioc_subset_Icc_self hx₄
  rw [uIoc, mem_Ioc] at hx₄
  have hx₆ : uIcc a b ∈ 𝓝 x := Icc_mem_nhds hx₄.left (lt_of_le_of_ne hx₄.right hx₃)
  replace hx₁ := (hx₁ hx₅).differentiableAt hx₆ |>.hasDerivAt
  replace hx₂ := (hx₂ hx₅).differentiableAt hx₆ |>.hasDerivAt
  exact (hx₁.sub hx₂).deriv.symm

/-- If `f` is absolutely continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
/-
**AbsolutelyContinuousOnInterval.intervalIntegrable_deriv** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：AbsolutelyContinuousOnInterval.intervalIntegrable_deriv {f : Real -> Real}
 {a b : Real} (hf : AbsolutelyContinuousOnInterval f a b) : IntervalIntegrable (
deriv f) volume a b
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedVariationOn.intervalIntegrable_deriv`：BoundedVariationOn.interval
Integrable_deriv {f : Real -> Real} {a b : Real} (hf : BoundedVariationOn f (uIc
c a b)) : IntervalIntegrable (der…
· 使用定理 `AbsolutelyContinuousOnInterval.boundedVariationOn`：boundedVariationOn (h
f : AbsolutelyContinuousOnInterval f a b) : BoundedVariationOn f (uIcc a b)

--- 原说明 ---
If `f` is absolutely continuous on `uIcc a b`, then `f'` is interval integrable 
on `a..b`.
-/
theorem AbsolutelyContinuousOnInterval.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.intervalIntegrable_deriv
