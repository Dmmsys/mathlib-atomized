/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Integrability of Special Functions

This file establishes basic facts about the interval integrability of special functions, including
powers and the logarithm.
-/

public section

open Interval MeasureTheory Real Set

variable {a b c d : ℝ} (n : ℕ) {f : ℝ → ℝ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

namespace intervalIntegral

@[simp]
/-
**intervalIntegral.intervalIntegrable_pow** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：intervalIntegrable_pow : IntervalIntegrable (fun x => x ^ n) μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem intervalIntegrable_pow : IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuous_pow n).intervalIntegrable a b
/-
**intervalIntegral.intervalIntegrable_zpow** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：intervalIntegrable_zpow {n : Int} (h : 0 <= n ∨ (0 : Real) ∉ [[a, b]]) : I
ntervalIntegrable (fun x => x ^ n) μ a b
参数：h : 0 <= n ∨ (0 : Real) ∉ [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.zpow₀`：ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : Int)
 (h : forall a in s, f a != 0 ∨ 0 <= m) : ContinuousOn (fun x => f x ^ m) s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
theorem intervalIntegrable_zpow {n : ℤ} (h : 0 ≤ n ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuousOn_id.zpow₀ n fun _ hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

/-- See `intervalIntegrable_rpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
/-
**intervalIntegral.intervalIntegrable_rpow** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：intervalIntegrable_rpow {r : Real} (h : 0 <= r ∨ (0 : Real) ∉ [[a, b]]) : 
IntervalIntegrable (fun x => x ^ r) μ a b
参数：h : 0 <= r ∨ (0 : Real) ∉ [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.rpow_const`：ContinuousOn.rpow_const (hf : ContinuousOn f s)
 (h : forall x in s, f x != 0 ∨ 0 <= p) : ContinuousOn (fun x => f x ^ p) s
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a

--- 原说明 ---
See `intervalIntegrable_rpow'` for a version with a weaker hypothesis on `r`, bu
t assuming the
measure is volume.
-/
theorem intervalIntegrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ r) μ a b :=
  (continuousOn_id.rpow_const fun _ hx =>
    h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

/-- See `intervalIntegrable_rpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
/-
**intervalIntegral.intervalIntegrable_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：intervalIntegrable_rpow' {r : Real} (h : -1 < r) : IntervalIntegrable (fun
 x => x ^ r) volume a b
参数：h : -1 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
See `intervalIntegrable_rpow` for a version applying to any locally finite measu
re, but with a
stronger hypothesis on `r`.
-/
theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
    IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff, uIoc_of_le hc]
    have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx
      convert! (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.1.ne')).div_const (r + 1) using 1
      simp [(by linarith : r + 1 ≠ 0)]
    apply integrableOn_deriv_of_nonneg _ hderiv
    · intro x hx; apply rpow_nonneg hx.1.le
    · refine (continuousOn_id.rpow_const ?_).div_const _; intro x _; right; linarith
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).smul (cos (r * π))
    rw [intervalIntegrable_iff] at m ⊢
    refine m.congr_fun ?_ measurableSet_Ioc; intro x hx
    rw [uIoc_of_le (by linarith : 0 ≤ -c)] at hx
    simp only [Pi.smul_apply, smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)]

/-- The power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s`. -/
/-
**intervalIntegral.integrableOn_Ioo_rpow_iff** 是 Mathlib 中的一个引理，位于命名空间 `interval
Integral`。
形式化陈述：integrableOn_Ioo_rpow_iff {s t : Real} (ht : 0 < t) : IntegrableOn (fun x 
=> x ^ s) (Ioo (0 : Real) t) ↔ -1 < s
参数：ht : 0 < t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s`.
-/
lemma integrableOn_Ioo_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) t) ↔ -1 < s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    apply intervalIntegrable_rpow' h (a := 0) (b := t)
  contrapose! h
  intro H
  have I : 0 < min 1 t := lt_min zero_lt_one ht
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioo 0 (min 1 t)) :=
    H.mono (Set.Ioo_subset_Ioo le_rfl (min_le_right _ _)) le_rfl
  have : IntegrableOn (fun x ↦ x⁻¹) (Ioo 0 (min 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hx.1)]
    rwa [← Real.rpow_neg_one x, Real.rpow_le_rpow_left_iff_of_base_lt_one hx.1]
    exact lt_of_lt_of_le hx.2 (min_le_left _ _)
  have : IntervalIntegrable (fun x ↦ x⁻¹) volume 0 (min 1 t) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le I.le]
  simp [intervalIntegrable_inv_iff, I.ne] at this

/-- See `intervalIntegrable_cpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
/-
**intervalIntegral.intervalIntegrable_cpow** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：intervalIntegrable_cpow {r : Complex} (h : 0 <= r.re ∨ (0 : Real) ∉ [[a, b
]]) : IntervalIntegrable (fun x : Real => (x : Complex) ^ r) μ a b
参数：h : 0 <= r.re ∨ (0 : Real) ∉ [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Complex.continuousAt_ofReal_cpow_const`：continuousAt_ofReal_cpow_const (
x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) : ContinuousAt (fun a => (a : Co
mplex) ^ y : Real -> Complex…
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `Complex.continuous_ofReal_cpow_const`：continuous_ofReal_cpow_const {y : 
Complex} (hs : 0 < y.re) : Continuous (fun x => (x : Complex) ^ y : Real -> Comp
lex)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntervalIntegrable.intervalIntegrable_norm_iff`：intervalIntegrable_norm_
iff {f : Real -> E} {μ : Measure Real} {a b : Real} (hf : AEStronglyMeasurable f
 (μ.restrict (Ι a b))) : IntervalInt…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_of_continuousOn_compl_singleton`：measurable_of_continuousOn_c
ompl_singleton [T1Space α] {f : α -> γ} (a : α) (hf : ContinuousOn f {a}ᶜ) : Mea
surable f
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `intervalIntegrable_const`：intervalIntegrable_const [IsLocallyFiniteMeasu
re μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun`：∀ {α : Type u_1} {ε : Type u_3} {m
α : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}  
 [inst : TopologicalSpace …
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
See `intervalIntegrable_cpow'` for a version with a weaker hypothesis on `r`, bu
t assuming the
measure is volume.
-/
theorem intervalIntegrable_cpow {r : ℂ} (h : 0 ≤ r.re ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) μ a b := by
  by_cases h2 : (0 : ℝ) ∉ [[a, b]]
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
    exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
  rw [eq_false h2, or_false] at h
  rcases lt_or_eq_of_le h with (h' | h')
  · -- Easy case #2: 0 < re r -- again use continuity
    exact (Complex.continuous_ofReal_cpow_const h').intervalIntegrable _ _
  -- Now the hard case: re r = 0 and 0 is in the interval.
  refine (IntervalIntegrable.intervalIntegrable_norm_iff ?_).mp ?_
  · refine (measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_).aestronglyMeasurable
    exact continuousOn_of_forall_continuousAt fun x hx =>
      Complex.continuousAt_ofReal_cpow_const x r (Or.inr hx)
  -- reduce to case of integral over `[0, c]`
  suffices ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => ‖(x : ℂ) ^ r‖) μ 0 c from
    (this a).symm.trans (this b)
  intro c
  rcases le_or_gt 0 c with (hc | hc)
  · -- case `0 ≤ c`: integrand is identically 1
    have : IntervalIntegrable (fun _ => 1 : ℝ → ℝ) μ 0 c := intervalIntegrable_const
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc] at this ⊢
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioc
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, ← h', rpow_zero]
  · -- case `c < 0`: integrand is identically constant, *except* at `x = 0` if `r ≠ 0`.
    apply IntervalIntegrable.symm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le]
    rw [← Ioo_union_right hc, integrableOn_union, and_comm]; constructor
    · exact integrableOn_singleton (by simp) <|
        isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_singleton
    · have : ∀ x : ℝ, x ∈ Ioo c 0 → ‖Complex.exp (↑π * Complex.I * r)‖ = ‖(x : ℂ) ^ r‖ := by
        intro x hx
        rw [Complex.ofReal_cpow_of_nonpos hx.2.le, norm_mul, ← Complex.ofReal_neg,
          Complex.norm_cpow_eq_rpow_re_of_pos (neg_pos.mpr hx.2), ← h',
          rpow_zero, one_mul]
      refine IntegrableOn.congr_fun ?_ this measurableSet_Ioo
      rw [integrableOn_const_iff]
      right
      refine (measure_mono Set.Ioo_subset_Icc_self).trans_lt ?_
      exact isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_Icc

/-- See `intervalIntegrable_cpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
/-
**intervalIntegral.intervalIntegrable_cpow'** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：intervalIntegrable_cpow' {r : Complex} (h : -1 < r.re) : IntervalIntegrabl
e (fun x : Real => (x : Complex) ^ r) volume a b
参数：h : -1 < r.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntervalIntegrable.intervalIntegrable_norm_iff`：intervalIntegrable_norm_
iff {f : Real -> E} {μ : Measure Real} {a b : Real} (hf : AEStronglyMeasurable f
 (μ.restrict (Ι a b))) : IntervalInt…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_cpow_const`：continuousAt_cpow_const {a b : Complex} (ha : a
 in slitPlane) : ContinuousAt (· ^ b) a
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun`：∀ {α : Type u_1} {ε : Type u_3} {m
α : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}  
 [inst : TopologicalSpace …
· 使用定理 `intervalIntegral.intervalIntegrable_rpow'`：intervalIntegrable_rpow' {r :
 Real} (h : -1 < r) : IntervalIntegrable (fun x => x ^ r) volume a b
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `IntervalIntegrable.iff_comp_neg`：iff_comp_neg {f : Real -> E} (h : ‖f (m
in a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
See `intervalIntegrable_cpow` for a version applying to any locally finite measu
re, but with a
stronger hypothesis on `r`.
-/
theorem intervalIntegrable_cpow' {r : ℂ} (h : -1 < r.re) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.intervalIntegrable_norm_iff]
    · rw [intervalIntegrable_iff]
      apply IntegrableOn.congr_fun
      · rw [← intervalIntegrable_iff]; exact intervalIntegral.intervalIntegrable_rpow' h
      · intro x hx
        rw [uIoc_of_le hc] at hx
        dsimp only
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      · exact measurableSet_uIoc
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      rw [uIoc_of_le hc] at hx
      refine (continuousAt_cpow_const (Or.inl ?_)).comp Complex.continuous_ofReal.continuousAt
      rw [Complex.ofReal_re]
      exact hx.1
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).const_mul (Complex.exp (π * Complex.I * r))
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : 0 ≤ -c)] at m ⊢
    refine m.congr_fun (fun x hx => ?_) measurableSet_Ioc
    #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
    instantiation order leads to a term with a beta redex.
    https://github.com/leanprover/lean4/pull/13762
    This will be removed once app elaboration itself does beta reduction. -/
    dsimp only
    have : -x ≤ 0 := by linarith [hx.1]
    rw [Complex.ofReal_cpow_of_nonpos this, mul_comm]
    simp

/-- The complex power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s.re`. -/
/-
**intervalIntegral.integrableOn_Ioo_cpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integrableOn_Ioo_cpow_iff {s : Complex} {t : Real} (ht : 0 < t) : Integrab
leOn (fun x : Real => (x : Complex) ^ s) (Ioo (0 : Real) t) ↔ -1 < s.re
参数：ht : 0 < t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用引理 `intervalIntegral.integrableOn_Ioo_rpow_iff`：integrableOn_Ioo_rpow_iff {s
 t : Real} (ht : 0 < t) : IntegrableOn (fun x => x ^ s) (Ioo (0 : Real) t) ↔ -1 
< s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioo_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioo_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `intervalIntegral.intervalIntegrable_cpow'`：intervalIntegrable_cpow' {r :
 Complex} (h : -1 < r.re) : IntervalIntegrable (fun x : Real => (x : Complex) ^ 
r) volume a b

--- 原说明 ---
The complex power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s.re`.
-/
theorem integrableOn_Ioo_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioo (0 : ℝ) t) ↔ -1 < s.re := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact intervalIntegrable_cpow' h (a := 0) (b := t)
  have B : IntegrableOn (fun a ↦ a ^ s.re) (Ioo 0 t) := by
    apply (integrableOn_congr_fun _ measurableSet_Ioo).1 h.norm
    intro a ha
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ha.1]
  rwa [integrableOn_Ioo_rpow_iff ht] at B

@[simp]
/-
**intervalIntegral.intervalIntegrable_id** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：intervalIntegrable_id : IntervalIntegrable (fun x => x) μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem intervalIntegrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.intervalIntegrable a b
/-
**intervalIntegral.intervalIntegrable_one_div** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：intervalIntegrable_one_div (h : forall x : Real, x in [[a, b]] -> f x != 0
) (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 1 / f x) μ a b
参数：h : forall x : Real, x in [[a, b]] -> f x != 0；hf : ContinuousOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.div`：ContinuousOn.div (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (h₀ : forall x in s, g x != 0) : ContinuousOn (f / g) s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem intervalIntegrable_one_div (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 1 / f x) μ a b :=
  (continuousOn_const.div hf h).intervalIntegrable

@[simp]
/-
**intervalIntegral.intervalIntegrable_inv** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：intervalIntegrable_inv (h : forall x : Real, x in [[a, b]] -> f x != 0) (h
f : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => (f x)⁻¹) μ a b
参数：h : forall x : Real, x in [[a, b]] -> f x != 0；hf : ContinuousOn f [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `intervalIntegral.intervalIntegrable_one_div`：intervalIntegrable_one_div 
(h : forall x : Real, x in [[a, b]] -> f x != 0) (hf : ContinuousOn f [[a, b]]) 
: IntervalIntegrable (fun x => 1 …
-/
theorem intervalIntegrable_inv (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => (f x)⁻¹) μ a b := by
  simpa only [one_div] using intervalIntegrable_one_div h hf

@[simp]
/-
**intervalIntegral.intervalIntegrable_sin** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：intervalIntegrable_sin : IntervalIntegrable sin μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `Real.continuous_sin`：continuous_sin : Continuous sin
-/
theorem intervalIntegrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.intervalIntegrable a b

@[simp]
/-
**intervalIntegral.intervalIntegrable_cos** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：intervalIntegrable_cos : IntervalIntegrable cos μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `Real.continuous_cos`：continuous_cos : Continuous cos
-/
theorem intervalIntegrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.intervalIntegrable a b

@[simp]
/-
**intervalIntegral.intervalIntegrable_exp** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：intervalIntegrable_exp : IntervalIntegrable exp μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
-/
theorem intervalIntegrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.intervalIntegrable a b

@[simp]
/-
**intervalIntegral._root_.IntervalIntegrable.log** 是 Mathlib 中的一个定理，位于命名空间 `inte
rvalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IntervalIntegrable.log (hf : ContinuousOn f [[a, b]])
    (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).intervalIntegrable

/--
The real logarithm is interval integrable (with respect to every locally finite measure) over every
interval that does not contain zero. See `intervalIntegrable_log'` for a version without any
hypothesis on the interval, but assuming the measure is the volume.
-/
@[simp]
/-
**intervalIntegral.intervalIntegrable_log** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：intervalIntegrable_log (h : (0 : Real) ∉ [[a, b]]) : IntervalIntegrable lo
g μ a b
参数：h : (0 : Real) ∉ [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.log`：∀ {a b : ℝ} {f : ℝ → ℝ} {μ : MeasureTheory.Measu
re ℝ} [MeasureTheory.IsLocallyFiniteMeasure μ],   ContinuousOn f (Set.uIcc a b) 
→ (∀ x ∈ Set…
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b

--- 原说明 ---
The real logarithm is interval integrable (with respect to every locally finite 
measure) over every
interval that does not contain zero. See `intervalIntegrable_log'` for a version
 without any
hypothesis on the interval, but assuming the measure is the volume.
-/
theorem intervalIntegrable_log (h : (0 : ℝ) ∉ [[a, b]]) : IntervalIntegrable log μ a b :=
  IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h

/--
The real logarithm is interval integrable (with respect to the volume measure) on every interval.
See `intervalIntegrable_log` for a version applying to any locally finite measure, but with an
additional hypothesis on the interval.
-/
@[simp]
/-
**intervalIntegral.intervalIntegrable_log'** 是 Mathlib 中的一个定理，位于命名空间 `intervalIn
tegral`。
形式化陈述：intervalIntegrable_log' : IntervalIntegrable log volume a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegrable_of_even`：intervalIntegrable_of_even (h₁f : forall x, 
f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {a b : 
Real} (ha : ‖f (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `IntervalIntegrable.neg`：neg {f : Real -> E} (h : IntervalIntegrable f μ 
a b) : IntervalIntegrable (-f) μ a b
· 使用定理 `intervalIntegral.intervalIntegrable_deriv_of_nonneg`：intervalIntegrable_
deriv_of_nonneg (hcont : ContinuousOn g (uIcc a b)) (hderiv : forall x in Ioo (m
in a b) (max a b), HasDerivAt g (g' x) x)…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `Real.continuous_mul_log`：continuous_mul_log : Continuous fun x => x * lo
g x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `HasDerivAt.sub`：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f - g) (f' - g') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用引理 `Real.hasDerivAt_mul_log`：hasDerivAt_mul_log {x : Real} (hx : x != 0) : H
asDerivAt (fun x => x * log x) (log x + 1) x
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The real logarithm is interval integrable (with respect to the volume measure) o
n every interval.
See `intervalIntegrable_log` for a version applying to any locally finite measur
e, but with an
additional hypothesis on the interval.
-/
theorem intervalIntegrable_log' : IntervalIntegrable log volume a b := by
  -- Log is even, so it suffices to consider the case 0 < a and b = 0
  apply intervalIntegrable_of_even (log_neg_eq_log · |>.symm)
  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_neg log]
    apply IntervalIntegrable.neg
    apply intervalIntegrable_deriv_of_nonneg (g := fun x ↦ -(x * log x - x))
    · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
    · intro s ⟨hs, _⟩
      norm_num at *
      simpa using! (hasDerivAt_id s).sub (hasDerivAt_mul_log hs.ne.symm)
    · intro s ⟨hs₁, hs₂⟩
      grind [Pi.neg_apply, log_nonpos_iff]
  · -- Show integrability on [1…t] by continuity
    apply ContinuousOn.intervalIntegrable
    apply Real.continuousOn_log.mono
    apply Set.notMem_uIcc_of_lt zero_lt_one at hx
    simpa
/-
**intervalIntegral.intervalIntegrable_one_div_one_add_sq** 是 Mathlib 中的一个定理，位于命名
空间 `intervalIntegral`。
形式化陈述：intervalIntegrable_one_div_one_add_sq : IntervalIntegrable (fun x : Real =
> 1 / (↑1 + x ^ 2)) μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `Continuous.div₀`：Continuous.div₀ (hf : Continuous f) (hg : Continuous g)
 (h₀ : forall x, g x != 0) : Continuous (fun x => f x / g x)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
（共 68 条，此处仅展示前 30 条）
-/
theorem intervalIntegrable_one_div_one_add_sq :
    IntervalIntegrable (fun x : ℝ => 1 / (↑1 + x ^ 2)) μ a b := by
  apply Continuous.intervalIntegrable
  fun_prop (discharger := intro; nlinarith)

@[simp]
/-
**intervalIntegral.intervalIntegrable_inv_one_add_sq** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：intervalIntegrable_inv_one_add_sq : IntervalIntegrable (fun x : Real => (↑
1 + x ^ 2)⁻¹) μ a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem intervalIntegrable_inv_one_add_sq :
    IntervalIntegrable (fun x : ℝ => (↑1 + x ^ 2)⁻¹) μ a b := by
  simp [← one_div, intervalIntegrable_one_div_one_add_sq]

end intervalIntegral

