/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Tactic.MoveAdd

/-!
# The integral of the real power of a nonnegative function

In this file, we give a common application of the layer cake formula ---
a representation of the integral of the p:th power of a nonnegative function `f`:
`∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt`.

A variant of the formula with measures of sets of the form `{ω | f(ω) > t}` instead of
`{ω | f(ω) ≥ t}` is also included.

Moreover, we prove that `‖x‖ ^ (-d + ε)` is locally integrable.

## Main results

* `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` and
  `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`:
  other common special cases of the layer cake formulas, stating that for a nonnegative function `f`
  and `p > 0`, we have `∫ f(ω)ᵖ ∂μ(ω) = p * ∫ μ {ω | f(ω) ≥ t} * tᵖ⁻¹ dt` and
  `∫ f(ω)ᵖ ∂μ(ω) = p * ∫ μ {ω | f(ω) > t} * tᵖ⁻¹ dt`, respectively.
* `MeasureTheory.locallyIntegrable_of_norm_le_rpow`:
  a function that is dominated by `‖x‖ ^ (-d + ε)` is locally integrable.

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/

public section

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

section Layercake

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` for a version with sets of the form
`{ω | f(ω) > t}` instead. -/
/-
**MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_rpow_eq_lintegral_meas_le_mul {f : α -> Real} (f_nn : 0 <=ᵐ[μ] f
) (f_mble : AEMeasurable f μ) {p : Real} (p_pos : 0 < p) : ∫⁻ ω, ENNReal.ofReal 
(f ω ^ p) ∂μ = ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t <= f a} * ENNReal.
ofReal (t ^ (p - 1))
参数：f_nn : 0 <=ᵐ[μ] f；f_mble : AEMeasurable f μ；p_pos : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
An application of the layer cake formula / Cavalieri's principle / tail probabil
ity formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` 
can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω 
| f(ω) ≥ t}`.

See `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` for a version with s
ets of the form
`{ω | f(ω) > t}` instead.
-/
theorem lintegral_rpow_eq_lintegral_meas_le_mul
    {f : α → ℝ} (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : ∀ x : ℝ, ∫ t : ℝ in 0..x, t ^ (p - 1) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : ℝ => t ^ (p - 1)
  have g_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    intro t t_pos
    exact Real.rpow_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble (t) (ht : 0 < t) : IntervalIntegrable g volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key, ← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le, mul_div_cancel₀ (f ω ^ p) p_pos.ne.symm]
  · have aux := (measurable_const (a := p)).aemeasurable (μ := μ)
    exact measurable_id.ennreal_ofReal.comp_aemeasurable <| (f_mble.pow aux).div_const p

end Layercake

section LayercakeLT

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω | f(ω) > t}`.

See `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` for a version with sets of the form
`{ω | f(ω) ≥ t}` instead. -/
/-
**MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_rpow_eq_lintegral_meas_lt_mul {f : α -> Real} (f_nn : 0 <=ᵐ[μ] f
) (f_mble : AEMeasurable f μ) {p : Real} (p_pos : 0 < p) : ∫⁻ ω, ENNReal.ofReal 
(f ω ^ p) ∂μ = ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.o
fReal (t ^ (p - 1))
参数：f_nn : 0 <=ᵐ[μ] f；f_mble : AEMeasurable f μ；p_pos : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`：lintegral_rpow_eq
_lintegral_meas_le_mul {f : α -> Real} (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurabl
e f μ) {p : Real} (p_pos : 0 < p) : ∫⁻ ω, E…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.meas_le_ae_eq_meas_lt`：meas_le_ae_eq_meas_lt {R : Type*} [
LinearOrder R] [MeasurableSpace R] (ν : Measure R) [NullSingletonClass ν] (g : α
 -> R) : (fun t => μ {a :…
· 使用定理 `MeasureTheory.Measure.restrict.instNullSingletonClass`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.NullSingle
tonClass μ]   (s : Set α), MeasureTheory.Nu…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
An application of the layer cake formula / Cavalieri's principle / tail probabil
ity formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` 
can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω 
| f(ω) > t}`.

See `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` for a version with s
ets of the form
`{ω | f(ω) ≥ t}` instead.
-/
theorem lintegral_rpow_eq_lintegral_meas_lt_mul
    {f : α → ℝ} (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  rw [ht]

end LayercakeLT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open Set Metric in
/-
**MeasureTheory.integrableOn_ball_of_norm_le_rpow** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrableOn_ball_of_norm_le_rpow (hd : 1 <= Module.finrank Real E) {f : E
 -> F} {C α r : Real} (hα : α < Module.finrank Real E) (h_decay : forallᵐ x ∂μ.r
estrict (ball 0 r), ‖f x‖ <= C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f μ)
 : IntegrableOn f (ball 0 r) μ
参数：hd : 1 <= Module.finrank Real E；hα : α < Module.finrank Real E；h_decay : fora
llᵐ x ∂μ.restrict (ball 0 r), ‖f x‖ <= C * ‖x‖ ^ (-α)；h_meas : AEStronglyMeasura
ble f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Module.nontrivial_of_finrank_pos`：Module.nontrivial_of_finrank_pos (h : 
0 < finrank R M) : Nontrivial M
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `intervalIntegral.integrableOn_Ioo_rpow_iff`：integrableOn_Ioo_rpow_iff {s
 t : Real} (ht : 0 < t) : IntegrableOn (fun x => x ^ s) (Ioo (0 : Real) t) ↔ -1 
< s
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 62 条，此处仅展示前 30 条）
-/
lemma integrableOn_ball_of_norm_le_rpow (hd : 1 ≤ Module.finrank ℝ E) {f : E → F} {C α r : ℝ}
    (hα : α < Module.finrank ℝ E) (h_decay : ∀ᵐ x ∂μ.restrict (ball 0 r), ‖f x‖ ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f μ) :
    IntegrableOn f (ball 0 r) μ := by
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    positivity
  have hint : IntegrableOn (fun y ↦ y ^ (Module.finrank ℝ E - 1) • (C * y ^ (-α))) (Ioo 0 r) := by
    simp only [smul_eq_mul]
    have h_rpow : IntegrableOn (fun y ↦ y ^ ((Module.finrank ℝ E : ℝ) - 1 - α)) (Ioo 0 r) := by
      by_cases! hr : 0 < r
      · rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
        linarith
      · simp [hr]
    apply IntegrableOn.congr_fun (h_rpow.const_mul C) ?_ measurableSet_Ioo
    intro y ⟨hy, _⟩
    simp only
    move_mul [C]
    rw [← Real.rpow_natCast y (Module.finrank ℝ E - 1), ← Real.rpow_add hy]
    congr
    norm_cast
  rw [← integrableOn_fun_norm_addHaar μ] at hint
  exact Integrable.mono' hint h_meas.restrict h_decay

/-- A function that is dominated by `‖x‖ ^ (-d + ε)` is locally integrable -/
/-
**MeasureTheory.locallyIntegrable_of_norm_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：locallyIntegrable_of_norm_le_rpow (hdim : 1 <= Module.finrank Real E) {f :
 E -> F} {C α : Real} (hα : α < Module.finrank Real E) (h_decay : forallᵐ x ∂μ, 
‖f x‖ <= C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f μ) : LocallyIntegrable
 f μ
参数：hdim : 1 <= Module.finrank Real E；hα : α < Module.finrank Real E；h_decay : fo
rallᵐ x ∂μ, ‖f x‖ <= C * ‖x‖ ^ (-α)；h_meas : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.locallyIntegrable_iff`：locallyIntegrable_iff [PseudoMetriz
ableSpace ε] [LocallyCompactSpace X] : LocallyIntegrable f μ ↔ forall k : Set X,
 IsCompact k -> Integrabl…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Bornology.IsBounded.exists_pos_norm_lt`：∀ {E : Type u_2} [inst : Seminor
medAddGroup E] {s : Set E}, Bornology.IsBounded s → ∃ R > 0, ∀ x ∈ s, ‖x‖ < R
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用引理 `MeasureTheory.integrableOn_ball_of_norm_le_rpow`：integrableOn_ball_of_no
rm_le_rpow (hd : 1 <= Module.finrank Real E) {f : E -> F} {C α r : Real} (hα : α
 < Module.finrank Real E) (h_decay : …
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r

--- 原说明 ---
A function that is dominated by `‖x‖ ^ (-d + ε)` is locally integrable
-/
theorem locallyIntegrable_of_norm_le_rpow (hdim : 1 ≤ Module.finrank ℝ E) {f : E → F} {C α : ℝ}
    (hα : α < Module.finrank ℝ E)
    (h_decay : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrable f μ := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_ball_of_norm_le_rpow hdim hα (ae_restrict_of_ae h_decay) h_meas).mono_set
    (mem_ball_zero_iff.mpr <| hR · ·)

end MeasureTheory

