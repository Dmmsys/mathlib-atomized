/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement, establishing invariance
of the characteristic function `characteristic f ⊤` under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f⁻¹` agree up to a constant, see Proposition 2.1 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f - const` agree up to a constant, see Proposition 2.2 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677]

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

public section
namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicAt MeromorphicOn Metric Real

section FirstPart

variable {f : Complex -> Complex} {R : Real}

/-!
## First Part of the First Main Theorem
-/

/--
lemma `characteristic_sub_characteristic_inv` / 引理 `characteristic_sub_characteristic_inv`

English:
lemma characteristic_sub_characteristic_inv
  given: (h : Meromorphic f)
  proof: by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAver

中文:
引理 characteristic_sub_characteristic_inv
  条件: (h : Meromorphic f)
  证明: by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAver

Depends on / 依赖: Set.univ, ValueDistribution, ValueDistribution.log_counting_zero, characteristic, circleAverage, divisor, logCounting, logCounting_inv, log_counting_zero, proximity, proximity_sub_proximity_inv_eq_circleAverage
-/
lemma characteristic_sub_characteristic_inv (h : Meromorphic f) :
    characteristic f ⊤ - characteristic f⁻¹ ⊤ =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
  calc characteristic f ⊤ - characteristic f⁻¹ ⊤
  _ = proximity f ⊤ - proximity f⁻¹ ⊤ - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ - logCounting f ⊤) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 - logCounting f ⊤) := by
    rw [logCounting_inv]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ).logCounting := by
    rw [← ValueDistribution.log_counting_zero_sub_logCounting_top]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `characteristic_sub_characteristic_inv_of_ne_zero` / 引理 `characteristic_sub_characteristic_inv_of_ne_zero`

English:
lemma characteristic_sub_characteristic_inv_of_ne_zero
  proof: by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf]; rw [Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoe

中文:
引理 characteristic_sub_characteristic_inv_of_ne_zero
  证明: by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf]; rw [Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoe

Depends on / 依赖: Function, Function.locallyFinsuppWithin.logCounting, MeromorphicOn, MeromorphicOn.circleAverage_log_norm, Pi.sub_apply, Set.univ, characteristic, characteristic_sub_characteristic_inv, circleAverage, circleAverage_log_norm, closedBall, divisor, hf.meromorphicOn, locallyFinsuppWithin, logCounting, meromorphicOn, meromorphicTrailingCoeffAt, sub_apply, toClosedBall
-/
lemma characteristic_sub_characteristic_inv_of_ne_zero
    (hf : Meromorphic f) (hR : R != 0) :
    characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  calc characteristic f ⊤ R - characteristic f⁻¹ ⊤ R
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) R := by simp
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ).logCounting R := by
    rw [characteristic_sub_characteristic_inv hf]; rw [Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoeffAt f 0‖ := by
    rw [MeromorphicOn.circleAverage_log_norm hR hf.meromorphicOn]
    unfold Function.locallyFinsuppWithin.logCounting
    have : (divisor f (closedBall 0 |R|)) = (divisor f Set.univ).toClosedBall R :=
      (divisor_restrict hf.meromorphicOn (by tauto)).symm
    simp [this, toClosedBall, restrictMonoidHom, restrict_apply]

/--
lemma `characteristic_sub_characteristic_inv_at_zero` / 引理 `characteristic_sub_characteristic_inv_at_zero`

English:
lemma characteristic_sub_characteristic_inv_at_zero
  given: (h : Meromorphic f)
  proof: by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h]; rw [Pi.sub_apply]
  _ = log ‖f 0‖ 

中文:
引理 characteristic_sub_characteristic_inv_at_zero
  条件: (h : Meromorphic f)
  证明: by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h]; rw [Pi.sub_apply]
  _ = log ‖f 0‖ 

Depends on / 依赖: Pi.sub_apply, Set.univ, ValueDistribution, ValueDistribution.characteristic_sub_characteristic_inv, characteristic, characteristic_sub_characteristic_inv, circleAverage, divisor, logCounting, sub_apply
-/
lemma characteristic_sub_characteristic_inv_at_zero (h : Meromorphic f) :
    characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0 = log ‖f 0‖ := by
  calc characteristic f ⊤ 0 - characteristic f⁻¹ ⊤ 0
  _ = (characteristic f ⊤ - characteristic f⁻¹ ⊤) 0 := by simp
  _ = circleAverage (log ‖f ·‖) 0 0 - (divisor f Set.univ).logCounting 0 := by
    rw [ValueDistribution.characteristic_sub_characteristic_inv h]; rw [Pi.sub_apply]
  _ = log ‖f 0‖ := by
    simp

/--
theorem `characteristic_sub_characteristic_inv_le` / 定理 `characteristic_sub_characteristic_inv_le`

English:
theorem characteristic_sub_characteristic_inv_le
  given: (hf : Meromorphic f)
  proof: by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

中文:
定理 characteristic_sub_characteristic_inv_le
  条件: (hf : Meromorphic f)
  证明: by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

Depends on / 依赖: characteristic_sub_characteristic_inv_at_zero, characteristic_sub_characteristic_inv_of_ne_zero
-/
theorem characteristic_sub_characteristic_inv_le (hf : Meromorphic f) :
    |characteristic f ⊤ R - characteristic f⁻¹ ⊤ R|
      <= max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h]

/--
theorem `isBigO_characteristic_sub_characteristic_inv` / 定理 `isBigO_characteristic_sub_characteristic_inv`

English:
theorem isBigO_characteristic_sub_characteristic_inv
  given: (h : Meromorphic f)
  proof: isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R => by simpa using characteristic_sub_characteristic_inv_le h (R := R))

中文:
定理 isBigO_characteristic_sub_characteristic_inv
  条件: (h : Meromorphic f)
  证明: isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R => by simpa using characteristic_sub_characteristic_inv_le h (R := R))

Depends on / 依赖: characteristic_sub_characteristic_inv_le, isBigO_of_le, meromorphicTrailingCoeffAt
-/
theorem isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : Real -> Real) :=
  isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0‖|) _
    (fun R => by simpa using characteristic_sub_characteristic_inv_le h (R := R))

end FirstPart

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {a₀ : E} {f : Complex -> E}

/-!
## Second Part of the First Main Theorem
-/

/--
theorem `abs_characteristic_sub_characteristic_shift_le` / 定理 `abs_characteristic_sub_characteristic_shift_le`

English:
theorem abs_characteristic_sub_characteristic_shift_le
  given: {r : Real} (h : Meromorphic f)
  proof: by
  have h₁f : CircleIntegrable (fun x => log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x => log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    apply h.meromorphicOn.sub (MeromorphicOn.const a₀)
  rw [← Pi.sub

中文:
定理 abs_characteristic_sub_characteristic_shift_le
  条件: {r : 实数} (h : Meromorphic f)
  证明: by
  have h₁f : CircleIntegrable (fun x => log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x => log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    apply h.meromorphicOn.sub (MeromorphicOn.const a₀)
  rw [← Pi.sub

Depends on / 依赖: CircleIntegrable, MeromorphicOn, MeromorphicOn.circleIntegrable_posLog_norm, MeromorphicOn.const, Pi.sub_apply, abs_circleAverage_le_circleAverage_abs, characteristic_sub_characteristic_eq_proximity_sub_proximity, circleAverage_sub, circleIntegrable_posLog_norm, h.meromorphicOn.circleIntegrable_posLog_norm, h.meromorphicOn.sub, le_trans, meromorphicOn, proximity, reduceDIte, sub_apply
-/
theorem abs_characteristic_sub_characteristic_shift_le {r : Real} (h : Meromorphic f) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| <= log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x => log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x => log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    apply h.meromorphicOn.sub (MeromorphicOn.const a₀)
  rw [← Pi.sub_apply]; rw [characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity, reduceDIte, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  · apply (h₁f.sub h₂f).abs
  · intro θ hθ
    simp only [Pi.abs_apply, Pi.sub_apply]
    by_cases h : 0 <= log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
    · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
        using (posLog_norm_add_le (f θ - a₀) a₀)
    · simp only [abs_of_nonpos (le_of_not_ge h), neg_sub, tsub_le_iff_right,
        add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert! posLog_norm_add_le (-f θ) a₀ using 2
      · rw [← norm_neg]
        abel_nf
      · simp

/--
theorem `isBigO_characteristic_sub_characteristic_shift` / 定理 `isBigO_characteristic_sub_characteristic_shift`

English:
theorem isBigO_characteristic_sub_characteristic_shift
  given: (h : Meromorphic f)
  proof: isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R => by simpa using abs_characteristic_sub_characteristic_shift_le h)

中文:
定理 isBigO_characteristic_sub_characteristic_shift
  条件: (h : Meromorphic f)
  证明: isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R => by simpa using abs_characteristic_sub_characteristic_shift_le h)

Depends on / 依赖: abs_characteristic_sub_characteristic_shift_le, isBigO_of_le
-/
theorem isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : Real -> Real) :=
  isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R => by simpa using abs_characteristic_sub_characteristic_shift_le h)

end SecondPart

end ValueDistribution
