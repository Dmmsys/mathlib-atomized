/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Integral of `log ∘ sin`

This file computes special values of the integral of `log ∘ sin`. Given that the indefinite integral
involves the dilogarithm, this can be seen as computing special values of `Li₂`.
-/

public section

open Filter Interval Real

/-
Helper lemma for `integral_log_sin_zero_pi_div_two`: The integral of `log ∘ sin` on `0 … π` is
double the integral on `0 … π/2`.
-/
/-
**integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two** 是 Mathl
ib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for `integral_log_sin_zero_pi_div_two`: The integral of `log ∘ sin`
 on `0 … π` is
double the integral on `0 … π/2`.
-/
private lemma integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two :
    ∫ x in 0..π, log (sin x) = 2 * ∫ x in 0..(π / 2), log (sin x) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := π / 2) (c := π)
    (by apply intervalIntegrable_log_sin) (by apply intervalIntegrable_log_sin)]
  conv =>
    left; right; arg 1
    intro x
    rw [← sin_pi_sub]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)), sub_self,
    (by linarith : π - π / 2 = π / 2)]
  ring!

/--
The integral of `log ∘ sin` on `0 … π/2` equals `-log 2 * π / 2`.
-/
/-
**integral_log_sin_zero_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_log_sin_zero_pi_div_two : ∫ x in 0..(π / 2), log (sin x) = -log 2
 * π / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `intervalIntegral.integral_congr_codiscreteWithin`：integral_congr_codiscr
eteWithin {a b : Real} {f₁ f₂ : Real -> Real} (hf : f₁ =ᶠ[codiscreteWithin (Ι a 
b)] f₂) : ∫ (x : Real) in a..b, f₁ x =…
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用定理 `trivial`：True
· 使用定理 `AnalyticOnNhd.preimage_zero_mem_codiscrete`：preimage_zero_mem_codiscrete
 [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f Set.univ) (hx : f x != 0) : 
f ⁻¹' {0}ᶜ in codiscrete 𝕜
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `Real.analyticOnNhd_sin`：analyticOnNhd_sin {s : Set Real} : AnalyticOnNhd
 Real sin s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.analyticOnNhd_cos`：analyticOnNhd_cos {s : Set Real} : AnalyticOnNhd
 Real cos s
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.sin_two_mul`：∀ (x : ℝ), Real.sin (2 * x) = 2 * Real.sin x * Real.co
s x
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 101 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of `log ∘ sin` on `0 … π/2` equals `-log 2 * π / 2`.
-/
theorem integral_log_sin_zero_pi_div_two : ∫ x in 0..(π / 2), log (sin x) = -log 2 * π / 2 := by
  calc ∫ x in 0..(π / 2), log (sin x)
    _ = ∫ x in 0..(π / 2), (log (sin (2 * x)) - log 2 - log (cos x)) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      apply Filter.codiscreteWithin_mono (by tauto : Ι 0 (π / 2) ⊆ Set.univ)
      have t₀ : sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
        apply analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := π / 2)
        simp
      have t₁ : cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
        apply analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0)
        simp
      filter_upwards [t₀, t₁] with y h₁y h₂y
      simp_all only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        sin_two_mul, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, log_mul]
      ring
    _ = (∫ x in 0..(π / 2), log (sin (2 * x))) - π / 2 * log 2
        - ∫ x in 0..(π / 2), log (cos x) := by
      rw [intervalIntegral.integral_sub _ _,
        intervalIntegral.integral_sub _ intervalIntegrable_const,
        intervalIntegral.integral_const]
      · simp
      · simpa using (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left
      · apply IntervalIntegrable.sub _ intervalIntegrable_const
        simpa using (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left
      · exact intervalIntegrable_log_cos
    _ = (∫ x in 0..(π / 2), log (sin (2 * x)))
        - π / 2 * log 2 - ∫ x in 0..(π / 2), log (sin x) := by
      simp [← sin_pi_div_two_sub,
        intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)) (π / 2)]
    _ = -log 2 * π / 2 := by
      simp only [intervalIntegral.integral_comp_mul_left (f := fun x ↦ log (sin x)) two_ne_zero,
        mul_zero, (by linarith : 2 * (π / 2) = π),
        integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two, smul_eq_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel_left₀, sub_sub_cancel_left, neg_mul]
      linarith

/--
The integral of `log ∘ sin` on `0 … π` equals `-log 2 * π`.
-/
/-
**integral_log_sin_zero_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_log_sin_zero_pi : ∫ x in 0..π, log (sin x) = -log 2 * π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric.0.
integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two`：∫ (x : ℝ) 
in 0..Real.pi, Real.log (Real.sin x) = 2 * ∫ (x : ℝ) in 0..Real.pi / 2, Real.log
 (Real.sin x)
· 使用定理 `integral_log_sin_zero_pi_div_two`：integral_log_sin_zero_pi_div_two : ∫ x
 in 0..(π / 2), log (sin x) = -log 2 * π / 2
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of `log ∘ sin` on `0 … π` equals `-log 2 * π`.
-/
theorem integral_log_sin_zero_pi : ∫ x in 0..π, log (sin x) = -log 2 * π := by
  rw [integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two,
    integral_log_sin_zero_pi_div_two]
  ring
